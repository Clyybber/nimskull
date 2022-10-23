type
  TaintKind = enum
    implicitlyRead #(readTaint: false, writeTaint: false)
    read # not last read #(readTaint: true, writeTaint: false)
      # maybeAliasing
      # | \ | / |
      # \__r(x)_/
      # / / | \ \
      # maybeAliased
    write # could be last read #(readTaint: false, writeTaint: true)
      # maybeAliasing
      # | \ | / |
      # \__r(x)_/
      #   / | \
      # defAliased
    writeAndRead #(readTaint: true, writeTaint: true)
      # this was first written and then read from
    deactivatedWrite #(readTaint: false, writeTaint: false)
      # maybeAliasing
      # | \ | / |
      # \__d(x)_/
      # This occurs when joining paths in which one wrote x but the other one didn't
      # This is the same as implicitlyRead and can exist as a leaf too.
  TaintNode = ref object
    taint: bool
      # read: false: implicitly read, true: explicitly read
      # write: false: not written before read, true: written before read
    fields: Table[PSym, TaintNode]
    constants: Table[BiggestInt, TaintNode]
    variables: Table[PSym, TaintNode]
      # Only one node for now, change back to Table[NodeKey, TaintNode]
      # if smarter variable analysis is implemented
      # Smarter variable analysis could simply assign
      # an integer to each snippet of code in which a variable
      # is an unchanged value, and then treat them as (variable+snippet_id)
      # tuples for equality

  TaintTree = object
    # Example taint tree:
    #            root
    #       s            t
    # r(s.x) w(s.y)   r(t[i])
    # Child nodes always taint their parents
    # as read implicitly (without their taintkind actually reflecting it)
    # A taint tree also only needs to support insertion, no removal.
    writeRoot: TaintNode
    readRoot: TaintNode

func taintRead(hs: var TaintTree, loc: PNode) =
  let path = nodesToPath(collectImportantNodes(loc))

  # First check if dominated by write
  var writeLastRef = hs.writeRoot
  for i in 0..<path.len:
    if writeLastRef != nil and writeLastRef.taint:
      return # A parent of our read was already completely written.

    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey.field in writeLastRef.fields:
        writeLastRef = writeLastRef.fields[nodeKey.field]
      else: break
    of constant:
      if nodeKey.constant in writeLastRef.constants:
        writeLastRef = writeLastRef.constants[nodeKey.constant]
      else: break
    of variable:
      if nodeKey.variable in writeLastRef.variables:
        writeLastRef = writeLastRef.variables[nodeKey.variable]
      else: break

  var readLastRef = hs.readRoot
  for i in 0..<path.len:
    if readLastRef != nil and readLastRef.taint:
      return # A parent of our read was already completely read.

    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey.field notin readLastRef.fields:
        readLastRef.fields[nodeKey.field] = TaintNode()
      readLastRef = readLastRef.fields[nodeKey.field]
    of constant:
      if nodeKey.constant notin readLastRef.constants:
        readLastRef.constants[nodeKey.constant] = TaintNode()
      readLastRef = readLastRef.constants[nodeKey.constant]
    of variable:
      if nodeKey.variable notin readLastRef.variables:
        readLastRef.variables[nodeKey.variable] = TaintNode()
      readLastRef = readLastRef.variables[nodeKey.variable]

  readLastRef.taint = true
  # The following turns (read: true, write: true) into (read: true, write: false)
  # but it's probably unneccessary since we can just treat them as the latter when
  # applying the cache. Although OTOH this might allow some cleanup if write.len == 0
  # if writeLastRef != nil and writeLastRef.taint: #instead of checking taint check len,
  #                                                #because then we get deactivated writes too
  #   writeLastRef.taint = false

func taintWrite(hs: var TaintTree, loc: PNode) =
  let path = nodesToPath(collectImportantNodes(loc))

  # First check if dominated by read
  var readLastRef = hs.readRoot
  for i in 0..<path.len:
    if readLastRef != nil and readLastRef.taint:
      return # A parent of our read was already completely read.

    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey.field in readLastRef.fields:
        readLastRef = readLastRef.fields[nodeKey.field]
      else: readLastRef = nil; break
    of constant:
      if nodeKey.constant in readLastRef.constants:
        readLastRef = readLastRef.constants[nodeKey.constant]
      else: readLastRef = nil; break
    of variable:
      if nodeKey.variable in readLastRef.variables:
        readLastRef = readLastRef.variables[nodeKey.variable]
      else: readLastRef = nil; break

  var writeLastRef = hs.writeRoot
  for i in 0..<path.len:
    if writeLastRef != nil and writeLastRef.taint:
      return # A parent of our write was already completely written.

    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey.field notin writeLastRef.fields:
        writeLastRef.fields[nodeKey.field] = TaintNode()
      writeLastRef = writeLastRef.fields[nodeKey.field]
    of constant:
      if nodeKey.constant notin writeLastRef.constants:
        writeLastRef.constants[nodeKey.constant] = TaintNode()
      writeLastRef = writeLastRef.constants[nodeKey.constant]
    of variable:
      if nodeKey.variable notin writeLastRef.variables:
        writeLastRef.variables[nodeKey.variable] = TaintNode()
      writeLastRef = writeLastRef.variables[nodeKey.variable]

  if not(readLastRef != nil and readLastRef.taint): # read before write: nothing
    writeLastRef.taint = true

func len(n: TaintNode): int =
  n.fields.len + n.constants.len + n.variables.len

proc mergeTaintTrees(cfg: ControlFlowGraph, a: var TaintTree, b: TaintTree) =
  # merge
  #   {w(s[1])} with {}
  # must still exclMaybeAliasing(s[1]) but
  # not exclDefinitelyAliased(s[1]) nor exclMaybeAliased(s[1])
  # So this is like a "deactivated" write. We use a non tainted leaf node for this.
  # If it's not a leaf that's fine because a child of s[1] handles excludes the
  # maybe aliasing of s[1] anyways. It's arbitrary wether we put this non
  # tainted leaf node into the read taint tree or the write taint tree.

  proc mergeTaintTreesAux(readCursorA, writeCursorA,
                          readCursorB, writeCursorB: TaintNode):
                        tuple[read, write: TaintNode] =
    if readCursorA != nil or writeCursorA != nil or
       readCursorB != nil or writeCursorB != nil:

      var
        allFields: HashSet[PSym]
        allConsts: HashSet[BiggestInt]
        allVars: HashSet[PSym]

      template collectChilds(n, res) =
        if n != nil:
          allFields.incl n.fields.keys.toSeq.toHashSet
          allConsts.incl n.constants.keys.toSeq.toHashSet
          allVars.incl n.variables.keys.toSeq.toHashSet
          res = n

      collectChilds(readCursorB, result.read)
      collectChilds(writeCursorB, result.write)
      collectChilds(readCursorA, result.read)
      collectChilds(writeCursorA, result.write)

      template recurse(allChilds, childs) =
        for k in allChilds:
          let (read, write) = mergeTaintTreesAux(
            if readCursorA != nil and k in readCursorA.childs:
              readCursorA.childs[k]
            else: nil,
            if writeCursorA != nil and k in writeCursorA.childs:
              writeCursorA.childs[k]
            else: nil,
            if readCursorB != nil and k in readCursorB.childs:
              readCursorB.childs[k]
            else: nil,
            if writeCursorB != nil and k in writeCursorB.childs:
              writeCursorB.childs[k]
            else: nil)
          if read != nil:
            result.read.childs[k] = read
          if write != nil:
            result.write.childs[k] = write

      recurse(allFields, fields)
      recurse(allConsts, constants)
      recurse(allVars, variables)

      # reads merge quite simply:
      if readCursorA != nil and readCursorB != nil:
        #result.read = readCursorA #handled before the for loops
        result.read.taint = readCursorA.taint or readCursorB.taint
      #elif readCursorA != nil: #handled before the for loops
      #  result.read = readCursorA
      #elif readCursorB != nil: #handled before the for loops
      #  result.read = readCursorB
      #else: #implicitly nil
      #  result.read = nil

      # writes are a bit more complex:
      if writeCursorA != nil and writeCursorB != nil:
        #result.write = writeCursorA #handled before the for loops
        result.write.taint = writeCursorA.taint and writeCursorB.taint
      elif writeCursorA != nil or writeCursorB != nil:
        result.write.taint = false # deactivated write, since it only occurs in A xor B

  var newA = mergeTaintTreesAux(a.readRoot, a.writeRoot, b.readRoot, b.writeRoot)
  a = TaintTree(readRoot: newA.read, writeRoot: newA.write)

func copy(n: TaintNode): TaintNode =
  result = TaintNode(
    taint: n.taint,
    fields: n.fields,
    constants: n.constants,
    variables: n.variables
  )
  for child in result.fields.mvalues:
    child = copy(child)
  for child in result.constants.mvalues:
    child = copy(child)
  for child in result.variables.mvalues:
    child = copy(child)

func copy(t: TaintTree): TaintTree = TaintTree(readRoot: copy(t.readRoot), writeRoot: copy(t.writeRoot))

proc `$`(t: TaintTree): string =
  proc debugNode(lvl: int, key: NodeKey, r, w: TaintNode): string =
    if r != nil or w != nil:
      result.add repeat(' ', lvl)
      if lvl == 0:
        result.add "root"
      else:
        result.add reprNodeKey key
      if r != nil:
        result.add " r(" & $r.taint & ")"
      if w != nil:
        result.add " w(" & $w.taint & ")"
      result.add "\n"

      var
        allFields: HashSet[PSym]
        allConsts: HashSet[BiggestInt]
        allVars: HashSet[PSym]
      if r != nil:
        allFields.incl r.fields.keys.toSeq.toHashSet
        allConsts.incl r.constants.keys.toSeq.toHashSet
        allVars.incl r.variables.keys.toSeq.toHashSet
      if w != nil:
        allFields.incl w.fields.keys.toSeq.toHashSet
        allConsts.incl w.constants.keys.toSeq.toHashSet
        allVars.incl w.variables.keys.toSeq.toHashSet

      for k in allFields:
        result.add debugNode(lvl+1, NodeKey(kind: field, field: k),
          if r != nil and k in r.fields: r.fields[k] else: nil,
          if w != nil and k in w.fields: w.fields[k] else: nil)

      for k in allConsts:
        result.add debugNode(lvl+1, NodeKey(kind: constant, constant: k),
          if r != nil and k in r.constants: r.constants[k] else: nil,
          if w != nil and k in w.constants: w.constants[k] else: nil)

      for k in allVars:
        result.add debugNode(lvl+1, NodeKey(kind: variable, variable: k),
          if r != nil and k in r.variables: r.variables[k] else: nil,
          if w != nil and k in w.variables: w.variables[k] else: nil)

  result = debugNode(0, NodeKey(kind: field), t.readRoot, t.writeRoot)

