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
    fields: Table[NodeKey, TaintNode]
    constants: Table[NodeKey, TaintNode]
    variables: TaintNode
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
      if nodeKey in writeLastRef.fields:
        writeLastRef = writeLastRef.fields[nodeKey]
      else: break
    of constant:
      if nodeKey in writeLastRef.constants:
        writeLastRef = writeLastRef.constants[nodeKey]
      else: break
    of variable:
      if writeLastRef.variables != nil:
        writeLastRef = writeLastRef.variables
      else: break

  var readLastRef = hs.readRoot
  for i in 0..<path.len:
    if readLastRef != nil and readLastRef.taint:
      return # A parent of our read was already completely read.

    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey notin readLastRef.fields:
        readLastRef.fields[nodeKey] = TaintNode()
      readLastRef = readLastRef.fields[nodeKey]
    of constant:
      if nodeKey notin readLastRef.constants:
        readLastRef.constants[nodeKey] = TaintNode()
      readLastRef = readLastRef.constants[nodeKey]
    of variable:
      if readLastRef.variables == nil:
        readLastRef.variables = TaintNode()
      readLastRef = readLastRef.variables

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
      if nodeKey in readLastRef.fields:
        readLastRef = readLastRef.fields[nodeKey]
      else: readLastRef = nil; break
    of constant:
      if nodeKey in readLastRef.constants:
        readLastRef = readLastRef.constants[nodeKey]
      else: readLastRef = nil; break
    of variable:
      if readLastRef.variables != nil:
        readLastRef = readLastRef.variables
      else: readLastRef = nil; break

  var writeLastRef = hs.writeRoot
  for i in 0..<path.len:
    if writeLastRef != nil and writeLastRef.taint:
      return # A parent of our write was already completely written.

    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey notin writeLastRef.fields:
        writeLastRef.fields[nodeKey] = TaintNode()
      writeLastRef = writeLastRef.fields[nodeKey]
    of constant:
      if nodeKey notin writeLastRef.constants:
        writeLastRef.constants[nodeKey] = TaintNode()
      writeLastRef = writeLastRef.constants[nodeKey]
    of variable:
      if writeLastRef.variables == nil:
        writeLastRef.variables = TaintNode()
      writeLastRef = writeLastRef.variables

  if not(readLastRef != nil and readLastRef.taint): # read before write: nothing
    writeLastRef.taint = true

func len(n: TaintNode): int =
  n.fields.len + n.constants.len + ord(n.variables != nil)

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

      var allSyms, allConsts: HashSet[NodeKey]
      if readCursorA != nil:
        allSyms.incl readCursorA.fields.keys.toSeq.toHashSet
        allConsts.incl readCursorA.constants.keys.toSeq.toHashSet
      if writeCursorA != nil:
        allSyms.incl writeCursorA.fields.keys.toSeq.toHashSet
        allConsts.incl writeCursorA.constants.keys.toSeq.toHashSet
      if readCursorB != nil:
        allSyms.incl readCursorB.fields.keys.toSeq.toHashSet
        allConsts.incl readCursorB.constants.keys.toSeq.toHashSet
      if writeCursorB != nil:
        allSyms.incl writeCursorB.fields.keys.toSeq.toHashSet
        allConsts.incl writeCursorB.constants.keys.toSeq.toHashSet

      if readCursorB != nil: result.read = readCursorB
      if readCursorA != nil: result.read = readCursorA
      if writeCursorB != nil: result.write = writeCursorB
      if writeCursorA != nil: result.write = writeCursorA

      for k in allSyms:
        let (read, write) = mergeTaintTreesAux(
          if readCursorA != nil and readCursorA.fields.hasKey(k):
            readCursorA.fields[k]
          else: nil,
          if writeCursorA != nil and writeCursorA.fields.hasKey(k):
            writeCursorA.fields[k]
          else: nil,
          if readCursorB != nil and readCursorB.fields.hasKey(k):
            readCursorB.fields[k]
          else: nil,
          if writeCursorB != nil and writeCursorB.fields.hasKey(k):
            writeCursorB.fields[k]
          else: nil)
        if read != nil:
          result.read.fields[k] = read
        if write != nil:
          result.write.fields[k] = write

      for k in allConsts:
        let (read, write) = mergeTaintTreesAux(
          if readCursorA != nil and readCursorA.constants.hasKey(k):
            readCursorA.constants[k]
          else: nil,
          if writeCursorA != nil and writeCursorA.constants.hasKey(k):
            writeCursorA.constants[k]
          else: nil,
          if readCursorB != nil and readCursorB.constants.hasKey(k):
            readCursorB.constants[k]
          else: nil,
          if writeCursorB != nil and writeCursorB.constants.hasKey(k):
            writeCursorB.constants[k]
          else: nil)
        if read != nil:
          result.read.constants[k] = read
        if write != nil:
          result.write.constants[k] = write

      block:
        let (read, write) = mergeTaintTreesAux(
          if readCursorA != nil: readCursorA.variables else: nil,
          if writeCursorA != nil: writeCursorA.variables else: nil,
          if readCursorB != nil: readCursorB.variables else: nil,
          if writeCursorB != nil: writeCursorB.variables else: nil)
        if read != nil:
          result.read.variables = read
        if write != nil:
          result.write.variables = write

      # reads merge quite simply:
      #if   readCursorA != nil and readCursorB == nil: #handled before the for loops
      #  result.read = readCursorB
      #elif readCursorA == nil and readCursorB != nil: #handled before the for loops
      #  result.read = readCursorA
      #elif readCursorA == nil and readCursorB == nil: #implicitly nil
      #  result.read = nil
      if readCursorA != nil and readCursorB != nil:
        #result.read = readCursorA #handled before the for loops
        result.read.taint = readCursorA.taint or readCursorB.taint

      # writes are a bit more complex:
      if writeCursorA != nil and writeCursorB != nil:
        #result.read = readCursorA #handled before the for loops
        result.write.taint = writeCursorA.taint and writeCursorB.taint
      elif writeCursorA != nil and writeCursorB == nil:
        result.write.taint = false # deactivated write, since it doesn't occur in B
      elif writeCursorA == nil and writeCursorB != nil:
        result.write.taint = false # deactivated write, since it doesn't occur in A

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
  if result.variables != nil:
    result.variables = copy(result.variables)

func copy(t: TaintTree): TaintTree = TaintTree(readRoot: copy(t.readRoot), writeRoot: copy(t.writeRoot))

proc `$`(t: TaintTree): string =
  proc reprNodeKeys(keys: seq[NodeKey]): string =
    let k = keys[^1]
    case k.kind
    of field:
      $k.field
    of constant:
      $k.constant
    of variable:
      "var"

  proc debugNode(key: seq[NodeKey], r, w: TaintNode): string =
    if r != nil or w != nil:
      result.add repeat(' ', key.len)
      if key.len == 0:
        result.add "root"
      else:
        result.add reprNodeKeys key
      if r != nil:
        result.add " r(" & $r.taint & ")"
      if w != nil:
        result.add " w(" & $w.taint & ")"
      result.add "\n"

      var allSyms, allConsts: HashSet[NodeKey]
      if r != nil:
        allSyms.incl r.fields.keys.toSeq.toHashSet
        allConsts.incl r.constants.keys.toSeq.toHashSet
      if w != nil:
        allSyms.incl w.fields.keys.toSeq.toHashSet
        allConsts.incl w.constants.keys.toSeq.toHashSet

      for k in allSyms:
        result.add debugNode(key & k,
          if r != nil and r.fields.hasKey(k): r.fields[k] else: nil,
          if w != nil and w.fields.hasKey(k): w.fields[k] else: nil)

      for k in allConsts:
        result.add debugNode(key & k,
          if r != nil and r.constants.hasKey(k): r.constants[k] else: nil,
          if w != nil and w.constants.hasKey(k): w.constants[k] else: nil)

      if r != nil or w != nil:
        result.add debugNode(key & NodeKey(kind: variable),
          if r != nil: r.variables else: nil,
          if w != nil: w.variables else: nil)

  result = debugNode(@[], t.readRoot, t.writeRoot)

