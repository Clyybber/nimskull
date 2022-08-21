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
  TaintNode = ref object
    taint: bool # read: false: implicitly read, true: explicitly read
                # write: false: not written before read, true: written before read
    symChildren: Table[NodeKey, TaintNode]
    constantChildren: Table[NodeKey, TaintNode]
    variableChildren: TaintNode
      # Only one node for now, change back to Table[NodeKey, TaintNode]
      # if smarter variable analysis is implemented
      # Smarter variable analysis could simply assign
      # an integer to each snippet of code in which a variable
      # is an unchanged value, and then treat them as (variable+snippet_id)
      # tuples for equality

  TaintTree = object
    # Example taint tree:
    #          root
    #      s            t
    #r(s.x) w(s.y)    r(t[i])
    # Child nodes always taint their parents
    # as read implicitly (without their taintkind actually reflecting it)
    # A taint tree also only needs to support insertion, no removal.
    writeRoot: TaintNode
    readRoot: TaintNode

func taintRead(hs: var TaintTree, loc: PNode) =
  let path = nodeToPath(loc)

  # First check if dominated by write
  var writeLastRef = hs.writeRoot
  for i in 0..<path.len:
    if writeLastRef != nil and writeLastRef.taint:
      return # A parent of our read was already completely written.

    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      if nodeKey in writeLastRef.symChildren:
        writeLastRef = writeLastRef.symChildren[nodeKey]
      else: break
    of constant:
      if nodeKey in writeLastRef.constantChildren:
        writeLastRef = writeLastRef.constantChildren[nodeKey]
      else: break
    of variable:
      if writeLastRef.variableChildren != nil:
        writeLastRef = writeLastRef.variableChildren
      else: break

  var readLastRef = hs.readRoot
  for i in 0..<path.len:
    if readLastRef != nil and readLastRef.taint:
      return # A parent of our read was already completely read.

    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      if nodeKey notin readLastRef.symChildren:
        readLastRef.symChildren[nodeKey] = TaintNode()
      readLastRef = readLastRef.symChildren[nodeKey]
    of constant:
      if nodeKey notin readLastRef.constantChildren:
        readLastRef.constantChildren[nodeKey] = TaintNode()
      readLastRef = readLastRef.constantChildren[nodeKey]
    of variable:
      if readLastRef.variableChildren == nil:
        readLastRef.variableChildren = TaintNode()
      readLastRef = readLastRef.variableChildren

  readLastRef.taint = true
  # The following turns (read: true, write: true) into (read: true, write: false)
  # but it's probably unneccessary since we can just treat them as the latter when
  # applying the cache. Although OTOH this might allow some cleanup if write.len == 0
  # if writeLastRef != nil and writeLastRef.taint: #instead of checking taint check len,
  #                                                #because then we get deactivated writes too
  #   writeLastRef.taint = false

func taintWrite(hs: var TaintTree, loc: PNode) =
  let path = nodeToPath(loc)

  # First check if dominated by read
  var readLastRef = hs.readRoot
  for i in 0..<path.len:
    if readLastRef != nil and readLastRef.taint:
      return # A parent of our read was already completely read.

    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      if nodeKey in readLastRef.symChildren:
        readLastRef = readLastRef.symChildren[nodeKey]
      else: readLastRef = nil; break
    of constant:
      if nodeKey in readLastRef.constantChildren:
        readLastRef = readLastRef.constantChildren[nodeKey]
      else: readLastRef = nil; break
    of variable:
      if readLastRef.variableChildren != nil:
        readLastRef = readLastRef.variableChildren
      else: readLastRef = nil; break

  var writeLastRef = hs.writeRoot
  for i in 0..<path.len:
    if writeLastRef != nil and writeLastRef.taint:
      return # A parent of our write was already completely written.

    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      if nodeKey notin writeLastRef.symChildren:
        writeLastRef.symChildren[nodeKey] = TaintNode()
      writeLastRef = writeLastRef.symChildren[nodeKey]
    of constant:
      if nodeKey notin writeLastRef.constantChildren:
        writeLastRef.constantChildren[nodeKey] = TaintNode()
      writeLastRef = writeLastRef.constantChildren[nodeKey]
    of variable:
      if writeLastRef.variableChildren == nil:
        writeLastRef.variableChildren = TaintNode()
      writeLastRef = writeLastRef.variableChildren

  if not(readLastRef != nil and readLastRef.taint): # read before write: nothing
    writeLastRef.taint = true

func len(n: TaintNode): int =
  n.symChildren.len + n.constantChildren.len + ord(n.variableChildren != nil)

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
        allSyms.incl readCursorA.symChildren.keys.toSeq.toHashSet
        allConsts.incl readCursorA.constantChildren.keys.toSeq.toHashSet
      if writeCursorA != nil:
        allSyms.incl writeCursorA.symChildren.keys.toSeq.toHashSet
        allConsts.incl writeCursorA.constantChildren.keys.toSeq.toHashSet
      if readCursorB != nil:
        allSyms.incl readCursorB.symChildren.keys.toSeq.toHashSet
        allConsts.incl readCursorB.constantChildren.keys.toSeq.toHashSet
      if writeCursorB != nil:
        allSyms.incl writeCursorB.symChildren.keys.toSeq.toHashSet
        allConsts.incl writeCursorB.constantChildren.keys.toSeq.toHashSet

      if readCursorB != nil: result.read = readCursorB
      if readCursorA != nil: result.read = readCursorA
      if writeCursorB != nil: result.write = writeCursorB
      if writeCursorA != nil: result.write = writeCursorA

      for k in allSyms:
        let (read, write) = mergeTaintTreesAux(
          if readCursorA != nil and readCursorA.symChildren.hasKey(k):
            readCursorA.symChildren[k]
          else: nil,
          if writeCursorA != nil and writeCursorA.symChildren.hasKey(k):
            writeCursorA.symChildren[k]
          else: nil,
          if readCursorB != nil and readCursorB.symChildren.hasKey(k):
            readCursorB.symChildren[k]
          else: nil,
          if writeCursorB != nil and writeCursorB.symChildren.hasKey(k):
            writeCursorB.symChildren[k]
          else: nil)
        if read != nil:
          result.read.symChildren[k] = read
        if write != nil:
          result.write.symChildren[k] = write

      for k in allConsts:
        let (read, write) = mergeTaintTreesAux(
          if readCursorA != nil and readCursorA.constantChildren.hasKey(k):
            readCursorA.constantChildren[k]
          else: nil,
          if writeCursorA != nil and writeCursorA.constantChildren.hasKey(k):
            writeCursorA.constantChildren[k]
          else: nil,
          if readCursorB != nil and readCursorB.constantChildren.hasKey(k):
            readCursorB.constantChildren[k]
          else: nil,
          if writeCursorB != nil and writeCursorB.constantChildren.hasKey(k):
            writeCursorB.constantChildren[k]
          else: nil)
        if read != nil:
          result.read.constantChildren[k] = read
        if write != nil:
          result.write.constantChildren[k] = write

      block:
        let (read, write) = mergeTaintTreesAux(
          if readCursorA != nil: readCursorA.variableChildren else: nil,
          if writeCursorA != nil: writeCursorA.variableChildren else: nil,
          if readCursorB != nil: readCursorB.variableChildren else: nil,
          if writeCursorB != nil: writeCursorB.variableChildren else: nil)
        if read != nil:
          result.read.variableChildren = read
        if write != nil:
          result.write.variableChildren = write

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
    symChildren: n.symChildren,
    constantChildren: n.constantChildren,
    variableChildren: n.variableChildren
  )
  for child in result.symChildren.mvalues:
    child = copy(child)
  for child in result.constantChildren.mvalues:
    child = copy(child)
  if result.variableChildren != nil:
    result.variableChildren = copy(result.variableChildren)

func copy(t: TaintTree): TaintTree = TaintTree(readRoot: copy(t.readRoot), writeRoot: copy(t.writeRoot))

proc `$`(t: TaintTree): string =
  proc reprNodeKeys(keys: seq[NodeKey]): string =
    let k = keys[^1]
    case k.kind
    of sym:
      $k.sym
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
        allSyms.incl r.symChildren.keys.toSeq.toHashSet
        allConsts.incl r.constantChildren.keys.toSeq.toHashSet
      if w != nil:
        allSyms.incl w.symChildren.keys.toSeq.toHashSet
        allConsts.incl w.constantChildren.keys.toSeq.toHashSet

      for k in allSyms:
        result.add debugNode(key & k,
          if r != nil and r.symChildren.hasKey(k): r.symChildren[k] else: nil,
          if w != nil and w.symChildren.hasKey(k): w.symChildren[k] else: nil)

      for k in allConsts:
        result.add debugNode(key & k,
          if r != nil and r.constantChildren.hasKey(k): r.constantChildren[k] else: nil,
          if w != nil and w.constantChildren.hasKey(k): w.constantChildren[k] else: nil)

      if r != nil or w != nil:
        result.add debugNode(key & NodeKey(kind: variable),
          if r != nil: r.variableChildren else: nil,
          if w != nil: w.variableChildren else: nil)

  result = debugNode(@[], t.readRoot, t.writeRoot)

