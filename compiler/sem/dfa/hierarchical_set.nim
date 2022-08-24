
type
  NodeKeyKind = enum
    field, constant, variable
  NodeKey = object
    case kind: NodeKeyKind
    of field:
      field: PSym
    of constant:
      constant: BiggestInt
    of variable:
      variable: PSym

type
  NodeKind = enum
    Leaf # an atom (int, float etc)
    RefPtr # an indirection
    Object # only statically indexable via syms aka fields
    Array # indexable statically and dynamically within static bounds
    Infinite # indexable statically and dynamically without any bounds
    # Seq # represented by Object[len, RefPtr[Object[cap, Infinite]]]
  Node = ref object
    # we need a way to differentiate
    # between a node simply serving as a path to a
    # subnode, or being a node itself. For now we
    # just check if instructions is empty.
    # This is a set because the same location
    # could be read in different instructions
    instructions: IntSet
    case kind: NodeKind
    of Leaf:
      discard
    of RefPtr:
      target: Node
    of Object:
      allFields: HashSet[NodeKey]
      fields: Table[PSym, Node]
    of Array, Infinite:
      extent: Slice[BiggestInt]
      constants: Table[BiggestInt, Node]
      variables: Table[PSym, Node]

  HierarchicalSet = object
    root: Node

import compiler/utils/astrepr

proc typeToKind(n: PNode): NodeKind = # Should take PType instead
  const skipped = {tyAlias, tyDistinct, tyGenericInst,
    tyRef, tyPtr, tyVar, tySink, tyLent, tyOwned}
  var typ = n.typ.skipTypes(skipped)
  # HACK: sometimes typ is tyUntyped, in that case we try to get the sym typ instead
  if typ.kind == tyUntyped and n.kind == nkSym:
    typ = n.sym.typ.skipTypes(skipped)
  case typ.kind
  of tyObject, tyTuple:
    result = Object
  of tyArray:
    result = Array
  of tySequence, tyString, tyCstring, tyUncheckedArray, tyOpenArray, tyVarargs:
    result = Infinite
  of tyInt, tyInt8, tyInt16, tyInt32, tyInt64,
    tyFloat, tyFloat32, tyFloat64, tyFloat128,
    tyUInt, tyUInt8, tyUInt16, tyUInt32, tyUInt64,
    tyPointer, tyRange, tySet, tyEnum, tyBool, tyChar, tyProc:
    result = Leaf
  else:
    #debug typ
    debug n
    debug typ
    doAssert false, $typ.kind

proc hash(n: PNode): Hash = hash(cast[pointer](n))

proc hash(s: PSym): Hash = hash(cast[pointer](s))

from sequtils import toSeq

func collectImportantNodes(n: PNode): seq[PNode] =
  var n = n
  while true:
    case n.kind
    of PathKinds0 - {nkDotExpr, nkBracketExpr}:
      n = n[0]
    of PathKinds1:
      n = n[1]
    of nkDotExpr, nkBracketExpr:
      result.add n
      n = n[0]
    of nkSym:
      result.add n; break
    else:
      doAssert false, "unreachable" # is it?

var fakeTupleIndexSyms: seq[PSym]

func nodeToPath(n: PNode): seq[NodeKey] =
  let importantNodes = collectImportantNodes(n)
  for i in countdown(importantNodes.len-1, 0):
    let n = importantNodes[i]
    case n.kind
    of nkDotExpr:
      doAssert n[1].kind == nkSym
      result.add NodeKey(kind: field, field: n[1].sym)
    of nkBracketExpr:
      if typeToKind(n[0]) == Object: # Indexing a tuple
        {.cast(noSideEffect).}:
          # hack because sem doesn't transform tup[X] to tup.field_X
          if fakeTupleIndexSyms.len < n[1].intVal + 1:
            fakeTupleIndexSyms.setLen n[1].intVal + 1
          if fakeTupleIndexSyms[n[1].intVal] == nil:
            fakeTupleIndexSyms[n[1].intVal] =
              newSym(skField, nil,
                     ItemId() #[nextSymId c.idgen]#, nil, n[1].info)
          result.add NodeKey(kind: field, field: fakeTupleIndexSyms[n[1].intVal])
          continue

      result.add if n[1].kind in nkLiterals:
                   NodeKey(kind: constant, constant: n[1].intVal)
                 else:
                   NodeKey(kind: variable) # Could be a sym or a call
    of nkSym:
      # A "field" of the stack/environment
      result.add NodeKey(kind: field, field: n.sym)
    else: doAssert false, "unreachable"

func childrenLen(n: Node): int =
  case n.kind:
  of Leaf: 0
  of RefPtr:
    ord n.target != nil
  of Object:
    n.fields.len
  of Array, Infinite:
    n.constants.len + n.variables.len

func copy(n: Node): Node =
  case n.kind:
  of Leaf:
    result = Node(instructions: n.instructions, kind: Leaf)
  of RefPtr:
    result = Node(instructions: n.instructions, kind: RefPtr,
                  target: n.target)
    if result.target != nil:
      result.target = copy(result.target)
  of Object:
    result = Node(instructions: n.instructions, kind: Object,
                  fields: n.fields)
    for child in result.fields.mvalues:
      child = copy(child)
  of Array:
    result = Node(instructions: n.instructions, kind: Array,
                  constants: n.constants, variables: n.variables)
    for child in result.constants.mvalues:
      child = copy(child)
    for child in result.variables.mvalues:
      child = copy(child)
  of Infinite:
    result = Node(instructions: n.instructions, kind: Infinite,
                  constants: n.constants, variables: n.variables)
    for child in result.constants.mvalues:
      child = copy(child)
    for child in result.variables.mvalues:
      child = copy(child)

func copy(hs: HierarchicalSet): HierarchicalSet = HierarchicalSet(root: copy(hs.root))

func toIntSet(hs: HierarchicalSet): IntSet =
  func toIntSetAux(node: Node, result: var IntSet) =
    result.incl node.instructions
    case node.kind
    of Object:
      for n in node.fields.values:
        toIntSetAux(n, result)
    of Array, Infinite:
      for n in node.constants.values:
        toIntSetAux(n, result)
      for n in node.variables.values:
        toIntSetAux(n, result)
    of Leaf, RefPtr: discard

  toIntSetAux(hs.root, result)

func incl(hs: var HierarchicalSet, loc: PNode, instr: int) =
  var lastRef = hs.root
  let path = nodeToPath(loc)
  let parts = collectImportantNodes(loc)
  for i in 0..<path.len:
    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      #CONTINUE: typeToKind invocation needs to be passed the appropriate parts of the whole
      #expression to type the whole path/subtree leading to the loc leaf
      lastRef = lastRef.fields.mgetOrPut(nodeKey.field, Node(kind: typeToKind(parts[^(i+1)]))) #XXX
    of constant:
      lastRef = lastRef.constants.mgetOrPut(nodeKey.constant, Node(kind: typeToKind(parts[^(i+1)]))) #XXX
    of variable:
      lastRef = lastRef.variables.mgetOrPut(nodeKey.variable, Node(kind: typeToKind(parts[^(i+1)]))) #XXX

  lastRef.instructions.incl instr

func excl(hs: var HierarchicalSet, loc: PNode, instr: int) =
  # A single instruction int can only correspond to one location PNode
  # so we only need to find one node to exclude the instruction int from
  var lastRef = hs.root
  let path = nodeToPath(loc)
  for i in 0..<path.len:
    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey.field notin lastRef.fields:
        return
      lastRef = lastRef.fields[nodeKey.field]
    of constant:
      if nodeKey.constant notin lastRef.constants:
        return
      lastRef = lastRef.constants[nodeKey.constant]
    of variable:
      if nodeKey.variable notin lastRef.variables:
        return
      lastRef = lastRef.variables[nodeKey.variable]

  lastRef.instructions.excl instr
  # if lastRef.instructions.len == 0:
  #   #if lastRef.childrenLen == 0: XXX: Cleanup as in
  #   #  Remove it from it's parent, and for the parent of the parent if needed


func incl(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
  func incl(a: Node, b: Node) =
    a.instructions.incl b.instructions

    case b.kind:
    of Object:
      for k, child in b.fields:
        # mGetOrPut would work too
        if k in a.fields:
          incl(a.fields[k], child)
        else:
          a.fields[k] = copy(child)

    of Array, Infinite:
      for k, child in b.constants:
        if k in a.constants:
          incl(a.constants[k], child)
        else:
          a.constants[k] = copy(child)

      for k, child in b.variables:
        if k in a.variables:
          incl(a.variables[k], child)
        else:
          a.variables[k] = copy(child)

    of Leaf:
      discard # Nothing to do
    of RefPtr:
      discard #NYI

  if b.root == nil:
    debugEcho "HA"
  incl(hs.root, b.root)


func excl(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
  func excl(a: Node, b: Node) =
    a.instructions.excl b.instructions
    # if a.instructions.len == 0:
    #   #if a.childrenLen == 0: XXX: cleanup

    case a.kind:
    of Object:
      for k, child in a.fields:
        if k in b.fields:
          excl(child, b.fields[k])

    of Array, Infinite:
      for k, child in a.constants:
        if k in b.constants:
          excl(child, b.constants[k])

      for k, child in a.variables:
        if k in b.variables:
          excl(child, b.variables[k])

    of Leaf, RefPtr: discard

  excl(hs.root, b.root)


func exclDefinitelyAliased(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  result = HierarchicalSet(root: Node(kind: Object))
  var lastRef = @[hs.root] #TODO Rename, is a sequence because construction needs the kinds,
                           # could be a single lastRef and a list of kinds too
  let path = nodeToPath(loc)
  lastRef.setLen path.len
  for i in 0..<path.len-1:
    let nodeKey = path[i]
    case nodeKey.kind
    of field:
      if nodeKey.field notin lastRef[i].fields: return # Nothing to exclude
      lastRef[i+1] = lastRef[i].fields[nodeKey.field]
    of constant:
      if nodeKey.constant notin lastRef[i].constants: return # Nothing to exclude
      lastRef[i+1] = lastRef[i].constants[nodeKey.constant]
    of variable:
      return # not definitely aliased

  template popLocLeaf(children) =
    if locLeaf in lastRef[^1].children:
      var resLastRef = result.root
      for i in 0..<path.len-1:
        let nodeKey = path[i]
        case nodeKey.kind
        of field:
          let nextResLastRef = Node(kind: lastRef[i+1].kind) #XXX Or +1??
          resLastRef.fields[nodeKey.field] = nextResLastRef
          resLastRef = nextResLastRef
        of constant:
          let nextResLastRef = Node(kind: lastRef[i+1].kind) #XXX Or +1??
          resLastRef.constants[nodeKey.constant] = nextResLastRef
          resLastRef = nextResLastRef
        of variable:
          doAssert false, "unreachable"
      resLastRef.children[locLeaf] = lastRef[^1].children[locLeaf]
      lastRef[^1].children.del locLeaf

  # Remove loc, loc.X, loc[i], loc[1]
  let locLeaf = path[^1]
  case locLeaf.kind
  of field:
    let locLeaf = locLeaf.field
    popLocLeaf(fields)
  of constant:
    let locLeaf = locLeaf.constant
    popLocLeaf(constants)
  of variable: discard # not definitely aliased

type BackLastRef = object
  node: Node
  key: NodeKey
  parent: int

func exclMaybeAliased(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  let path = nodeToPath(loc)
  var lastRefs = @[@[BackLastRef(node: hs.root)]]
  lastRefs.setLen path.len
  for idx in 0..<path.len-1:
    let nodeKey = path[idx]

    template followDefinitelyAliasedPaths(children, keyContent) =
      if keyContent in lastRef.node.children:
        lastRefs[idx+1].add:
          BackLastRef(
            node: lastRef.node.children[keyContent],
            key: nodeKey,
            parent: i)

    template followMaybeAliasedPaths(children, keyConstructor) =
      for k {.inject.}, child in lastRef.node.children:
        lastRefs[idx+1].add:
          BackLastRef(
            node: child,
            key: keyConstructor,
            parent: i)

    case nodeKey.kind
    of field:
      for i, lastRef in lastRefs[idx]:
        followDefinitelyAliasedPaths(fields, nodeKey.field)
    of constant:
      for i, lastRef in lastRefs[idx]:
        followMaybeAliasedPaths(variables, NodeKey(kind: variable, variable: k))
        followDefinitelyAliasedPaths(constants, nodeKey.constant)
    of variable:
      for i, lastRef in lastRefs[idx]:
        followMaybeAliasedPaths(variables, NodeKey(kind: variable, variable: k))
        followMaybeAliasedPaths(constants, NodeKey(kind: constant, constant: k))

    if lastRefs[idx+1].len == 0:
      result = HierarchicalSet(root: Node(kind: Object))
      return # Nothing to exclude

  # Remove loc, loc.X, loc[i], loc[1]
  var lastNodes: seq[BackLastRef]
  let locLeaf = path[^1]
  template popDefinitelyAliasedLeaf(children, locLeafContent) =
    if locLeafContent in lastRef.node.children:
      lastNodes.add BackLastRef(
        node: lastRef.node.children[locLeafContent],
        key: locLeaf, parent: lastRef.parent)
      lastRef.node.children.del locLeafContent

  template popMaybeAliasedLeaf(children, keyConstructor) =
    for k {.inject.}, child in lastRef.node.children:
      lastNodes.add BackLastRef(
        node: child,
        key: keyConstructor, parent: lastRef.parent)
    lastRef.node.children.clear


  case locLeaf.kind
  of field:
    for lastRef in lastRefs[^1]:
      popDefinitelyAliasedLeaf(fields, locLeaf.field)
  of constant:
    for lastRef in lastRefs[^1]:
      popDefinitelyAliasedLeaf(constants, locLeaf.constant)
      popMaybeAliasedLeaf(variables, NodeKey(kind: variable, variable: k))
  of variable:
    for lastRef in lastRefs[^1]:
      popMaybeAliasedLeaf(constants, NodeKey(kind: constant, constant: k))
      popMaybeAliasedLeaf(variables, NodeKey(kind: variable, variable: k))

  template putput(node, key, child) =
    case key.kind
    of field:
      node.fields[key.field] = child
    of constant:
      node.constants[key.constant] = child
    of variable:
      node.variables[key.variable] = child


  # Construct result
  if lastNodes.len > 0:
    var parents: IntSet
    for i in 0..<lastNodes.len: parents.incl i
    lastRefs.add lastNodes

    for idx in countdown(lastRefs.len-1, 1):
      var newParents: IntSet
      for k in parents:
        let lr = lastRefs[idx][k]
        if lr.parent notin newParents:
          lastRefs[idx-1][lr.parent].node = Node(kind: lastRefs[idx-1][lr.parent].node.kind) #XXX
        newParents.incl lr.parent
        lastRefs[idx-1][lr.parent].node.putput(lr.key, lr.node)
      parents = newParents

    assert parents.len == 1
    result = HierarchicalSet(root: lastRefs[0][0].node)

  else:
    result = HierarchicalSet(root: Node(kind: Object))

func exclMaybeAliasing(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  result = HierarchicalSet(root: Node(kind: Object))
  var resLastRefs = @[result.root]

  var lastRefs = @[hs.root]
  let path = nodeToPath(loc)
  for j in 0..<path.len:
    let nodeKey = path[j]

    template followDefinitelyAliasedPaths(children, nodeKeyContent) =
      var i = 0
      while i < lastRefs.len:
        if nodeKeyContent notin lastRefs[i].children:
          lastRefs.del i
          resLastRefs.del i # XXX: Cleanup result???
        else:
          let nextLastRef = lastRefs[i].children[nodeKeyContent]
          if nextLastRef.instructions.len > 0:
            if nextLastRef.childrenLen == 0:
              lastRefs[i].children.del nodeKeyContent # Remove path leading to loc
              lastRefs.del i

              resLastRefs[i].children[nodeKeyContent] = nextLastRef
              resLastRefs.del i
            else:
              lastRefs[i] = nextLastRef

              let resNextLastRef = Node(kind: nextLastRef.kind,
                                        instructions: nextLastRef.instructions) #XXX
              resLastRefs[i].children[nodeKeyContent] = resNextLastRef
              resLastRefs[i] = resNextLastRef

              nextLastRef.instructions.clear # Remove node on path leading to loc

              inc i
          else:
            if nextLastRef.childrenLen == 0: # Unreachable if hs is cleaned up
              lastRefs[i].children.del nodeKeyContent
              lastRefs.del i

              resLastRefs.del i
            else:
              lastRefs[i] = nextLastRef

              let resNextLastRef = Node(kind: nextLastRef.kind) #XXX
              resLastRefs[i].children[nodeKeyContent] = resNextLastRef
              resLastRefs[i] = resNextLastRef

              inc i


    template followMaybeAliasedPaths(children) =
      # Delete all ...[var/const]
      let children = toSeq lastRefs[i].children.pairs
      for (key, nextLastRef) in children:
        if nextLastRef.instructions.len > 0:
          if nextLastRef.childrenLen == 0: # If ...[var/const] has no children
            lastRefs[i].children.del key # GC ...[var/const] from the set

            resLastRefs[i].children[key] = nextLastRef
          else:
            nextLastRefs.add nextLastRef # Recurse into children of ...[var/const]

            let resNextLastRef = Node(kind: nextLastRef.kind,
                                      instructions: nextLastRef.instructions) #XXX
            resLastRefs[i].children[key] = resNextLastRef
            nextResLastRefs.add resNextLastRef

            nextLastRef.instructions.clear # Remove ...[var/const]
        else:
          if nextLastRef.childrenLen == 0: # Unreachable if hs is cleaned up
            lastRefs[i].children.del key
          else:
            nextLastRefs.add nextLastRef # Recurse into children of ...[var/const]

            let resNextLastRef = Node(kind: nextLastRef.kind) #XXX
            resLastRefs[i].children[key] = resNextLastRef
            nextResLastRefs.add resNextLastRef

    case nodeKey.kind
    of field:
      followDefinitelyAliasedPaths(fields, nodeKey.field)
    of constant:
      var nextLastRefs: seq[Node]
      var nextResLastRefs: seq[Node]

      for i in 0..<lastRefs.len:
        followMaybeAliasedPaths(variables)

      followDefinitelyAliasedPaths(constants, nodeKey.constant)

      lastRefs.add nextLastRefs
      resLastRefs.add nextResLastRefs

    of variable:
      var nextLastRefs: seq[Node]
      var nextResLastRefs: seq[Node]

      for i in 0..<lastRefs.len:
        followMaybeAliasedPaths(constants)
        followMaybeAliasedPaths(variables)

      lastRefs = nextLastRefs
      resLastRefs = nextResLastRefs


# Remove loc from the set means to empty it's instruction set
# It may still serve as a path to other locs
# GC loc from the set means to actually remove the node from it,
# which is possible if the node has no instructions and no children.

#def:
#  potentialLastReads.excl:
#    lastReads.incl:
#      all definitely aliased by the def loc (exclDefinitelyAliased)
#    notLastReads.incl:
#      all that would maybe alias the def loc (exclmaybeAliasing)
#use:
#  potentialLastReads.excl:
#    notLastReads.incl:
#      all maybe aliased by the use loc (exclMaybeAliased)
#      all that would maybe alias the use loc (exclmaybeAliasing)
#  potentialLastReads.incl:
#    the use loc
#merge:
#  lastReads = a.lastReads + b.lastReads
#  potentialLastReads = (a.potentialLastReads + b.potentialLastReads) - (a.notLastReads + b.notLastReads)
#  notLastReads = a.notLastReads + b.notLastReads
#  alreadySeen = a.alreadySeen + b.alreadySeen
#finalize:
#  lastReads = (states[^1].lastReads + states[^1].potentialLastReads) - states[^1].notLastReads
#  
#  var lastReadTable: Table[PNode, seq[int]]
#  for position, node in cfg:
#    if node.kind == use:
#      lastReadTable.mgetOrPut(node.n, @[]).add position
#  for node, positions in lastReadTable:
#    block checkIfAllPosLastRead:
#      for p in positions:
#        if p notin lastReads: break checkIfAllPosLastRead
#      node.flags.incl nfLastRead

template incl(a, b) = cfg.incl(a, b)
template excl(a, b) = cfg.excl(a, b)

proc reprNodeKey(k: NodeKey): string =
  case k.kind
  of field:
    $k.field
  of constant:
    $k.constant
  of variable:
    "var:" & $k.variable

proc reprNodeKeys(keys: seq[NodeKey]): string =
  for i in 0..<keys.len:
    let k = keys[i]
    result.add "|" & $reprNodeKey(k)

proc reprHS(hs: HierarchicalSet): string =
  proc debugNode(key: seq[NodeKey], n: Node): string =
    result.add repeat(' ', key.len)
    if key.len == 0:
      result.add "root"
    else:
      result.add reprNodeKey key[^1]
    result.add $n.kind & " " & $n.instructions
    result.add "\n"

    case n.kind:
    of Object:
      for k, c in n.fields:
        result.add debugNode(key & NodeKey(kind: field, field: k), c)

    of Array, Infinite:
      for k, c in n.constants:
        result.add debugNode(key & NodeKey(kind: constant, constant: k), c)

      for k, c in n.variables:
        result.add debugNode(key & NodeKey(kind: variable, variable: k), c)

    of Leaf:
      discard
    of RefPtr:
      result.add debugNode(key & NodeKey(), n.target)

  result = debugNode(@[], hs.root)

proc debugA(hs: HierarchicalSet): HierarchicalSet =
  echo reprHS hs
  hs
