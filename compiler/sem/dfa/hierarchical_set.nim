import
  std/[
    intsets,
    strutils,
    tables,
    sets
  ],
  compiler/ast/[
    ast
  ],
  compiler/sem/dfa/[
    cfg,
    setnode
  ]

from sequtils import toSeq

type
  SetNode* = Node[IntSet]

  HierarchicalSet* = object
    root*: SetNode

template instructions(n: SetNode): IntSet = n.data

proc typeToKind(typ: PType): NodeKind =
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
    doAssert false, $typ.kind

proc nodeToNode(n: PNode): SetNode =
  let typ = typeOfNode(n)
  result = SetNode(kind: typeToKind(typ))

func childrenLen(n: SetNode): int =
  case n.kind:
  of Leaf: 0
  of Object:
    n.fields.len
  of Array, Infinite:
    n.constants.len + n.variables.len

func copyIntSet(s: IntSet): IntSet =
  # IntSets do a stupid shallowcopy without this
  assign(result, s)

func copy(n: SetNode): SetNode =
  case n.kind:
  of Leaf:
    result = SetNode(data: copyIntSet(n.instructions), kind: Leaf)
  of Object:
    result = SetNode(data: copyIntSet(n.instructions), kind: Object,
                  fields: n.fields)
    for child in result.fields.mvalues:
      child = copy(child)
  of Array:
    result = SetNode(data: copyIntSet(n.instructions), kind: Array,
                  constants: n.constants, variables: n.variables)
    for child in result.constants.mvalues:
      child = copy(child)
    for child in result.variables.mvalues:
      child = copy(child)
  of Infinite:
    result = SetNode(data: copyIntSet(n.instructions), kind: Infinite,
                  constants: n.constants, variables: n.variables)
    for child in result.constants.mvalues:
      child = copy(child)
    for child in result.variables.mvalues:
      child = copy(child)

func copy*(hs: HierarchicalSet): HierarchicalSet = HierarchicalSet(root: copy(hs.root))

func toIntSet*(hs: HierarchicalSet): IntSet =
  func toIntSetAux(node: SetNode, result: var IntSet) =
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
    of Leaf: discard

  toIntSetAux(hs.root, result)

func incl*(hs: var HierarchicalSet, loc: PNode, instr: int) =
  var lastRef = hs.root
  let parts = collectImportantNodes(loc)
  let path = nodesToPath(parts)
  for i in 0..<path.len:
    let nodeKey = path[i]
    template traverseOrCreate(children, key) =
      if key notin children:
        children[key] = nodeToNode(parts[^(i+1)])
      lastRef = children[key]

    case nodeKey.kind
    of field:
      traverseOrCreate(lastRef.fields, nodeKey.field)
    of constant:
      traverseOrCreate(lastRef.constants, nodeKey.constant)
    of variable:
      traverseOrCreate(lastRef.variables, nodeKey.variable)

  lastRef.instructions.incl instr

# Remove loc from the set means to empty it's instruction set
# It may still serve as a path to other locs
# GC loc from the set means to actually remove the node from it,
# which is possible if the node has no instructions and no children.

func excl(hs: var HierarchicalSet, loc: PNode, instr: int) =
  # A single instruction int can only correspond to one location PNode
  # so we only need to find one node to exclude the instruction int from
  var lastRef = hs.root
  let path = nodesToPath(collectImportantNodes(loc))
  for i in 0..<path.len:
    let nodeKey = path[i]
    template traverseOrExit(children, key) =
      if key notin children:
        return
      lastRef = children[key]

    case nodeKey.kind
    of field:
      traverseOrExit(lastRef.fields, nodeKey.field)
    of constant:
      traverseOrExit(lastRef.constants, nodeKey.constant)
    of variable:
      traverseOrExit(lastRef.variables, nodeKey.variable)

  lastRef.instructions.excl instr
  # if lastRef.instructions.len == 0:
  #   #if lastRef.childrenLen == 0: XXX: Cleanup as in
  #   #  Remove it from it's parent, and for the parent of the parent if needed


func incl*(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
  func incl(a, b: SetNode) =
    a.instructions.incl b.instructions
    template inclOrCreate(achilds, bchilds) =
      for k, child in bchilds:
        if k in achilds:
          incl(achilds[k], child)
        else:
          achilds[k] = copy(child)

    case b.kind:
    of Object:
      inclOrCreate(a.fields, b.fields)
    of Array, Infinite:
      inclOrCreate(a.constants, b.constants)
      inclOrCreate(a.variables, b.variables)
    of Leaf:
      discard # Nothing to do

  if b.root == nil:
    debugEcho "HA"
  incl(hs.root, b.root)


func excl*(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
  func excl(a, b: SetNode): bool =
    result = true
    a.instructions.excl b.instructions
    if a.instructions.len > 0: result = false
    template exclAndClean(achilds, bchilds) =
      block:
        var toClean: seq[type(achilds.keys)]
        for k, child in achilds:
          if k in bchilds:
            if excl(child, bchilds[k]):
              toClean.add k
        for k in toClean: achilds.del k

    case a.kind:
    of Object:
      exclAndClean(a.fields, b.fields)
      if a.fields.len > 0: result = false
    of Array, Infinite:
      exclAndClean(a.constants, b.constants)
      exclAndClean(a.variables, b.variables)
      if a.constants.len > 0: result = false
      if a.variables.len > 0: result = false
    of Leaf: discard

  discard excl(hs.root, b.root)


func exclDefinitelyAliased*(hs: var HierarchicalSet, path: seq[NodeKey]): HierarchicalSet =
  result = HierarchicalSet(root: SetNode(kind: Object))
  var lastRef = @[hs.root] #TODO Rename, is a sequence because construction needs the kinds,
                           # could be a single lastRef and a list of kinds too
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
          let nextResLastRef = SetNode(kind: lastRef[i+1].kind) #XXX Or +1??
          resLastRef.fields[nodeKey.field] = nextResLastRef
          resLastRef = nextResLastRef
        of constant:
          let nextResLastRef = SetNode(kind: lastRef[i+1].kind) #XXX Or +1??
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

func exclDefinitelyAliased*(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  exclDefinitelyAliased(hs, nodesToPath(collectImportantNodes(loc)))

type BackLastRef = object
  node: SetNode
  key: NodeKey
  parent: int

func exclMaybeAliased*(hs: var HierarchicalSet, path: seq[NodeKey]): HierarchicalSet =
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
      result = HierarchicalSet(root: SetNode(kind: Object))
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
          lastRefs[idx-1][lr.parent].node = SetNode(kind: lastRefs[idx-1][lr.parent].node.kind) #XXX
        newParents.incl lr.parent
        lastRefs[idx-1][lr.parent].node.putput(lr.key, lr.node)
      parents = newParents

    assert parents.len == 1
    result = HierarchicalSet(root: lastRefs[0][0].node)

  else:
    result = HierarchicalSet(root: SetNode(kind: Object))

func exclMaybeAliased*(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  exclMaybeAliased(hs, nodesToPath(collectImportantNodes(loc)))

func exclMaybeAliasing*(hs: var HierarchicalSet, path: seq[NodeKey]): HierarchicalSet =
  result = HierarchicalSet(root: SetNode(kind: Object))
  var resLastRefs = @[result.root]

  var lastRefs = @[hs.root]
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

              let resNextLastRef = SetNode(kind: nextLastRef.kind,
                                           data: nextLastRef.instructions) #XXX
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

              let resNextLastRef = SetNode(kind: nextLastRef.kind) #XXX
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

            let resNextLastRef = SetNode(kind: nextLastRef.kind,
                                         data: nextLastRef.instructions) #XXX
            resLastRefs[i].children[key] = resNextLastRef
            nextResLastRefs.add resNextLastRef

            nextLastRef.instructions.clear # Remove ...[var/const]
        else:
          if nextLastRef.childrenLen == 0: # Unreachable if hs is cleaned up
            lastRefs[i].children.del key
          else:
            nextLastRefs.add nextLastRef # Recurse into children of ...[var/const]

            let resNextLastRef = SetNode(kind: nextLastRef.kind) #XXX
            resLastRefs[i].children[key] = resNextLastRef
            nextResLastRefs.add resNextLastRef

    case nodeKey.kind
    of field:
      followDefinitelyAliasedPaths(fields, nodeKey.field)
    of constant:
      var nextLastRefs: seq[SetNode]
      var nextResLastRefs: seq[SetNode]

      for i in 0..<lastRefs.len:
        followMaybeAliasedPaths(variables)

      followDefinitelyAliasedPaths(constants, nodeKey.constant)

      lastRefs.add nextLastRefs
      resLastRefs.add nextResLastRefs

    of variable:
      var nextLastRefs: seq[SetNode]
      var nextResLastRefs: seq[SetNode]

      for i in 0..<lastRefs.len:
        followMaybeAliasedPaths(constants)
        followMaybeAliasedPaths(variables)

      lastRefs = nextLastRefs
      resLastRefs = nextResLastRefs

func exclMaybeAliasing*(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  exclMaybeAliasing(hs, nodesToPath(collectImportantNodes(loc)))

proc `$`*(hs: HierarchicalSet): string =
  proc debugNode(lvl: int, key: NodeKey, n: SetNode): string =
    result.add repeat(' ', lvl)
    if lvl == 0:
      result.add "root"
    else:
      result.add $key
    result.add " " & $n.kind & " " & $n.instructions
    result.add "\n"

    case n.kind:
    of Object:
      for k, c in n.fields:
        result.add debugNode(lvl+1, NodeKey(kind: field, field: k), c)

    of Array, Infinite:
      for k, c in n.constants:
        result.add debugNode(lvl+1, NodeKey(kind: constant, constant: k), c)

      for k, c in n.variables:
        result.add debugNode(lvl+1, NodeKey(kind: variable, variable: k), c)

    of Leaf:
      discard

  result = debugNode(0, NodeKey(kind: field), hs.root)

