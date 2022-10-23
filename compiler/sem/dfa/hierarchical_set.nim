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

proc hash(s: PSym): Hash = hash(cast[pointer](s))

proc hash(k: NodeKey): Hash =
  result = result !& hash(k.kind)
  case k.kind
  of field:
    result = result !& hash(k.field)
  of constant:
    result = result !& hash(k.constant)
  of variable:
    result = result !& hash(k.variable)
  result = !$result

proc `==`(a, b: NodeKey): bool =
  if a.kind != b.kind:
    false
  else:
    case a.kind
    of field:
      b.field == b.field
    of constant:
      b.constant == b.constant
    of variable:
      b.variable == b.variable

type
  NodeKind = enum
    Leaf
    Object
    Array
    Infinite
  Node[T] = ref object
    # we need a way to differentiate
    # between a node simply serving as a path to a
    # subnode, or being a node itself. For now we
    # just check if instructions is empty.
    # This is a set because the same location
    # could be read in different instructions
    data: T
    kind: NodeKind
    fields: Table[PSym, Node[T]]
    constants: Table[BiggestInt, Node[T]]
    variables: Table[PSym, Node[T]]

  SetNode = Node[IntSet]

  HierarchicalSet = object
    root: SetNode

template instructions(n: SetNode): IntSet = n.data

import compiler/utils/astrepr

proc hash(n: PNode): Hash = hash(cast[pointer](n))

proc typeOfNode(n: PNode): PType =
  const skipped = {tyAlias, tyDistinct, tyGenericInst,
    tyRef, tyPtr, tyVar, tySink, tyLent, tyOwned}
  result = n.typ.skipTypes(skipped)
  # HACK: sometimes typ is tyUntyped, in that case we try to get the sym typ instead
  if result.kind == tyUntyped and n.kind == nkSym:
    result = n.sym.typ.skipTypes(skipped)

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
    #debug typ
    doAssert false, $typ.kind

proc nodeToNode(n: PNode): SetNode =
  let typ = typeOfNode(n)
  result = SetNode(kind: typeToKind(typ))
    
from sequtils import toSeq
from compiler/ast/typesrenderer import `$`

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

func nodesToPath(importantNodes: seq[PNode]): seq[NodeKey] =
  for i in countdown(importantNodes.len-1, 0):
    let n = importantNodes[i]

    case n.kind
    of nkDotExpr:
      doAssert n[1].kind == nkSym
      result.add NodeKey(kind: field, field: n[1].sym)
    of nkBracketExpr:
      let typ = typeOfNode(n[0])
      if typ.kind == tyTuple: # Indexing a tuple
        # hack because sem doesn't transform tup[X] to tup.field_X
        if typ.n != nil:
          result.add NodeKey(kind: field, field: typ.n.sons[n[1].intVal].sym)
        else: # Unnamed tuple fields
          {.cast(noSideEffect).}:
            if fakeTupleIndexSyms.len < n[1].intVal + 1:
              fakeTupleIndexSyms.setLen n[1].intVal + 1
            if fakeTupleIndexSyms[n[1].intVal] == nil:
              fakeTupleIndexSyms[n[1].intVal] =
                newSym(skField, nil,
                       ItemId() #[nextSymId c.idgen]#, nil, n[1].info)
            result.add NodeKey(kind: field, field: fakeTupleIndexSyms[n[1].intVal])
      else:
        result.add if n[1].kind in nkLiterals:
                     NodeKey(kind: constant, constant: n[1].intVal)
                   else:
                     NodeKey(kind: variable, variable: nil)
                       # Could be a sym or a call
                       # but currently all variables treated as one (nil)
    of nkSym:
      # A "field" of the stack/environment
      result.add NodeKey(kind: field, field: n.sym)

    else: doAssert false, "unreachable"

  #debugEcho result

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

func copy(hs: HierarchicalSet): HierarchicalSet = HierarchicalSet(root: copy(hs.root))

func toIntSet(hs: HierarchicalSet): IntSet =
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

func incl(hs: var HierarchicalSet, loc: PNode, instr: int) =
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


func incl(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
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


func excl(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
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


func exclDefinitelyAliased(hs: var HierarchicalSet, path: seq[NodeKey]): HierarchicalSet =
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

func exclDefinitelyAliased(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  exclDefinitelyAliased(hs, nodesToPath(collectImportantNodes(loc)))

type BackLastRef = object
  node: SetNode
  key: NodeKey
  parent: int

func exclMaybeAliased(hs: var HierarchicalSet, path: seq[NodeKey]): HierarchicalSet =
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

func exclMaybeAliased(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  exclMaybeAliased(hs, nodesToPath(collectImportantNodes(loc)))

func exclMaybeAliasing(hs: var HierarchicalSet, path: seq[NodeKey]): HierarchicalSet =
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

func exclMaybeAliasing(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  exclMaybeAliasing(hs, nodesToPath(collectImportantNodes(loc)))

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

proc reprHS(hs: HierarchicalSet): string =
  proc debugNode(lvl: int, key: NodeKey, n: SetNode): string =
    result.add repeat(' ', lvl)
    if lvl == 0:
      result.add "root"
    else:
      result.add reprNodeKey key
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

proc debugA(hs: HierarchicalSet): HierarchicalSet =
  echo reprHS hs
  hs

func shiftedCopy(s: IntSet, shift: int): IntSet =
  for i in s:
    result.incl i + shift

func shiftedCopy(n: SetNode, shift: int): SetNode =
  case n.kind:
  of Leaf:
    result = SetNode(data: shiftedCopy(n.instructions, shift), kind: Leaf)
  of Object:
    result = SetNode(data: shiftedCopy(n.instructions, shift), kind: Object,
                  fields: n.fields)
    for child in result.fields.mvalues:
      child = copy(child)
  of Array:
    result = SetNode(data: shiftedCopy(n.instructions, shift), kind: Array,
                  constants: n.constants, variables: n.variables)
    for child in result.constants.mvalues:
      child = copy(child)
    for child in result.variables.mvalues:
      child = copy(child)
  of Infinite:
    result = SetNode(data: shiftedCopy(n.instructions, shift), kind: Infinite,
                  constants: n.constants, variables: n.variables)
    for child in result.constants.mvalues:
      child = copy(child)
    for child in result.variables.mvalues:
      child = copy(child)

func shiftedCopy(hs: HierarchicalSet, shift: int): HierarchicalSet = HierarchicalSet(root: shiftedCopy(hs.root, shift))
