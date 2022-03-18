import
  std/[
    intsets,
    strtabs,
    strutils,
    tables
  ],
  compiler/ast/[
    ast,
    astalgo,
    renderer,
    types,
    typesrenderer,
    idents,
    lineinfos,
    reports
  ],
  compiler/modules/[
    magicsys,
    modulegraphs
  ],
  compiler/front/[
    msgs,
    options
  ],
  compiler/sem/[
    dfa,
    lowerings,
    parampatterns,
    sighashes,
    liftdestructors,
    optimizer,
    varpartitions
  ]


import sets, hashes


proc skipConvDfa*(n: PNode): PNode =
  result = n
  while true:
    case result.kind
    of nkObjDownConv, nkObjUpConv:
      result = result[0]
    of PathKinds1:
      result = result[1]
    else: break

type AliasKind* = enum
  yes, no, maybe

proc aliases*(obj, field: PNode): AliasKind =
  ##[

============ =========== ====
obj          field       alias kind
------------ ----------- ----
`x`          `x`         true
`x`          `x.f`       true
`x.f`        `x`         false
`x.f`        `x.f`       true
`x.f`        `x.v`       false
`x`          `x[0]`      true
`x[0`]       `x`         false
`x[0`]       `x[0]`      true
`x[0`]       `x[1]`      false
`x`          `x[i]`      true
`x[i`]       `x`         false
`x[i`]       `x[i]`      maybe; Further analysis could make this return true when i is a runtime-constant
`x[i`]       `x[j]`      maybe; also returns maybe if only one of i or j is a compiletime-constant

============ =========== ======

  ]##

  template collectImportantNodes(result, n) =
    var result: seq[PNode]
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
      else: return no

  collectImportantNodes(objImportantNodes, obj)
  collectImportantNodes(fieldImportantNodes, field)

  # If field is less nested than obj, then it cannot be part of/aliased by obj
  if fieldImportantNodes.len < objImportantNodes.len: return no

  result = yes
  for i in 1..objImportantNodes.len:
    # We compare the nodes leading to the location of obj and field
    # with each other.
    # We continue until they diverge, in which case we return no, or
    # until we reach the location of obj, in which case we do not need
    # to look further, since field must be part of/aliased by obj now.
    # If we encounter an element access using an index which is a runtime value,
    # we simply return maybe instead of yes; should further nodes not diverge.
    let currFieldPath = fieldImportantNodes[^i]
    let currObjPath = objImportantNodes[^i]

    if currFieldPath.kind != currObjPath.kind:
      return no

    case currFieldPath.kind
    of nkSym:
      if currFieldPath.sym != currObjPath.sym: return no
    of nkDotExpr:
      if currFieldPath[1].sym != currObjPath[1].sym: return no
    of nkBracketExpr:
      if currFieldPath[1].kind in nkLiterals and currObjPath[1].kind in nkLiterals:
        if currFieldPath[1].intVal != currObjPath[1].intVal:
          return no
      else:
        result = maybe
    else: assert false # unreachable


proc hash(n: PNode): Hash = hash(cast[pointer](n))

proc aliasesCached(cache: var Table[(PNode, PNode), AliasKind], obj, field: PNode): AliasKind =
  let key = (obj, field)
  if not cache.hasKey(key):
    cache[key] = aliases(obj, field)
  cache[key]

proc preprocessCfg(cfg: var ControlFlowGraph) =
  for i in 0..<cfg.len:
    if cfg[i].kind in {goto, fork} and i + cfg[i].dest > cfg.len:
      cfg[i].dest = cfg.len - i

type
  NodeKeyKind = enum
    sym, constant, variable
  NodeKey = object
    case kind: NodeKeyKind
    of sym:
      sym: PSym
    of constant:
      constant: BiggestInt
    of variable:
      variable: PSym
  Node = ref object
    # we need a way to differentiate
    # between a node simply serving as a path to a
    # subnode, or being a node itself. For now we
    # just check if instructions is empty.
    # This is a set because the same location
    # could be read in different instructions
    instructions: IntSet
    # Could also split this into
    # seperate tables for each of the kinds
    symChildren: Table[NodeKey, Node]
    constantChildren: Table[NodeKey, Node]
    variableChildren: Table[NodeKey, Node]

  HierarchicalSet = object
    root: Node

proc hash(n: NodeKey): Hash =
  var h: Hash = 0
  case n.kind
  of sym:
    h = h !& cast[int](n.sym)
  of constant:
    h = h !& cast[int](n.constant)
  of variable:
    h = h !& cast[int](n.variable)
  result = !$h

proc `==`(a, b: NodeKey): bool =
  if a.kind != b.kind: return false
  case a.kind
  of sym: return a.sym == b.sym
  of constant: return a.constant == b.constant
  of variable: return a.variable == b.variable

from algorithm import reversed
from sequtils import toSeq
import compiler/utils/astrepr

proc collectImportantNodes(n: PNode): seq[PNode] =
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
      discard # TODO: return no
      # actually this seems unreachable? Confirm that this is the case in theory too.
      doAssert false, "unreachable"

proc importantNodesToKeys(importantNodes: seq[PNode]): seq[NodeKey] =
  for n in importantNodes:
    case n.kind
    of nkDotExpr:
      doAssert n[1].kind == nkSym
      result.add NodeKey(kind: sym, sym: n[1].sym)
    of nkBracketExpr:
      if n[1].kind in nkLiterals:
        result.add NodeKey(kind: constant, constant: n[1].intVal)
      else:
        #doAssert n[1].kind == nkSym, $n[1].kind
        result.add NodeKey(kind: variable)#, variable: n[1].sym)
    of nkSym:
      result.add NodeKey(kind: sym, sym: n.sym)
    else: doAssert false, "unreachable"

func childrenLen(n: Node): int = n.symChildren.len + n.constantChildren.len + n.variableChildren.len

func copy(n: Node): Node =
  result = Node(
    instructions: n.instructions,
    symChildren: n.symChildren,
    constantChildren: n.constantChildren,
    variableChildren: n.variableChildren
  )
  for child in result.symChildren.mvalues:
    child = copy(child)
  for child in result.constantChildren.mvalues:
    child = copy(child)
  for child in result.variableChildren.mvalues:
    child = copy(child)

func copy(hs: HierarchicalSet): HierarchicalSet = HierarchicalSet(root: copy(hs.root))

func toIntSet(hs: HierarchicalSet): IntSet =
  func toIntSetAux(node: Node, result: var IntSet) =
    result.incl node.instructions
    for n in node.symChildren.values:
      toIntSetAux(n, result)
    for n in node.constantChildren.values:
      toIntSetAux(n, result)
    for n in node.variableChildren.values:
      toIntSetAux(n, result)

  toIntSetAux(hs.root, result)

func incl(hs: var HierarchicalSet, loc: PNode, instr: int) =
  var lastRef = hs.root
  let path = importantNodesToKeys collectImportantNodes(loc).reversed()
  for i in 0..<path.len:
    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      lastRef = lastRef.symChildren.mgetOrPut(nodeKey, Node())
    of constant:
      lastRef = lastRef.constantChildren.mgetOrPut(nodeKey, Node())
    of variable:
      lastRef = lastRef.variableChildren.mgetOrPut(nodeKey, Node())

  lastRef.instructions.incl instr

func excl(hs: var HierarchicalSet, loc: PNode, instr: int) =
  # A single instruction int can only correspond to one location PNode
  # so we only need to find one node to exclude the instruction int from
  var lastRef = hs.root
  let path = importantNodesToKeys collectImportantNodes(loc).reversed()
  for i in 0..<path.len:
    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      if nodeKey notin lastRef.symChildren:
        return
      lastRef = lastRef.symChildren[nodeKey]
    of constant:
      if nodeKey notin lastRef.constantChildren:
        return
      lastRef = lastRef.constantChildren[nodeKey]
    of variable:
      if nodeKey notin lastRef.variableChildren:
        return
      lastRef = lastRef.variableChildren[nodeKey]

  lastRef.instructions.excl instr
  # if lastRef.instructions.len == 0:
  #   #if lastRef.childrenLen == 0: XXX: Cleanup as in
  #   #  Remove it from it's parent, and for the parent of the parent if needed


func incl(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
  func incl(a: Node, b: Node) =
    a.instructions.incl b.instructions

    for k, child in b.symChildren:
      # mGetOrPut would work too
      if k in a.symChildren:
        incl(a.symChildren[k], child)
      else:
        a.symChildren[k] = copy(child)

    for k, child in b.constantChildren:
      if k in a.constantChildren:
        incl(a.constantChildren[k], child)
      else:
        a.constantChildren[k] = copy(child)

    for k, child in b.variableChildren:
      if k in a.variableChildren:
        incl(a.variableChildren[k], child)
      else:
        a.variableChildren[k] = copy(child)

  incl(hs.root, b.root)


func excl(cfg: ControlFlowGraph, hs: var HierarchicalSet, b: HierarchicalSet) =
  func excl(a: Node, b: Node) =
    a.instructions.excl b.instructions
    # if a.instructions.len == 0:
    #   #if a.childrenLen == 0: XXX: cleanup

    for k, child in a.symChildren:
      if k in b.symChildren:
        excl(child, b.symChildren[k])

    for k, child in a.constantChildren:
      if k in b.constantChildren:
        excl(child, b.constantChildren[k])

    for k, child in a.variableChildren:
      if k in b.variableChildren:
        excl(child, b.variableChildren[k])

  excl(hs.root, b.root)


func exclDefinitelyAliased(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  result = HierarchicalSet(root: Node())
  var lastRef = hs.root
  let path = importantNodesToKeys collectImportantNodes(loc).reversed()
  for i in 0..<path.len-1:
    let nodeKey = path[i]
    case nodeKey.kind
    of sym:
      if nodeKey notin lastRef.symChildren: return # Nothing to exclude
      lastRef = lastRef.symChildren[nodeKey]
    of constant:
      if nodeKey notin lastRef.constantChildren: return # Nothing to exclude
      lastRef = lastRef.constantChildren[nodeKey]
    of variable:
      return # not definitely aliased

  template popLocLeaf(children) =
    if locLeaf in lastRef.children:
      var resLastRef = result.root
      for i in 0..<path.len-1:
        let nodeKey = path[i]
        case nodeKey.kind
        of sym:
          let nextResLastRef = Node()
          resLastRef.symChildren[nodeKey] = nextResLastRef
          resLastRef = nextResLastRef
        of constant:
          let nextResLastRef = Node()
          resLastRef.constantChildren[nodeKey] = nextResLastRef
          resLastRef = nextResLastRef
        of variable:
          doAssert false, "unreachable"
      resLastRef.children[locLeaf] = lastRef.children[locLeaf]
      lastRef.children.del locLeaf

  # Remove loc, loc.X, loc[i], loc[1]
  let locLeaf = path[^1]
  case locLeaf.kind
  of sym: popLocLeaf(symChildren)
  of constant: popLocLeaf(constantChildren)
  of variable: discard # not definitely aliased

type BackLastRef = object
  node: Node
  key: NodeKey
  parent: int

func exclMaybeAliased(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  let path = importantNodesToKeys collectImportantNodes(loc).reversed()
  var lastRefs = @[@[BackLastRef(node: hs.root)]]
  lastRefs.setLen path.len
  for idx in 0..<path.len-1:
    let nodeKey = path[idx]

    template followDefinitelyAliasedPaths(children) =
      if nodeKey in lastRef.node.children:
        lastRefs[idx+1].add:
          BackLastRef(
            node: lastRef.node.children[nodeKey],
            key: nodeKey, parent: i)

    template followMaybeAliasedPaths(children) =
      for k, child in lastRef.node.children:
        lastRefs[idx+1].add:
          BackLastRef(
            node: child,
            key: k, parent: i)

    case nodeKey.kind
    of sym:
      for i, lastRef in lastRefs[idx]:
        followDefinitelyAliasedPaths(symChildren)
    of constant:
      for i, lastRef in lastRefs[idx]:
        followMaybeAliasedPaths(variableChildren)
        followDefinitelyAliasedPaths(constantChildren)
    of variable:
      for i, lastRef in lastRefs[idx]:
        followMaybeAliasedPaths(variableChildren)
        followMaybeAliasedPaths(constantChildren)

    if lastRefs[idx+1].len == 0:
      result = HierarchicalSet(root: Node())
      return # Nothing to exclude

  # Remove loc, loc.X, loc[i], loc[1]
  var lastNodes: seq[BackLastRef]
  let locLeaf = path[^1]
  template popDefinitelyAliasedLeaf(children) =
    if locLeaf in lastRef.node.children:
      lastNodes.add BackLastRef(
        node: lastRef.node.children[locLeaf],
        key: locLeaf, parent: lastRef.parent)
      lastRef.node.children.del locLeaf

  template popMaybeAliasedLeaf(children) =
    for k, child in lastRef.node.children:
      lastNodes.add BackLastRef(
        node: child,
        key: k, parent: lastRef.parent)
    lastRef.node.children.clear


  case locLeaf.kind
  of sym:
    for lastRef in lastRefs[^1]:
      popDefinitelyAliasedLeaf(symChildren)
  of constant:
    for lastRef in lastRefs[^1]:
      popDefinitelyAliasedLeaf(constantChildren)
      popMaybeAliasedLeaf(variableChildren)
  of variable:
    for lastRef in lastRefs[^1]:
      popMaybeAliasedLeaf(constantChildren)
      popMaybeAliasedLeaf(variableChildren)

  template putput(node, key, child) =
    case key.kind
    of sym: node.symChildren[key] = child
    of constant: node.constantChildren[key] = child
    of variable: node.variableChildren[key] = child


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
          lastRefs[idx-1][lr.parent].node = Node()
        newParents.incl lr.parent
        lastRefs[idx-1][lr.parent].node.putput(lr.key, lr.node)
      parents = newParents

    assert parents.len == 1
    result = HierarchicalSet(root: lastRefs[0][0].node)

  else:
    result = HierarchicalSet(root: Node())

func exclMaybeAliasing(hs: var HierarchicalSet, loc: PNode): HierarchicalSet =
  result = HierarchicalSet(root: Node())
  var resLastRefs = @[result.root]

  var lastRefs = @[hs.root]
  let path = importantNodesToKeys collectImportantNodes(loc).reversed()
  for j in 0..<path.len:
    let nodeKey = path[j]

    template followDefinitelyAliasedPaths(children) =
      var i = 0
      while i < lastRefs.len:
        if nodeKey notin lastRefs[i].children:
          lastRefs.del i
          resLastRefs.del i # XXX: Cleanup result???
        else:
          let nextLastRef = lastRefs[i].children[nodeKey]
          if nextLastRef.instructions.len > 0:
            if nextLastRef.childrenLen == 0:
              lastRefs[i].children.del nodeKey # Remove path leading to loc
              lastRefs.del i

              resLastRefs[i].children[nodeKey] = nextLastRef
              resLastRefs.del i
            else:
              lastRefs[i] = nextLastRef

              let resNextLastRef = Node(instructions: nextLastRef.instructions)
              resLastRefs[i].children[nodeKey] = resNextLastRef
              resLastRefs[i] = resNextLastRef

              nextLastRef.instructions.clear # Remove node on path leading to loc

              inc i
          else:
            if nextLastRef.childrenLen == 0: # Unreachable if hs is cleaned up
              lastRefs[i].children.del nodeKey
              lastRefs.del i

              resLastRefs.del i
            else:
              lastRefs[i] = nextLastRef

              let resNextLastRef = Node()
              resLastRefs[i].children[nodeKey] = resNextLastRef
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

            let resNextLastRef = Node(instructions: nextLastRef.instructions)
            resLastRefs[i].children[key] = resNextLastRef
            nextResLastRefs.add resNextLastRef

            nextLastRef.instructions.clear # Remove ...[var/const]
        else:
          if nextLastRef.childrenLen == 0: # Unreachable if hs is cleaned up
            lastRefs[i].children.del key
          else:
            nextLastRefs.add nextLastRef # Recurse into children of ...[var/const]

            let resNextLastRef = Node()
            resLastRefs[i].children[key] = resNextLastRef
            nextResLastRefs.add resNextLastRef

    case nodeKey.kind
    of sym:
      followDefinitelyAliasedPaths(symChildren)
    of constant:
      var nextLastRefs: seq[Node]
      var nextResLastRefs: seq[Node]

      for i in 0..<lastRefs.len:
        followMaybeAliasedPaths(variableChildren)

      followDefinitelyAliasedPaths(constantChildren)

      lastRefs.add nextLastRefs
      resLastRefs.add nextResLastRefs

    of variable:
      var nextLastRefs: seq[Node]
      var nextResLastRefs: seq[Node]

      for i in 0..<lastRefs.len:
        followMaybeAliasedPaths(constantChildren)
        followMaybeAliasedPaths(variableChildren)

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

from compiler/sem/injectdestructors import dbg

type
  State = ref object
    lastReads: HierarchicalSet
    potentialLastReads: HierarchicalSet
    notLastReads: HierarchicalSet
    alreadySeen: HashSet[PNode]

template incl(a, b) = cfg.incl(a, b)
template excl(a, b) = cfg.excl(a, b)

func mergeStates(cfg: ControlFlowGraph, a: var State, b: sink State) =
  # Inplace for performance:
  #   lastReads = a.lastReads + b.lastReads
  #   potentialLastReads = (a.potentialLastReads + b.potentialLastReads) - (a.notLastReads + b.notLastReads)
  #   notLastReads = a.notLastReads + b.notLastReads
  #   alreadySeen = a.alreadySeen + b.alreadySeen
  # b is never nil
  if a == nil:
    a = b
  else:
    a.lastReads.incl b.lastReads

    a.potentialLastReads.incl b.potentialLastReads
    a.potentialLastReads.excl a.notLastReads
    a.potentialLastReads.excl b.notLastReads

    a.notLastReads.incl b.notLastReads

    a.alreadySeen.incl b.alreadySeen

proc debugAux(node: Node, result: var string) =
  if node.instructions.len > 0:
    result.add "X"
  else:
    result.add "O"
  result.add "{"
  for n in node.symChildren.values:
    debugAux(n, result)
  for n in node.constantChildren.values:
    debugAux(n, result)
  for n in node.variableChildren.values:
    debugAux(n, result)
  result.add "}"

proc debugA(hs: HierarchicalSet): string =
  debugAux(hs.root, result)

proc computeLastReadsAndFirstWrites*(cfg: ControlFlowGraph) =
  var cache = initTable[(PNode, PNode), AliasKind]()
  template aliasesCached(obj, field: PNode): AliasKind =
    aliasesCached(cache, obj, field)

  var cfg = cfg
  preprocessCfg(cfg)

  var states = newSeq[State](cfg.len + 1)
  states[0] = State(
    lastReads: HierarchicalSet(root: Node()),
    potentialLastReads: HierarchicalSet(root: Node()),
    notLastReads: HierarchicalSet(root: Node()),
  )

  for pc in 0..<cfg.len:
    template state: State = states[pc]
    if state != nil:
      dbg:
        echo "pc:",pc
        echo "lastReads:",toIntSet(state.lastReads)
        echo "potentialLastReads:",toIntSet(state.potentialLastReads)
        echo "notLastReads:",toIntSet(state.notLastReads)
      case cfg[pc].kind
      of def:
        # the path leads to a redefinition of 's' --> sink 's'.
        state.lastReads.incl state.potentialLastReads.exclDefinitelyAliased(cfg[pc].n)

        # only partially writes to 's' --> can't sink 's', so this def reads 's'
        # or maybe writes to 's' --> can't sink 's'
        var notLastReads = state.potentialLastReads.exclMaybeAliasing(cfg[pc].n)
        state.notLastReads.incl notLastReads
        for i in toIntSet(notLastReads):
          cfg[i].n.comment = '\n' & $pc

        var alreadySeenThisNode = false
        for s in state.alreadySeen:
          if cfg[pc].n.aliasesCached(s) != no or s.aliasesCached(cfg[pc].n) != no:
            alreadySeenThisNode = true; break
        if alreadySeenThisNode: cfg[pc].n.flags.excl nfFirstWrite
        else: cfg[pc].n.flags.incl nfFirstWrite

        state.alreadySeen.incl cfg[pc].n

        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of use:
        var notLastReads = state.potentialLastReads.exclMaybeAliased(cfg[pc].n)
        notLastReads.incl state.potentialLastReads.exclMaybeAliasing(cfg[pc].n)

        state.notLastReads.incl notLastReads
        for i in toIntSet(notLastReads):
          cfg[i].n.comment = '\n' & $pc

        state.potentialLastReads.incl(cfg[pc].n, pc)

        state.alreadySeen.incl cfg[pc].n

        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of goto:
        cfg.mergeStates(states[pc + cfg[pc].dest], move(states[pc]))
      of fork:
        var copy = State(
          lastReads: copy(state.lastReads),
          potentialLastReads: copy(state.potentialLastReads),
          notLastReads: copy(state.notLastReads),
          alreadySeen: state.alreadySeen
        )

        cfg.mergeStates(states[pc + cfg[pc].dest], copy)
        cfg.mergeStates(states[pc + 1], move(states[pc]))

  let lastReads = (toIntSet(states[^1].lastReads) + toIntSet(states[^1].potentialLastReads)) - toIntSet(states[^1].notLastReads)
  var lastReadTable: Table[PNode, seq[int]]
  for position, node in cfg:
    if node.kind == use:
      lastReadTable.mgetOrPut(node.n, @[]).add position
  for node, positions in lastReadTable:
    block checkIfAllPosLastRead:
      for p in positions:
        if p notin lastReads: break checkIfAllPosLastRead
      node.flags.incl nfLastRead



type
  OLDState = ref object
    lastReads: IntSet
    potentialLastReads: IntSet
    notLastReads: IntSet
    alreadySeen: HashSet[PNode]

proc oLDmergeStates(a: var OLDState, b: sink OLDState) =
  # Inplace for performance:
  #   lastReads = a.lastReads + b.lastReads
  #   potentialLastReads = (a.potentialLastReads + b.potentialLastReads) - (a.notLastReads + b.notLastReads)
  #   notLastReads = a.notLastReads + b.notLastReads
  #   alreadySeen = a.alreadySeen + b.alreadySeen
  # b is never nil
  if a == nil:
    a = b
  else:
    a.lastReads.incl b.lastReads
    a.potentialLastReads.incl b.potentialLastReads
    a.potentialLastReads.excl a.notLastReads
    a.potentialLastReads.excl b.notLastReads
    a.notLastReads.incl b.notLastReads
    a.alreadySeen.incl b.alreadySeen

proc oLDcomputeLastReadsAndFirstWrites*(cfg: ControlFlowGraph) =
  var cache = initTable[(PNode, PNode), AliasKind]()
  template aliasesCached(obj, field: PNode): AliasKind =
    aliasesCached(cache, obj, field)

  var cfg = cfg
  preprocessCfg(cfg)

  var states = newSeq[OLDState](cfg.len + 1)
  states[0] = OLDState()

  for pc in 0..<cfg.len:
    template state: OLDState = states[pc]
    if state != nil:
      dbg:
        echo "pc:",pc
        echo "lastReads:",state.lastReads
        echo "potentialLastReads:",state.potentialLastReads
        echo "notLastReads:",state.notLastReads
      case cfg[pc].kind
      of def:
        var potentialLastReadsCopy = state.potentialLastReads
        for r in potentialLastReadsCopy:
          if cfg[pc].n.aliasesCached(cfg[r].n) == yes:
            # the path leads to a redefinition of 's' --> sink 's'.
            state.lastReads.incl r
            state.potentialLastReads.excl r
          elif cfg[r].n.aliasesCached(cfg[pc].n) != no:
            # only partially writes to 's' --> can't sink 's', so this def reads 's'
            # or maybe writes to 's' --> can't sink 's'
            cfg[r].n.comment = '\n' & $pc
            state.potentialLastReads.excl r
            state.notLastReads.incl r

        var alreadySeenThisNode = false
        for s in state.alreadySeen:
          if cfg[pc].n.aliasesCached(s) != no or s.aliasesCached(cfg[pc].n) != no:
            alreadySeenThisNode = true; break
        if alreadySeenThisNode: cfg[pc].n.flags.excl nfFirstWrite
        else: cfg[pc].n.flags.incl nfFirstWrite

        state.alreadySeen.incl cfg[pc].n

        oLDmergeStates(states[pc + 1], move(states[pc]))
      of use:
        var potentialLastReadsCopy = state.potentialLastReads
        for r in potentialLastReadsCopy:
          if cfg[pc].n.aliasesCached(cfg[r].n) != no or cfg[r].n.aliasesCached(cfg[pc].n) != no:
            cfg[r].n.comment = '\n' & $pc
            state.potentialLastReads.excl r
            state.notLastReads.incl r

        state.potentialLastReads.incl pc

        state.alreadySeen.incl cfg[pc].n

        oLDmergeStates(states[pc + 1], move(states[pc]))
      of goto:
        oLDmergeStates(states[pc + cfg[pc].dest], move(states[pc]))
      of fork:
        var copy = OLDState()
        copy[] = states[pc][]
        oLDmergeStates(states[pc + cfg[pc].dest], copy)
        oLDmergeStates(states[pc + 1], move(states[pc]))

  let lastReads = (states[^1].lastReads + states[^1].potentialLastReads) - states[^1].notLastReads
  var lastReadTable: Table[PNode, seq[int]]
  for position, node in cfg:
    if node.kind == use:
      lastReadTable.mgetOrPut(node.n, @[]).add position
  for node, positions in lastReadTable:
    block checkIfAllPosLastRead:
      for p in positions:
        if p notin lastReads: break checkIfAllPosLastRead
      node.flags.incl nfLastRead

proc isLastRead*(n: PNode): bool =
  let m = skipConvDfa(n)
  (m.kind == nkSym and sfSingleUsedTemp in m.sym.flags) or nfLastRead in m.flags

proc isFirstWrite*(n: PNode): bool =
  let m = skipConvDfa(n)
  nfFirstWrite in m.flags

proc initialized*(code: ControlFlowGraph; pc: int,
                 init, uninit: var IntSet; until: int): int =
  ## Computes the set of definitely initialized variables across all code paths
  ## as an IntSet of IDs.
  var pc = pc
  while pc < code.len:
    case code[pc].kind
    of goto:
      pc += code[pc].dest
    of fork:
      var initA = initIntSet()
      var initB = initIntSet()
      var variantA = pc + 1
      var variantB = pc + code[pc].dest
      while variantA != variantB:
        if max(variantA, variantB) > until:
          break
        if variantA < variantB:
          variantA = initialized(code, variantA, initA, uninit, min(variantB, until))
        else:
          variantB = initialized(code, variantB, initB, uninit, min(variantA, until))
      pc = min(variantA, variantB)
      # we add vars if they are in both branches:
      for v in initA:
        if v in initB:
          init.incl v
    of use:
      let v = code[pc].n.sym
      if v.kind != skParam and v.id notin init:
        # attempt to read an uninit'ed variable
        uninit.incl v.id
      inc pc
    of def:
      let v = code[pc].n.sym
      init.incl v.id
      inc pc
  return pc

