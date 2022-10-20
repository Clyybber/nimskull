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
    idents,
    lineinfos,
    reports
  ],
  compiler/modules/modulegraphs,
  compiler/front/[
    msgs,
    options
  ],
  compiler/sem/dfa/cfg

const toDebug* {.strdefine.} = ""
when toDebug.len > 0:
  var shouldDebug* = false

template dbg*(body) =
  when toDebug.len > 0:
    if shouldDebug:
      body

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

include compiler/sem/dfa/hierarchical_set

when true: # disabled for now
  include compiler/sem/dfa/taint_tree

  type
    PathCache = object
      # This captures the effect a section
      # of cfg code has, with a single start and exit
      lastReads: HierarchicalSet
        # All last reads this section added internally,
        # that means not last reads that occured before
        # this section and were made last reads because
        # of a write in this section
      potentialLastReads: HierarchicalSet
        # All potential last reads this section added
        # internally, that means not potential last reads
        # that occured before this section,
        # and survived in this section
      notLastReads: HierarchicalSet
        # All uses that are definitely not last reads,
        # internal and external to this section
      hull: TaintTree
        # This contains all locations that this section
        # would turn into external last reads
        # Only this set probably needs to be hierarchical
        # This could also be all locations that this section
        # would not turn into external last reads
        #  -> time
        # s   w
        # s.x  r
        # s.y   r
        # v   r
        # v.x  w
        # v.y   r
        # t.x w
        # t.y  r
        # t     w
        # u.x r
        # u.y  w
        # u     r
        # r.x w
        # r.y  w
        # r     r
        # w.x r
        # w.y  r
        # w     w
        # ===
        # hull(writes):
        # w(s) + w(t.x) + w(u.y) + w(r.x) + w(r.y) + ~w(w-w.x-w.y)~
        # which will turn into last reads:
        # s      t.x      u.y      r.x      r.y      XXX: Same issue as below  
        # s.x                        \___r__/
        # s.y
        # vs
        # hull(reads)
        # r(v) (+ r(v.y)) + r(t.y) + r(u.x) + ~r(r-r.x-r.y)~
        # XXX: r-r.x-r.y is empty or not?
        #   In r(r.x) r(r.y) w(r) nothing will be sinked
        #   currently. For it to be we'd need type info.
        #   And then also handle ref objects and shit.
        # Regarding the XXX it makes sense to make reads or writes occuring before
        # reads or writes of their parents exclude those from the hull. This is consistent
        # with not doing the above (which needs typeinfo and shit)
        # What about locations not touched at all by this section?
        # -> We need both a write and read hull
        # lastReads.add potentialLastReads.exclDefinitelyAliased(hull(writes))
        # notLastReads.add potentialLastReads.exclMaybeAliasing(hull(writes))
        # notLastReads.add potentialLastReads.exclMaybeAliased(hull(read))
        # notLastReads.add potentialLastReads.exclMaybeAliasing(hull(read))
        # XXX: But if in the hull childs exclude parents then the hulls can together
        # add up to less than all touched locations
        # -> Keep write hull and hull of everything touched
        # XXX: Hull doesn't mean definitelyAliased, it also goes "up", via maybeAliasing

    Cache = object
      exits: Table[int, PathCache]
      start: int
      stop: int

  proc debugTaints(cfg: ControlFlowGraph, start = 0, stop = cfg.len) =
    type State = ref object
      taintTree: TaintTree

    func mergeStates(cfg: ControlFlowGraph, a: var State, b: sink State) =
      if a == nil:
        a = b
      else:
        cfg.mergeTaintTrees a.taintTree, b.taintTree

    var states = newSeq[State](cfg.len + 1)
    states[start] = State(taintTree: TaintTree(readRoot: TaintNode(), writeRoot: TaintNode()))

    for pc in start..<stop:
      template state: State = states[pc]
      if state != nil:
        dbg:
          echo "pc:",pc
          echo "taintTree:", $state.taintTree
        case cfg[pc].kind
        of def:
          state.taintTree.taintWrite cfg[pc].n

          cfg.mergeStates(states[pc + 1], move(states[pc]))
        of use:
          state.taintTree.taintRead cfg[pc].n

          cfg.mergeStates(states[pc + 1], move(states[pc]))
        of goto:
          cfg.mergeStates(states[pc + cfg[pc].dest], move(states[pc]))
        of fork:
          var copy = State(
            taintTree: copy(state.taintTree)
          )

          cfg.mergeStates(states[pc + cfg[pc].dest], copy)
          cfg.mergeStates(states[pc + 1], move(states[pc]))
        of cachew, cacher: # Skip; not handled
          cfg.mergeStates(states[pc + 1], move(states[pc]))

  func applyTaintTree(cfg: ControlFlowGraph, s: var HierarchicalSet, t: TaintTree):
    tuple[lastReads, notLastReads: HierarchicalSet] =

    proc applyTaintTreeAux(cfg: ControlFlowGraph, writeNode, readNode: TaintNode) =
      if writeNode.taint:
        discard

proc computeLastReads(cfg: ControlFlowGraph) =

  type State = ref object
    lastReads: HierarchicalSet
    potentialLastReads: HierarchicalSet
    notLastReads: HierarchicalSet

  when false:
    func applyPathCache(cfg: ControlFlowGraph, a: var State, c: PathCache) =
      if a == nil:
        a = State(
          lastReads: HierarchicalSet(root: Node(kind: Object)),
          potentialLastReads: HierarchicalSet(root: Node(kind: Object)),
          notLastReads: HierarchicalSet(root: Node(kind: Object)),
        )
      else:
        let (lastReads, notLastReads) = cfg.applyTaintTree(a.potentialLastReads, c.hull)
          # Modifies potentialLastReads already, no need to do that ourselves

        a.lastReads.incl lastReads # TaintTree
        a.notLastReads.incl notLastReads # TaintTree

        a.lastReads.incl c.lastReads

        a.potentialLastReads.incl c.potentialLastReads
        a.potentialLastReads.excl a.notLastReads # Is this unneccessary?
        a.potentialLastReads.excl c.notLastReads # it helps performance

        a.notLastReads.incl c.notLastReads

        # And if it is neccessary, then why not do
        # a.notLastReads.incl c.notLastReads
        # a.potentialLastReads.excl a.notLastReads
        # instead

  func mergeStates(cfg: ControlFlowGraph, a: var State, b: sink State) =
    # Inplace for performance:
    #   lastReads = a.lastReads + b.lastReads
    #   potentialLastReads = (a.potentialLastReads + b.potentialLastReads) - (a.notLastReads + b.notLastReads)
    #   notLastReads = a.notLastReads + b.notLastReads
    # b is never nil
    if a == nil:
      a = b
    else:
      a.lastReads.incl b.lastReads

      a.potentialLastReads.incl b.potentialLastReads
      a.potentialLastReads.excl a.notLastReads
      a.potentialLastReads.excl b.notLastReads

      a.notLastReads.incl b.notLastReads

  var states = newSeq[State](cfg.len + 1)
  states[0] = State(
    lastReads: HierarchicalSet(root: Node(kind: Object)),
    potentialLastReads: HierarchicalSet(root: Node(kind: Object)),
    notLastReads: HierarchicalSet(root: Node(kind: Object)),
  )

  when false:
    var caches: seq[Cache]

  for pc in 0..<cfg.len:
    template state: State = states[pc]
    if state != nil:
      dbg:
        echo "pc:",pc
        echo "lastReads:",reprHS(state.lastReads)
        echo "potentialLastReads:",reprHS(state.potentialLastReads)
        echo "notLastReads:",reprHS(state.notLastReads)
      case cfg[pc].kind
      of def:
        # the path leads to a redefinition of 's' --> sink 's'.
        state.lastReads.incl state.potentialLastReads.exclDefinitelyAliased(cfg[pc].n)

        # only partially writes to 's' --> can't sink 's', so this def reads 's'
        # or maybe writes to 's' --> can't sink 's'
        # This "def reads 's'" matters for seq/ref, but if writes access to these
        # is generated as a use s then maybe we could be more greedy here
        # That def would however also excl maybe aliased not only maybe aliasing,
        # so what would ultimately be best is to split the location s from s[].x..s[].y
        var notLastReads = state.potentialLastReads.exclMaybeAliasing(cfg[pc].n)
        state.notLastReads.incl notLastReads
        for i in toIntSet(notLastReads):
          cfg[i].n.comment = '\n' & $pc

        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of use:
        var notLastReads = state.potentialLastReads.exclMaybeAliased(cfg[pc].n)
        notLastReads.incl state.potentialLastReads.exclMaybeAliasing(cfg[pc].n)

        state.notLastReads.incl notLastReads
        for i in toIntSet(notLastReads):
          cfg[i].n.comment = '\n' & $pc

        # discard debugA state.potentialLastReads
        # echo renderTree cfg[pc].n
        # echo reprNodeKeys nodeToPath cfg[pc].n
        # echo len nodeToPath cfg[pc].n
        state.potentialLastReads.incl(cfg[pc].n, pc)

        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of goto:
        cfg.mergeStates(states[pc + cfg[pc].dest], move(states[pc]))
      of fork:
        var copy = State(
          lastReads: copy(state.lastReads),
          potentialLastReads: copy(state.potentialLastReads),
          notLastReads: copy(state.notLastReads),
        )

        cfg.mergeStates(states[pc + cfg[pc].dest], copy)
        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of cachew, cacher: # TODO
        cfg.mergeStates(states[pc + 1], move(states[pc]))

  let lastReads = (states[^1].lastReads.toIntSet + states[^1].potentialLastReads.toIntSet) -
                   states[^1].notLastReads.toIntSet
  var lastReadTable: Table[PNode, seq[int]]
  for position, node in cfg:
    if node.kind == use:
      lastReadTable.mgetOrPut(node.n, @[]).add position
  for node, positions in lastReadTable:
    block checkIfAllPosLastRead:
      for p in positions:
        if p notin lastReads: break checkIfAllPosLastRead
      node.flags.incl nfLastRead

proc computeFirstWrites(cfg: ControlFlowGraph) =

  type State = ref object
    alreadySeen: HashSet[PNode]

  func mergeStates(cfg: ControlFlowGraph, a: var State, b: sink State) =
    # Inplace for performance:
    #   alreadySeen = a.alreadySeen + b.alreadySeen
    # b is never nil
    if a == nil:
      a = b
    else:
      a.alreadySeen.incl b.alreadySeen

  var cache = initTable[(PNode, PNode), AliasKind]()
  proc aliasesCached(obj, field: PNode): AliasKind =
    let key = (obj, field)
    if not cache.hasKey(key):
      cache[key] = aliases(obj, field)
    cache[key]

  var states = newSeq[State](cfg.len + 1)
  states[0] = State()

  for pc in 0..<cfg.len:
    template state: State = states[pc]
    if state != nil:
      case cfg[pc].kind
      of def:
        block firstTime:
          block alreadySeen:
            for s in state.alreadySeen:
              if aliasesCached(cfg[pc].n, s) != no or
                 aliasesCached(s, cfg[pc].n) != no:
                break alreadySeen
            cfg[pc].n.flags.incl nfFirstWrite
            break firstTime

          cfg[pc].n.flags.excl nfFirstWrite

        state.alreadySeen.incl cfg[pc].n

        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of use:
        state.alreadySeen.incl cfg[pc].n

        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of goto:
        cfg.mergeStates(states[pc + cfg[pc].dest], move(states[pc]))
      of fork:
        var copy = State(
          alreadySeen: state.alreadySeen
        )

        cfg.mergeStates(states[pc + cfg[pc].dest], copy)
        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of cachew, cacher: # NYI
        cfg.mergeStates(states[pc + 1], move(states[pc]))

proc isLastRead*(n: PNode): bool =
  let m = skipConvDfa(n)
  (m.kind == nkSym and sfSingleUsedTemp in m.sym.flags) or nfLastRead in m.flags

proc isFirstWrite*(n: PNode): bool =
  let m = skipConvDfa(n)
  nfFirstWrite in m.flags

proc computeLastReadsAndFirstWrites*(cfg: ControlFlowGraph) =

  proc preprocessCfg(cfg: var ControlFlowGraph) =
    for i in 0..<cfg.len:
      if cfg[i].kind in {goto, fork} and i + cfg[i].dest > cfg.len:
        cfg[i].dest = cfg.len - i

  var cfg = cfg
  preprocessCfg(cfg)
  computeLastReads(cfg)
  computeFirstWrites(cfg)
  dbg:
    debugTaints(cfg)

when false:
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

