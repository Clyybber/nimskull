import
  std/[
    intsets,
    tables,
    sets,
    hashes
  ],
  compiler/ast/[
    ast,
    renderer,
    reports
  ],
  compiler/front/[
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

import compiler/sem/dfa/[setnode, hierarchical_set, taint_tree]

template incl(a, b) = cfg.incl(a, b)
template excl(a, b) = cfg.excl(a, b)

proc computeLastReads(cfg: ControlFlowGraph) =

  type
    State = ref object
      lastReads: HierarchicalSet
      potentialLastReads: HierarchicalSet
      notLastReads: HierarchicalSet

    PathCache = object
      # This captures the effect a section
      # of cfg code has, with a single start and exit
      internalState: State
        # Captures:
        # - all last reads internal to the section,
        #   that means not last reads that occured before
        #   this section and were made last reads because
        #   of a write in this section
        # - All potential last reads this section added
        #   internally, that means not potential last reads
        #   that occured before this section,
        #   and survived in this section
        # - All uses that are definitely not last reads,
        #   internal and external to this section
      hull: TaintTree
        # See comments on TaintTree

    Cache = object
      exits: Table[int, PathCache]
      start, stop: int

  func newState: State =
    State(
      lastReads: HierarchicalSet(root: SetNode(kind: Object)),
      potentialLastReads: HierarchicalSet(root: SetNode(kind: Object)),
      notLastReads: HierarchicalSet(root: SetNode(kind: Object)),
    )

  func copy(s: State): State =
    State(lastReads: copy s.lastReads,
          potentialLastReads: copy s.potentialLastReads,
          notLastReads: copy s.notLastReads)

  func copy(c: PathCache): PathCache =
    PathCache(internalState: copy c.internalState,
              hull: copy c.hull)

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

  func mergePathCaches(cfg: ControlFlowGraph, a: var PathCache, b: sink PathCache) =
    cfg.mergeStates(a.internalState, b.internalState)
    cfg.mergeTaintTrees(a.hull, b.hull)

  var states = newSeq[State](cfg.len + 1)
  states[0] = newState()

  var activeCaches: seq[Cache] # curr loop depth -> Cache
  var pathCaches: seq[seq[PathCache]] # pc -> curr loop depth -> PathCache
  pathCaches.setLen cfg.len + 1
  var finishedCaches: seq[Cache] # cacher.dest -> Cache
  finishedCaches.setLen cfg.len + 1

  for pc in 0..<cfg.len:
    template state: State = states[pc]
    if state != nil:
      dbg:
        echo "pc:",pc
        echo "lastReads:",state.lastReads
        echo "potentialLastReads:",state.potentialLastReads
        echo "notLastReads:",state.notLastReads

      template handleActiveCaches(pc) =
        for i in countdown(activeCaches.len-1, 0):
          if pc notin activeCaches[i].start..<activeCaches[i].stop:
            dbg: echo "XXXXX:  removing cache",pc,"|",activeCaches[i].start,"+",activeCaches[i].stop
            finishedCaches[activeCaches[i].start] = activeCaches[i]
            activeCaches.setLen activeCaches.len - 1
          else:
            # Not leaving the cache, and since caches
            # are nested, not leaving any others either
            break

      template handleCache(dest) =
        for i in countdown(activeCaches.len-1, 0):
          if dest notin activeCaches[i].start..<activeCaches[i].stop:
            activeCaches[i].exits[dest] = copy pathCaches[pc][i]
          else:
            # Not leaving the cache, and since caches
            # are nested, not leaving any others either
            break
        for i in 0..<activeCaches.len:
          if dest in activeCaches[i].start..<activeCaches[i].stop:
            if i in 0..<pathCaches[dest].len:
              cfg.mergePathCaches(pathCaches[dest][i], copy pathCaches[pc][i])
            else:
              pathCaches[dest].add copy pathCaches[pc][i]
          else:
            break
        #dbg: echo "XXXXX:  move ",pathCaches[pc].len," from ",pc," to ",dest," making ",pathCaches[dest].len

      handleActiveCaches(pc)
      assert pathCaches[pc].len == activeCaches.len, $pathCaches[pc].len & "|" & $activeCaches.len
      case cfg[pc].kind
      of def:
        #def:
        #  potentialLastReads.excl:
        #    lastReads.incl:
        #      all definitely aliased by the def loc (exclDefinitelyAliased)
        #    notLastReads.incl:
        #      all that would maybe alias the def loc (exclmaybeAliasing)

        # the path leads to a redefinition of 's' --> sink 's'.
        let newLastReads = state.potentialLastReads.exclDefinitelyAliased(cfg[pc].n)
        state.lastReads.incl newLastReads

        # only partially writes to 's' --> can't sink 's', so this def reads 's'
        # or maybe writes to 's' --> can't sink 's'
        # This "def reads 's'" matters for seq/ref, but if writes access to these
        # is generated as a use s then maybe we could be more greedy here
        # That def would however also excl maybe aliased not only maybe aliasing,
        # so what would ultimately be best is to split the location s from s[].x..s[].y
        # OTOH we cannot move from s[]... anyways since we don't own s[]...
        let newNotLastReads = state.potentialLastReads.exclMaybeAliasing(cfg[pc].n)
        state.notLastReads.incl newNotLastReads

        for i in toIntSet(newNotLastReads):
          cfg[i].n.comment = '\n' & $pc

        # Cache write:
        for i in 0..<pathCaches[pc].len:
          pathCaches[pc][i].hull.taintWrite(cfg[pc].n)
          pathCaches[pc][i].internalState.notLastReads.incl newNotLastReads
          pathCaches[pc][i].internalState.lastReads.incl newLastReads

        let dest = pc + 1
        handleCache(dest)
        cfg.mergeStates(states[dest], move state)
      of use:
        #use:
        #  potentialLastReads.excl:
        #    notLastReads.incl:
        #      all maybe aliased by the use loc (exclMaybeAliased)
        #      all that would maybe alias the use loc (exclmaybeAliasing)
        #  potentialLastReads.incl:
        #    the use loc

        var newNotLastReads = state.potentialLastReads.exclMaybeAliased(cfg[pc].n)
        newNotLastReads.incl state.potentialLastReads.exclMaybeAliasing(cfg[pc].n)

        state.notLastReads.incl newNotLastReads

        for i in toIntSet(newNotLastReads):
          cfg[i].n.comment = '\n' & $pc

        state.potentialLastReads.incl(cfg[pc].n, pc)

        # Cache read:
        for i in 0..<pathCaches[pc].len:
          pathCaches[pc][i].hull.taintRead(cfg[pc].n)
          pathCaches[pc][i].internalState.notLastReads.incl newNotLastReads
          pathCaches[pc][i].internalState.potentialLastReads.incl(cfg[pc].n, pc)

        let dest = pc + 1
        handleCache(dest)
        cfg.mergeStates(states[dest], move state)
      of goto:
        let dest = pc + cfg[pc].dest
        handleCache(dest)
        cfg.mergeStates(states[dest], move state)
      of fork:
        let destA = pc + cfg[pc].dest
        let destB = pc + 1
        handleCache(destA)
        handleCache(destB)
        cfg.mergeStates(states[destA], copy state)
        cfg.mergeStates(states[destB], move state)
      of cachew:
        dbg: echo "Adding cache: ",pc,"..",pc + cfg[pc].dest
        activeCaches.add Cache(start: pc, stop: pc + cfg[pc].dest)
        pathCaches[pc].add PathCache(
          internalState: newState(),
          hull: TaintTree(readRoot: TaintNode(), writeRoot: TaintNode()))
        let dest = pc + 1
        handleCache(dest)
        cfg.mergeStates(states[dest], move state)
      of cacher:
        doAssert finishedCaches[cfg[pc].dest].start == cfg[pc].dest
        dbg: echo "Applying cache at ",pc," from ",cfg[pc].dest

        for exit, pathCache in finishedCaches[cfg[pc].dest].exits:
          dbg: echo "Applying pathCache to ",exit,":",pathCache.hull
          depthFirstTraversal(pathCache.hull,
            proc (r, w: TaintNode, path: seq[NodeKey]) =
              if w != nil and w.data:
                let newLastReads = state.potentialLastReads.exclDefinitelyAliased(path)
                state.lastReads.incl newLastReads

              var newNotLastReads = state.potentialLastReads.exclMaybeAliasing(path)
              if r != nil and r.data:
                newNotLastReads.incl state.potentialLastReads.exclMaybeAliased(path)
                state.notLastReads.incl newNotLastReads
          )
          cfg.mergeStates(states[exit], copy(pathCache.internalState))

        let dest = pc + 1
        handleCache(dest)
        cfg.mergeStates(states[dest], move state)

  let lastReads = (states[^1].lastReads.toIntSet + states[^1].potentialLastReads.toIntSet) -
                   states[^1].notLastReads.toIntSet
  for position in lastReads:
    cfg[position].n.flags.incl nfLastRead


proc hash(n: PNode): Hash = hash(cast[pointer](n))

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

  var states = newSeq[State](cfg.len + 1)
  states[0] = State()

  #HACK:
  var inLoopUntil = -1

  for pc in 0..<cfg.len:
    template state: State = states[pc]
    if state != nil:
      case cfg[pc].kind
      of def:
        block firstTime:
          block alreadySeen:
            for s in state.alreadySeen:
              if aliases(cfg[pc].n, s) != no or
                 aliases(s, cfg[pc].n) != no:
                break alreadySeen
            if pc > inLoopUntil:
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
      of cachew:
        inLoopUntil = max(inLoopUntil, pc + cfg[pc].dest)
        cfg.mergeStates(states[pc + 1], move(states[pc]))
      of cacher: # NYI
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

