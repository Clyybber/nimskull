type
  State = ref object
    lastReads: IntSet
    potentialLastReads: IntSet
    notLastReads: IntSet
    alreadySeen: HashSet[PNode]

proc mergeStates(a: var State, b: sink State) =
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

proc computeLastReadsAndFirstWrites*(cfg: ControlFlowGraph) =
  var cache = initTable[(PNode, PNode), AliasKind]()
  template aliasesCached(obj, field: PNode): AliasKind =
    aliasesCached(cache, obj, field)

  var cfg = cfg
  preprocessCfg(cfg)

  var states = newSeq[State](cfg.len + 1)
  states[0] = State()

  for pc in 0..<cfg.len:
    template state: State = states[pc]
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

        mergeStates(states[pc + 1], move(states[pc]))
      of use:
        var potentialLastReadsCopy = state.potentialLastReads
        for r in potentialLastReadsCopy:
          if cfg[pc].n.aliasesCached(cfg[r].n) != no or cfg[r].n.aliasesCached(cfg[pc].n) != no:
            cfg[r].n.comment = '\n' & $pc
            state.potentialLastReads.excl r
            state.notLastReads.incl r

        state.potentialLastReads.incl pc

        state.alreadySeen.incl cfg[pc].n

        mergeStates(states[pc + 1], move(states[pc]))
      of goto:
        mergeStates(states[pc + cfg[pc].dest], move(states[pc]))
      of fork:
        var copy = State()
        copy[] = states[pc][]
        mergeStates(states[pc + cfg[pc].dest], copy)
        mergeStates(states[pc + 1], move(states[pc]))

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

