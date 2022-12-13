import
  std/[
    tables,
    hashes
  ],
  compiler/ast/[
    ast,
  ],
  compiler/sem/dfa/cfg

type
  NodeKeyKind* = enum
    field, constant, variable
  NodeKey* = object
    case kind*: NodeKeyKind
    of field:
      field*: PSym
    of constant:
      constant*: BiggestInt
    of variable:
      variable*: PSym
  NodeKind* = enum
    Leaf
    Object
    Array
    Infinite
  Node*[T] = ref object
    # we need a way to differentiate
    # between a node simply serving as a path to a
    # subnode, or being a node itself. For now we
    # just check if instructions is empty.
    # This is a set because the same location
    # could be read in different instructions
    data*: T
    kind*: NodeKind
    fields*: Table[PSym, Node[T]]
    constants*: Table[BiggestInt, Node[T]]
    variables*: Table[PSym, Node[T]]

proc hash*(s: PSym): Hash = hash(cast[pointer](s))

proc typeOfNode*(n: PNode): PType =
  const skipped = {tyAlias, tyDistinct, tyGenericInst,
    tyRef, tyPtr, tyVar, tySink, tyLent, tyOwned}
  result = n.typ.skipTypes(skipped)
  # HACK: sometimes typ is tyUntyped, in that case we try to get the sym typ instead
  if result.kind == tyUntyped and n.kind == nkSym:
    result = n.sym.typ.skipTypes(skipped)

func collectImportantNodes*(n: PNode): seq[PNode] =
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

func nodesToPath*(importantNodes: seq[PNode]): seq[NodeKey] =
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

proc `$`*(k: NodeKey): string =
  case k.kind
  of field:
    $k.field
  of constant:
    $k.constant
  of variable:
    "var:" & $k.variable

