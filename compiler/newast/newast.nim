#
#
#           The Nim Compiler
#        (c) Copyright 2021 Saem Ghani
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module is the new ast, it's an attempt to migrate the compiler towards
## a set of lowerings.
##
## Naming Conventions:
## * `legacy` related to bridging from old AST to the new one

from ".." / ast import PNode, safeLen

type
  ModuleAst* = object
    ## AST for an module
    id: ModuleId
    ast: Ast
    tokens: TokenList

  Ast* = object
    ## AST of some source code fragment or possibly entire module
    nodes: seq[AstNode]

  AstNode* = object
    ## An AST node in the most generous sense, it does two things:
    ## 1. overlay a tree structure upon sequentially stored nodes
    ## 2. stores indices for lookup into auxiliary information structures
    kind: AstNodeKind
      ## AST node this represents, mostly follows the written language grammar.
      ## Exceptions are made for data compactness, see: `AstNodeKind`
    token: TokenIndex
      ## `token` is used to lookup the corresponding `PNode` that was
      ## originally parsed.
      ## xxx: meant to be a temporary, replace with an index into a TokenList
      ##      representing the output of tokenizing source code
    left: AstLeft
      ## interpretation depends upon `kind`, typically this is an index for
      ## looking up the left child index in the list of `AstNode`.
    right: AstRight
      ## interpretation depends upon `kind`, typically this is an index for
      ## looking up the right child index in the list of `AstNode`.

  TokenList* = object
    ## list of tokens, typically for an entire module or fragment of code
    list: seq[Token]

  Token* = object
    ## xxx: should be a single token in a token list from the tokenization.
    ##      Presently, shims info between the old `ast.TNode` and the new AST.
    node: PNode

  AstNodeKind* {.pure.} = enum
    ## discriminant for different types of AST nodes, see `AstNode`
    ankEmpty
  
  TokenIndex* = distinct int32
    ## used to point to a token from the token list
  AstIndex* = distinct int32
    ## used to point to additional information for an AST node
  AstLeft* = distinct uint32
    ## might be an `AstIndex`, an int value, or interpretted some other way
    ## based on the `AstNode.kind`
  AstRight* = distinct uint32
    ## might be an `AstIndex`, an int value, or interpretted some other way
    ## based on the `AstNode.kind`
  ModuleId* = int32
    ## id for this module within a compilation
    ## XXX: refactor along with `ModuleAst` as this is mostly to shim with the
    ##      existing compiler instead of properly handling module vs module in
    ##      a package vs during a specific compilation.

const assumedAstLen: Natural = 100

proc initAst(hintAstLen = assumedAstLen): Ast =
  ## initialize an `Ast`, pre-allocate storage based on the `hintAstLen`
  Ast(nodes: newSeqOfCap[AstNode](hintAstLen))

proc initTokenList(hintListLen = assumedAstLen): TokenList =
  ## initialize a `TokenList`, pre-allocate storage based on the 'hintListLen`
  TokenList(list: newSeqOfCap[Token](hintListLen))

proc initModuleAst*(id: ModuleId, hintAstLen = assumedAstLen): ModuleAst =
  ## initialize a ModuleAst, pre-allocate storage based on the `hintAstLen` to
  ## excessive allocations/moves.
  ModuleAst(
    id:     id,
    ast:    initAst(hintAstLen),
    tokens: initTokenList(hintAstLen)
  )

proc legacyInitModuleAst*(id: int): ModuleAst =
  ## creates `ModuleAst` with the legacy `id` of the module, in order to keep
  ## it in sync with the legacy `ModuleGraph`.
  initModuleAst(ModuleId id)

proc legacyAdd(tokens: var TokenList, n: PNode): TokenIndex =
  ## add this `PNode` from the parser to the list of tokens (yess very weird)
  ## and return the `TokenIndex` corresponding to the fresh token.
  tokens.list.add Token(node: n)
  result = TokenIndex(tokens.list.len - 1)

func legacyNodeToAstKind(n: PNode): AstNodeKind =
  let
    kind = n.kind
    childCount = n.safeLen
  
  result = ankEmpty

proc legacyAppendPNode*(m: var ModuleAst; n: PNode) =
  ## take `n` the `PNode`, from parsing, and append it to `m` the `ModuleAst`.
  let
    kind = legacyNodeToAstKind(n)
    token = m.tokens.legacyAdd(n)

  # xxx: implement left and right properly, see below

  m.ast.nodes.add AstNode(
    kind: kind,
    token: token,
    left: AstLeft 1,
    right: AstRight 2
  )