%{
[@@@warning "-9"]
open Syntax.Term
open Arity
open Format

module Ctx = CCSet.Make(struct
  type t = Operator.t
  let compare = compare
end)
%}

%parameter<M : Cats.Sig.MONAD>

%token EOF
%token <string> IDENTIFIER
%token KEYWORD_ANALYZE
%token KEYWORD_ARITY
%token KEYWORD_CELL
%token KEYWORD_COMPUTAD
%token KEYWORD_LAMBDA
%token KEYWORD_SIGN
%token KEYWORD_TYPE
%token LEFT_PARENTHESIS
%token LEFT_SQUARE_BRACKET
%token RIGHT_PARENTHESIS
%token RIGHT_SQUARE_BRACKET

%type <Rose.t> arity
%type <Bouquet.t> arity_dom
%type <Node.t> arity_cod
%type <(Variable.t * Rose.t)> bind
%type <(Variable.t * Rose.t) list> binds
%type <Computad.t * Dimension.t -> Computad.t * Dimension.t> cell
%type <Computad.t * Dimension.t -> Computad.t * Dimension.t> computad_item
%type <Ctx.t -> Node.t> node
%type <Ctx.t -> Node.t> node_parens
%type <Ctx.t -> Node.t> operator_or_variable
%type <Ctx.t -> Rose.t> rose
%type <Ctx.t -> Rose.t> rose_parens
%type <Computad.t * Dimension.t -> Computad.t * Dimension.t> sign

%start <Computad.t M.T.el> computad

%%

arity:
  | LEFT_PARENTHESIS
  ; KEYWORD_ARITY
  ; dom = arity_dom
  ; cod = arity_cod
  ; RIGHT_PARENTHESIS
{ dom --> cod }
  | cod = arity_cod
{ pt cod }
  ;

arity_dom:
  | LEFT_SQUARE_BRACKET
  ; dom = list(arity)
  ; RIGHT_SQUARE_BRACKET
{ dom }
  | dom = rose
{ dom Ctx.empty :: [] }
  ;

arity_cod:
  | KEYWORD_TYPE
{ Builtin.star }
  | cod = node
{ cod Ctx.empty }
  ;

bind:
  | LEFT_PARENTHESIS
  ; KEYWORD_CELL
  ; op = IDENTIFIER
  ; ar = arity
  ; RIGHT_PARENTHESIS
{ (op, ar) }
  ;

binds:
  | bind = bind
{ bind :: [] }
  | LEFT_SQUARE_BRACKET
  ; binds = list(bind)
  ; RIGHT_SQUARE_BRACKET
{ binds }
  ;

cell:
  | LEFT_PARENTHESIS
  ; KEYWORD_CELL
  ; op = IDENTIFIER
  ; ar = arity
  ; RIGHT_PARENTHESIS
{
  fun (sigma, i) ->
    let sigma = Computad.bind sigma i (op <: ar) in
    (sigma, i)
}
  ;

computad:
  | LEFT_PARENTHESIS
  ; KEYWORD_COMPUTAD
  ; IDENTIFIER
  ; items = list(computad_item)
  ; RIGHT_PARENTHESIS
  ; EOF
{
  let (sigma, _) = List.fold_left (|>) (Computad.empty, 0) items in
  M.pure sigma
}
  ;

computad_item:
  | sign = sign
{ sign }
  | LEFT_PARENTHESIS
  ; KEYWORD_ANALYZE
  ; node = node
  ; RIGHT_PARENTHESIS
{
  fun sigma ->
    let module T = Typing in
    let dim = 2 in
    let node = node Ctx.empty in
    let rose = T.Inf.Node.arity (fst sigma) T.Ctx.empty node in
    let () =
      fprintf std_formatter "@.@[<v>@[<hv 2>term:@ %a@]@,@[<hv 2>type:@ %a@]@,@]"
        (Node.pp dim) node
        (Arity.pp dim) rose
    ; pp_print_flush std_formatter () in
    sigma
}
  ;

node:
  | node = operator_or_variable
{ node }
  | LEFT_PARENTHESIS
  ; node = node_parens
  ; RIGHT_PARENTHESIS
{ node }
  ;

node_parens:
  | KEYWORD_LAMBDA
  ; binds = binds
  ; body = node
{
  fun gamma ->
    let gamma = Ctx.union gamma @@ Ctx.of_list @@ CCList.map fst binds in
    Node.Lm (binds, body gamma)
}
  | node = operator_or_variable
  ; spine = nonempty_list(rose)
{ fun gamma -> node gamma *@ CCList.map ((|>) gamma) spine }
  ;

operator_or_variable:
  | id = IDENTIFIER
{ fun gamma -> if Ctx.mem id gamma then Node.Var id else Node.Op id }
  ;

rose:
  | node = operator_or_variable
{ fun gamma -> [] --> node gamma }
  | LEFT_PARENTHESIS
  ; rose = rose_parens
  ; RIGHT_PARENTHESIS
{ rose }
  ;

rose_parens:
  | KEYWORD_LAMBDA
  ; binds = binds
  ; body = node
{
  fun gamma ->
    let gamma = Ctx.union gamma @@ Ctx.of_list @@ CCList.map fst binds in
    [] --> Node.Lm (binds, body gamma)
}
  | node = operator_or_variable
  ; spine = nonempty_list(rose)
{ fun gamma -> CCList.map ((|>) gamma) spine --> node gamma }
  ;

sign:
  | LEFT_PARENTHESIS
  ; KEYWORD_SIGN
  ; IDENTIFIER
  ; cells = list(cell)
  ; RIGHT_PARENTHESIS
{
  fun (sigma, i) ->
    let (sigma, i) = List.fold_left (|>) (sigma, i) cells in
    (sigma, i + 1)
}
  ;
