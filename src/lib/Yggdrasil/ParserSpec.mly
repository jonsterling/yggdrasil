%{
[@@@warning "-9"]
open Syntax

module Ctx = CCSet.Make(struct
  type t = Name.Oper.t
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

%type <Frame.t> frame
%type <Bind.Term.t> bind
%type <Scope.Term.t> telescope
%type <Computad.t * Dimension.t -> Computad.t * Dimension.t> cell
%type <Computad.t * Dimension.t -> Computad.t * Dimension.t> computad_item
%type <Ctx.t -> Face.t> face
%type <Ctx.t -> Face.t> face_parens
%type <Ctx.t -> Face.t> operator_or_variable
%type <Ctx.t -> Term.t> term
%type <Ctx.t -> Term.t> term_parens
%type <Computad.t * Dimension.t -> Computad.t * Dimension.t> sign

%start <Computad.t M.T.el> computad

%%

%inline single_or_delimited(LHS, RULE, RHS):
  | result = delimited(LHS, list(RULE), RHS)
{ result }
  | result = RULE
{ result :: [] }
  ;

%inline parens(X):
  | result = delimited(LEFT_PARENTHESIS, X, RIGHT_PARENTHESIS)
{ result }

%inline single_or_squares(X):
  | result = single_or_delimited(LEFT_SQUARE_BRACKET, X, RIGHT_SQUARE_BRACKET)
{ result }

frame:
  | result = parens(pair(preceded(KEYWORD_ARITY, single_or_squares(frame)), face))
{
  let open Data in
  let (niche, face) = result in
  let face = face Ctx.empty in
  let lhs = [] in
  let rhs = niche in
  let diag = { Diag.lhs; rhs } in
  Rose.Fork (face, diag)
}
  | face = face
{ Frame.point @@ face Ctx.empty }
  ;

bind:
  | bind = parens(preceded(KEYWORD_CELL, pair(IDENTIFIER, frame)))
{ bind }
  ;

telescope:
  | tele = single_or_squares(bind)
{ tele }
  ;

cell:
  | result = parens(preceded(KEYWORD_CELL, pair(IDENTIFIER, frame)))
{
  fun (sigma, i) ->
    let (op, frame) = result in
    let sigma = Computad.bind sigma i (op <: frame) in
    (sigma, i)
}
  ;

computad:
  | result = terminated(parens(preceded(KEYWORD_COMPUTAD, pair(IDENTIFIER, list(computad_item)))), EOF)
{
  let (_, items) = result in
  let (sigma, _) = List.fold_left (|>) (Computad.empty, 0) items in
  M.pure sigma
}
  ;

computad_item:
  | sign = sign
{ sign }
  | face = parens(preceded(KEYWORD_ANALYZE, face))
{
  fun sigma ->
    let open Format in
    let module T = Typing in
    let dim = 2 in
    let face = face Ctx.empty in
    let frame = T.Inf.Face.arity (fst sigma) T.Ctx.empty face in
    fprintf std_formatter "@.@[<v>@[<hv 2>term:@ %a@]@,@[<hv 2>type:@ %a@]@,@]"
      (Face.pp dim) face
      (Frame.pp dim) frame
    ; pp_print_flush std_formatter ()
    ; sigma
}
  ;

face:
  | face = operator_or_variable
{ face }
  | KEYWORD_TYPE
{ fun _ -> Builtin.star }
  | face = parens(face_parens)
{ face }
  ;

face_parens:
  | result = preceded(KEYWORD_LAMBDA, pair(telescope, face))
{
  fun gamma ->
    let (tele, face) = result in
    let gamma = Ctx.union gamma @@ Ctx.of_list @@ CCList.map fst tele in
    Face.Abs ([], tele, face gamma)
}
  | result = pair(operator_or_variable, nonempty_list(term))
{
  fun gamma ->
    let (face, complex) = result in
    face gamma *@ CCList.map ((|>) gamma) complex
}
  ;

operator_or_variable:
  | id = IDENTIFIER
{
  fun gamma ->
    if Ctx.mem id gamma then
      Face.Var (Name.Term id)
    else
      Face.Var (Name.Oper id)
}
  ;

term:
  | face = operator_or_variable
{
  fun gamma ->
    let open Data in
    let face = face gamma in
    let lhs = [] in
    let rhs = [] in
    let diag = { Diag.lhs; rhs } in
    Rose.Fork (face, diag)
}
  | term = parens(term_parens)
{ term }
  ;

term_parens:
  | result = preceded(KEYWORD_LAMBDA, pair(telescope, face))
{
  fun gamma ->
    let (tele, face) = result in
    let gamma = Ctx.union gamma @@ Ctx.of_list @@ CCList.map fst tele in
    [] --> Face.Abs ([], tele, face gamma)
}
  | result = pair(operator_or_variable, nonempty_list(term))
{
  fun gamma ->
    let open Data in
    let (face, complex) = result in
    let face = face gamma in
    let lhs = [] in
    let rhs = CCList.map ((|>) gamma) complex in
    let diag = { Diag.lhs; rhs } in
    Rose.Fork (face, diag)
}
  ;

sign:
  | result = parens(preceded(KEYWORD_SIGN, pair(IDENTIFIER, list(cell))))
{
  fun (sigma, i) ->
    let (_, cells) = result in
    let (sigma, i) = List.fold_left (|>) (sigma, i) cells in
    (sigma, i + 1)
}
  ;
