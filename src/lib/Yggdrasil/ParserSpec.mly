%{
[@@@warning "-9"]
open Format
open Syntax
module R = Data.Rose

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

%type <Frame.t> frame
%type <Niche.t> frame_niche
%type <Face.t> frame_face
%type <Bind.Term.t> bind
%type <Telescope.Term.t> telescope
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

frame:
  | LEFT_PARENTHESIS
  ; KEYWORD_ARITY
  ; niche = frame_niche
  ; face = frame_face
  ; RIGHT_PARENTHESIS
{
  let tele = [] in
  let scoped = { Scoped.tele; face } in
  R.Fork (scoped, niche)
}
  | face = frame_face
{
  Frame.point face
}
  ;

frame_niche:
  | LEFT_SQUARE_BRACKET
  ; niche = list(frame)
  ; RIGHT_SQUARE_BRACKET
{
  niche
}
  | frame = frame
{
  frame :: []
}
  ;

frame_face:
  | KEYWORD_TYPE
{
  Builtin.star
}
  | face = face
{
  face Ctx.empty
}
  ;

bind:
  | LEFT_PARENTHESIS
  ; KEYWORD_CELL
  ; var = IDENTIFIER
  ; frame = frame
  ; RIGHT_PARENTHESIS
{
  (var, frame)
}
  ;

telescope:
  | bind = bind
{
  bind :: []
}
  | LEFT_SQUARE_BRACKET
  ; telescope = list(bind)
  ; RIGHT_SQUARE_BRACKET
{
  telescope
}
  ;

cell:
  | LEFT_PARENTHESIS
  ; KEYWORD_CELL
  ; op = IDENTIFIER
  ; frame = frame
  ; RIGHT_PARENTHESIS
{
  fun (sigma, i) ->
    let sigma = Computad.bind sigma i (op <: frame) in
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
{
  sign
}
  | LEFT_PARENTHESIS
  ; KEYWORD_ANALYZE
  ; face = face
  ; RIGHT_PARENTHESIS
{
  fun sigma ->
    let module T = Typing in
    let dim = 2 in
    let face = face Ctx.empty in
    let frame = T.Inf.Face.arity (fst sigma) T.Ctx.empty face in
    let () =
      fprintf std_formatter "@.@[<v>@[<hv 2>term:@ %a@]@,@[<hv 2>type:@ %a@]@,@]"
        (Face.pp dim) face
        (Frame.pp dim) frame
    ; pp_print_flush std_formatter () in
    sigma
}
  ;

face:
  | face = operator_or_variable
{
  face
}
  | LEFT_PARENTHESIS
  ; face = face_parens
  ; RIGHT_PARENTHESIS
{
  face
}
  ;

face_parens:
  | KEYWORD_LAMBDA
  ; tele = telescope
  ; face = face
{
  fun gamma ->
    let gamma = Ctx.union gamma @@ Ctx.of_list @@ CCList.map fst tele in
    Face.Lm ([], tele, face gamma)
}
  | face = operator_or_variable
  ; complex = nonempty_list(term)
{
  fun gamma ->
    face gamma *@ CCList.map ((|>) gamma) complex
}
  ;

operator_or_variable:
  | id = IDENTIFIER
{
  fun gamma ->
    if Ctx.mem id gamma then
      Face.VarT id
    else
      Face.Op id
}
  ;

term:
  | face = operator_or_variable
{
  fun gamma ->
    let tele = [] in
    let face = face gamma in
    let scoped = { Scoped.tele; face } in
    R.Fork (scoped, [])
}
  | LEFT_PARENTHESIS
  ; term = term_parens
  ; RIGHT_PARENTHESIS
{
  term
}
  ;

term_parens:
  | KEYWORD_LAMBDA
  ; tele = telescope
  ; face = face
{
  fun gamma ->
    let gamma = Ctx.union gamma @@ Ctx.of_list @@ CCList.map fst tele in
    [] --> Face.Lm ([], tele, face gamma)
}
  | face = operator_or_variable
  ; complex = nonempty_list(term)
{
  fun gamma ->
    let tele = [] in
    let face = face gamma in
    let scoped = { Scoped.tele; face } in
    R.Fork (scoped, CCList.map ((|>) gamma) complex)
}
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
