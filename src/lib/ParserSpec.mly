%{
[@@@warning "-9"]
%}

%parameter<M : Cats.Sig.MONAD>

%token EOF
%token <string> IDENTIFIER
%token KEYWORD_ANALYZE
%token KEYWORD_CELL
%token KEYWORD_COMPUTAD
%token KEYWORD_FUN
%token KEYWORD_NORMALIZE
%token KEYWORD_SIGN
%token KEYWORD_STAR
%token LEFT_PARENTHESIS
%token LEFT_SQUARE_BRACKET
%token RIGHT_PARENTHESIS
%token RIGHT_SQUARE_BRACKET

%type <Syntax.Term.t> application
%type <Syntax.Term.t Syntax.Spine.t> arity_dom
%type <Syntax.Term.t> arity_cod
%type <Syntax.Arity.t> arity
%type <Syntax.Operator.t> operator
%type <Syntax.Term.t Syntax.Spine.t> spine
%type <Syntax.Term.t> term

%start <Computad.t M.T.el> computad

%%

arity_dom:
  | LEFT_SQUARE_BRACKET
  ; dom = list(term)
  ; RIGHT_SQUARE_BRACKET
{
  dom
}
  | dom = term
{
  dom :: []
}
  ;

arity_cod:
  | KEYWORD_STAR
{
  Syntax.Term.op "*"
}
  | tm = term
{
  tm
}
  ;

arity:
  | LEFT_PARENTHESIS
  ; KEYWORD_FUN
  ; dom = arity_dom
  ; cod = arity_cod
  ; RIGHT_PARENTHESIS
{
  let open Syntax.Arity in
  { dom; cod }
}
  | cod = arity_cod
{
  let open Syntax.Arity in
  { dom = []; cod }
}
  ;

cell:
  | LEFT_PARENTHESIS
  ; KEYWORD_CELL
  ; op = IDENTIFIER
  ; ar = arity
  ; RIGHT_PARENTHESIS
{
  fun (gamma, i) ->
    let open Syntax.Cell in
    let gamma = Computad.bind gamma i { op; ar } in
    (gamma, i)
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
  let (gamma, _) = List.fold_left (fun ctx f -> f ctx) (Computad.init, 0) items in
  M.pure gamma
}
  ;

computad_item:
  | sign = sign
{
  sign
}
  | LEFT_PARENTHESIS
  ; KEYWORD_ANALYZE
  ; term = term
  ; RIGHT_PARENTHESIS
{
  fun (gamma, i) ->
    let open Format in
    let arity = Checker.term_infer_infer gamma term in
    let value = Computad.normTm gamma term in
    fprintf std_formatter "@[<v>@[<hv>input:@ %a@]@,@[arity:@ %a@]@,@[value:@ %a@]@,@.@]"
      Syntax.Term.pp term
      Syntax.Arity.pp arity
      Syntax.Term.pp value;
    (gamma, i)
}
  | LEFT_PARENTHESIS
  ; KEYWORD_NORMALIZE
  ; term = term
  ; RIGHT_PARENTHESIS
{
  fun (gamma, i) ->
    let open Format in
    let norm = Computad.normTm gamma term in
    fprintf std_formatter "@[<v>@[<hv>input:@ %a@]@,@[norm:@ %a@]@,@.@]"
      Syntax.Term.pp term
      Syntax.Term.pp norm;
    (gamma, i)
}
  ;

application:
  | op = operator
{
  Syntax.Term.Ap { op; sp = [] }
}
  | LEFT_PARENTHESIS
  ; op = operator
  ; sp = spine
  ; RIGHT_PARENTHESIS
{
  Syntax.Term.Ap { op; sp }
}
  ;

operator:
  | op = IDENTIFIER
{
  op
}
  ;

sign:
  | LEFT_PARENTHESIS
  ; KEYWORD_SIGN
  ; IDENTIFIER
  ; cells = list(cell)
  ; RIGHT_PARENTHESIS
{
  fun (gamma, i) ->
    let (gamma, i) = List.fold_left (fun ctx f -> f ctx) (gamma, i) cells in
    (gamma, i + 1)
}
  ;

spine:
  | sp = nonempty_list(term)
{
  sp
}
  ;

term:
  | tm = application
{
  tm
}
  ;
