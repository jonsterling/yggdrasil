%{
[@@@warning "-9"]
%}

%parameter<M : Cats.Sig.MONAD>

%token EOF
%token <string> IDENTIFIER

%start <string list M.T.el> main

%%

main:
  | mds = identifiers EOF
{ mds }
  ;

identifier:
  | id = IDENTIFIER
{ M.pure id }
  ;

identifiers:
  |
{ M.pure [] }
  | mid  = identifier
  ; mids = identifiers
{ M.bind mid  @@ fun id  ->
  M.bind mids @@ fun ids ->
  M.pure @@ id::ids }
  ;
