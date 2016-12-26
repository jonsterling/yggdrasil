open Format

type token =
  | EOF
  | IDENTIFIER of string
  | KEYWORD_ANALYZE
  | KEYWORD_ARITY
  | KEYWORD_CELL
  | KEYWORD_COMPUTAD
  | KEYWORD_LAMBDA
  | KEYWORD_SIGN
  | KEYWORD_TYPE
  | LEFT_PARENTHESIS
  | LEFT_SQUARE_BRACKET
  | RIGHT_PARENTHESIS
  | RIGHT_SQUARE_BRACKET
[@@deriving (eq, ord, show)]

module Pretty = struct
  let pp fmt = function
    | EOF ->
      fprintf fmt "@\n"
    | IDENTIFIER id ->
      fprintf fmt "%a" (Fmt.string) id
    | KEYWORD_ANALYZE ->
      fprintf fmt "%a" (Fmt.string) "@@analyze"
    | KEYWORD_ARITY ->
      fprintf fmt "%a" (Fmt.string) "->"
    | KEYWORD_CELL ->
      fprintf fmt "%a" (Fmt.string) "cell"
    | KEYWORD_COMPUTAD ->
      fprintf fmt "%a" (Fmt.string) "computad"
    | KEYWORD_LAMBDA ->
      fprintf fmt "%a" (Fmt.string) "lambda"
    | KEYWORD_SIGN ->
      fprintf fmt "%a" (Fmt.string) "sign"
    | KEYWORD_TYPE ->
      fprintf fmt "%a" (Fmt.string) "type"
    | LEFT_PARENTHESIS ->
      fprintf fmt "%a" (Fmt.string) "("
    | LEFT_SQUARE_BRACKET ->
      fprintf fmt "%a" (Fmt.string) "["
    | RIGHT_PARENTHESIS ->
      fprintf fmt "%a" (Fmt.string) ")"
    | RIGHT_SQUARE_BRACKET ->
      fprintf fmt "%a" (Fmt.string) "]"

  let pp_utf_8 fmt = function
    | EOF ->
      fprintf fmt "@\n"
    | IDENTIFIER id ->
      fprintf fmt "%a" (Uuseg_string.pp_utf_8) id
    | KEYWORD_ANALYZE ->
      fprintf fmt "%a" (Fmt.string) "@@analyze"
    | KEYWORD_ARITY ->
      fprintf fmt "%a" (Uuseg_string.pp_utf_8) "→"
    | KEYWORD_CELL ->
      fprintf fmt "%a" (Uuseg_string.pp_utf_8) "∂"
    | KEYWORD_COMPUTAD ->
      fprintf fmt "%a" (Fmt.string) "computad"
    | KEYWORD_LAMBDA ->
      fprintf fmt "%a" (Uuseg_string.pp_utf_8) "λ"
    | KEYWORD_SIGN ->
      fprintf fmt "%a" (Fmt.string) "sign"
    | KEYWORD_TYPE ->
      fprintf fmt "%a" (Fmt.string) "type"
    | LEFT_PARENTHESIS ->
      fprintf fmt "%a" (Fmt.string) "("
    | LEFT_SQUARE_BRACKET ->
      fprintf fmt "%a" (Fmt.string) "["
    | RIGHT_PARENTHESIS ->
      fprintf fmt "%a" (Fmt.string) ")"
    | RIGHT_SQUARE_BRACKET ->
      fprintf fmt "%a" (Fmt.string) "]"
end
