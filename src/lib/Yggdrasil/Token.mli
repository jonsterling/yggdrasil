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

module Pretty : sig
  val pp : token Fmt.t
  val pp_utf_8 : token Fmt.t
end
