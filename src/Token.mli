type token =
  | EOF
  | IDENTIFIER of (string)
  [@@deriving eq, ord, show]
