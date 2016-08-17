type token =
  | IDENTIFIER of (string)
  [@@deriving eq, ord, show]
