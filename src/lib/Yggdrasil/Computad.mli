module type S = sig
  open Syntax
  type t
  [@@deriving show]
  val empty : t
  val bind : t -> Term.Dim.t -> Term.Cell.t -> t
  val arity : t -> Term.Op.t -> Term.Rose.t
end

module Std : S
