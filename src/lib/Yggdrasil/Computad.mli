module type S = sig
  open Syntax.Term
  type t
  [@@deriving show]
  val empty : t
  val bind : t -> Dimension.t -> Cell.t -> t
  val arity : t -> Operator.t -> Rose.t
end

module Std : S
