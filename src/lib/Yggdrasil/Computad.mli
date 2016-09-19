open Syntax

module type Sig = sig
  type t [@@deriving show]
  val empty : t
  val bind : t -> Dimension.t -> Cell.t -> t
  val arity : t -> Name.Oper.t -> Frame.t
end

include Sig
