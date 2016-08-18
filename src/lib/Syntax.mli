module Dimension : sig
  type t = int
  [@@deriving eq, ord, show]
end
module Operator : sig
  type t = string
  [@@deriving eq, ord, show]
end

module rec Spine : sig
  type t = Term.t list
  [@@deriving eq, ord, show]
end

and Term : sig
  type t =
    | Ap of {
      op : Operator.t;
      sp : Spine.t;
    }
  [@@deriving eq, ord, show]
  val ( *@ ) : Operator.t -> Spine.t -> t
  val ap : Operator.t -> Spine.t -> t
  val op : Operator.t -> t
end

module Arity : sig
  type t = {
    dom : t list;
    cod : Term.t;
  } [@@deriving eq, ord, show]
  val ( --> ) : t list -> Term.t -> t
  val pt : Term.t -> t
end

module Cell : sig
  type t = {
    op : Operator.t;
    ar : Arity.t;
  } [@@deriving eq, ord, show]
  val source : t -> Arity.t list
  val target : t -> Term.t
  val ( <: ) : Operator.t -> Arity.t -> t
  val ( <! ) : Operator.t -> Term.t -> t
end
