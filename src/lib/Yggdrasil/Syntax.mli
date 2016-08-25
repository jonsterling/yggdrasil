module Term : sig
  open Format

  module Dimension : sig
    type t = int
    [@@deriving eq, ord, show]
  end

  module Operator : sig
    type t = string
    [@@deriving eq, ord, show]
  end

  module Var : sig
    type t = string
    [@@deriving eq, ord, show]
  end

  module rec Bind : sig
    type t = Var.t * Rose.t
    [@@deriving eq, ord, show]
  end

  and Node : sig
    type t =
      | Ap of Rose.t
      | Lm of Bind.t list * t
      | Op of Operator.t
      | Var of Var.t
    [@@deriving eq, ord]
    val pp : Dimension.t -> formatter -> t -> unit
    val show : Dimension.t -> t -> string
    val node : (formatter -> Rose.t -> unit) -> (formatter -> Node.t -> unit)
    val ap : Node.t -> Bouquet.t -> t
    val op : Operator.t -> t
  end

  and Rose : sig
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord]
    val pp : Dimension.t -> formatter -> t -> unit
    val show : Dimension.t -> t -> string
    val ap : Rose.t -> Bouquet.t -> Rose.t
    val op : Operator.t -> Bouquet.t -> Rose.t
  end

  and Bouquet : sig
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord]
  end

  module Arity : sig
    val pp : Dimension.t -> formatter -> Rose.t -> unit
    val pt : Node.t -> Rose.t
    val show : Dimension.t -> Rose.t -> string
  end

  module Cell : sig
    type t = {
      name : Operator.t;
      arity : Rose.t;
    } [@@deriving eq, ord]
  end

  val ( *@ ) : Node.t -> Bouquet.t -> Node.t
  val ( --> ) : Bouquet.t -> Node.t -> Rose.t
  val ( <: ) : Operator.t -> Rose.t -> Cell.t
  val ( <! ) : Operator.t -> Node.t -> Cell.t
end
