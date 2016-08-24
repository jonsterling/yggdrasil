module Term : sig
  module Dimension : sig
    type t = int
    [@@deriving eq, ord, show]
  end

  module Operator : sig
    type t = string
    [@@deriving eq, ord, show]
  end

  module rec Node : sig
    type t =
      | Op of Operator.t
      | Rho of Rose.t
    [@@deriving eq, ord]
    val pp : Dimension.t -> Format.formatter -> t -> unit
    val show : Dimension.t -> t -> string
    val node : (Format.formatter -> Rose.t -> unit) -> (Format.formatter -> Node.t -> unit)
    val op : Operator.t -> t
    val rho : Node.t -> Bouquet.t -> t
  end

  and Rose : sig
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord]
    val pp : Dimension.t -> Format.formatter -> t -> unit
    val show : Dimension.t -> t -> string
    val rho : Rose.t -> Bouquet.t -> Rose.t
    val op : Operator.t -> Bouquet.t -> Rose.t
  end

  and Bouquet : sig
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord]
  end

  module Arity : sig
    val pp : Dimension.t -> Format.formatter -> Rose.t -> unit
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
