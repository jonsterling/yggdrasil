module Term : sig
  module Dim : sig
    type t = int
    [@@deriving eq, ord, show]
  end

  module Op : sig
    type t = string
    [@@deriving eq, ord, show]
  end

  module rec Node : sig
    type t =
      | Op of Op.t
      | Rho of Rose.t
    [@@deriving eq, ord, show]
    val node : (Format.formatter -> Rose.t -> unit) -> (Format.formatter -> Node.t -> unit)
    val op : Op.t -> t
    val rho : Node.t -> Bouquet.t -> t
  end

  and Rose : sig
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord, show]
    val rho : Rose.t -> Bouquet.t -> Rose.t
    val op : Op.t -> Bouquet.t -> Rose.t
  end

  and Bouquet : sig
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord, show]
  end

  module Arity : sig
    val pp : Format.formatter -> Rose.t -> unit
    val pt : Node.t -> Rose.t
  end

  module Cell : sig
    type t = {
      name : Op.t;
      arity : Rose.t;
    } [@@deriving eq, ord, show]
  end

  val ( *@ ) : Node.t -> Bouquet.t -> Node.t
  val ( --> ) : Bouquet.t -> Node.t -> Rose.t
  val ( <: ) : Op.t -> Rose.t -> Cell.t
  val ( <! ) : Op.t -> Node.t -> Cell.t
end
