open Data
open Format

module Dimension : sig
  type t = int [@@deriving (eq, ord, show)]
end

module Name : sig
  module Meta : sig
    type t = string [@@deriving (eq, ord, show)]
  end
  module Oper : sig
    type t = string [@@deriving (eq, ord, show)]
  end
  module Term : sig
    type t = string [@@deriving (eq, ord, show)]
  end
  type t =
    | Meta of Meta.t
    | Oper of Oper.t
    | Term of Term.t
  [@@deriving (eq, ord, show)]
end

module rec Bind : sig
  module Meta : sig
    type t = (Name.Meta.t * Frame.t) [@@deriving (eq, ord, show)]
  end
  module Term : sig
    type t = (Name.Term.t * Frame.t) [@@deriving (eq, ord, show)]
  end
end

and Complex: sig
  type t = Node.t Rose.Corolla.t [@@deriving (eq, ord)]
end

and Face : sig
  type t =
    | Rho of Term.t
    | Abs of Scope.Meta.t * Scope.Term.t * t
    | Var of Name.t
  [@@deriving (eq, ord)]
  val pp : Dimension.t -> formatter -> t -> unit
  val pp_node : (formatter -> Term.t -> unit) -> formatter -> t -> unit
  val show : Dimension.t -> t -> string
  val ap : Face.t -> Complex.t -> t
  val op : Name.Oper.t -> t
end

and Frame : sig
  type t = Term.t [@@deriving (eq, ord)]
  val pp : Dimension.t -> formatter -> t -> unit
  val show : Dimension.t -> t -> string
  val point : Face.t -> t
end

and Niche : sig
  type t = Complex.t [@@deriving (eq, ord)]
end

and Node : sig
  type t = Face.t
end

and Scope : sig
  module Meta : sig type t = Bind.Meta.t list [@@deriving (eq, ord)] end
  module Term : sig type t = Bind.Term.t list [@@deriving (eq, ord)] end
end

and Term : sig
  type t = Node.t Rose.t [@@deriving (eq, ord)]
  val pp : Dimension.t -> formatter -> t -> unit
  val show : Dimension.t -> t -> string
  val ap : t -> Complex.t -> t
  val op : Name.Oper.t -> Complex.t -> t
end

module Cell : sig
  type t = { oname: Name.Oper.t; frame: Frame.t }
end

val ( *@< ) : Face.t -> Complex.t -> Term.t
val ( *@ ) : Face.t -> Complex.t -> Face.t
val ( --> ) : Niche.t -> Face.t -> Frame.t
val ( <: ) : Name.Oper.t -> Frame.t -> Cell.t
val ( <! ) : Name.Oper.t -> Face.t -> Cell.t

module Builtin : sig
  val star : Face.t
end
