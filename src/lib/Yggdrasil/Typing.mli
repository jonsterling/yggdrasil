module S = Syntax

module Ctx : sig
  type t [@@deriving (eq, ord)]
  val empty : t
  val push : t -> S.Scope.Term.t -> t
  val arity : t -> S.Name.Term.t -> S.Frame.t
end

module Chk : sig
  module Face : sig
    val arity : Computad.t -> Ctx.t -> S.Face.t -> S.Frame.t -> unit
  end
end
module Inf : sig
  module Face : sig
    val arity : Computad.t -> Ctx.t -> S.Face.t -> S.Frame.t
    val subtract : Computad.t -> Ctx.t -> S.Niche.t -> S.Complex.t -> S.Niche.t
  end
  module Term : sig
    val arity : Computad.t -> Ctx.t -> S.Term.t -> S.Frame.t
  end
end
