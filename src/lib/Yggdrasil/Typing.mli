module Make (Sigma : Computad.S) : sig
  open Syntax
  include Computad.S with type t = Sigma.t

  module Ctx : sig
    type t
    [@@deriving eq, ord]
    val init : t
    val push : t -> Term.Bind.t list -> t
    val arity : t -> Term.Var.t -> Term.Rose.t
  end

  module Inf : sig
    module Node : sig
      val arity : Sigma.t -> Ctx.t -> Term.Node.t -> Term.Rose.t
      val subtract : Sigma.t -> Ctx.t -> Term.Bouquet.t -> Term.Bouquet.t -> Term.Bouquet.t
    end
    module Rose : sig
      val arity : Sigma.t -> Ctx.t -> Term.Rose.t -> Term.Rose.t
    end
  end
  module Chk : sig
    module Node : sig
      val arity : Sigma.t -> Ctx.t -> Term.Node.t -> Term.Rose.t -> unit
    end
  end
end
