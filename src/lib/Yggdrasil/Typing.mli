module T = Syntax.Term

module Ctx : sig
  type t
  [@@deriving eq, ord]
  val empty : t
  val push : t -> T.Bind.t list -> t
  val arity : t -> T.Variable.t -> T.Rose.t
end

module Inf : sig
  module Node : sig
    val arity : Computad.t -> Ctx.t -> T.Node.t -> T.Rose.t
    val subtract : Computad.t -> Ctx.t -> T.Bouquet.t -> T.Bouquet.t -> T.Bouquet.t
  end
  module Rose : sig
    val arity : Computad.t -> Ctx.t -> T.Rose.t -> T.Rose.t
  end
end
module Chk : sig
  module Node : sig
    val arity : Computad.t -> Ctx.t -> T.Node.t -> T.Rose.t -> unit
  end
end
