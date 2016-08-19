module Make (Sigma : Computad.S) : sig
  open Syntax
  include Computad.S with type t = Sigma.t
  module Inf : sig
    module Node : sig
      val arity : Sigma.t -> Term.Node.t -> Term.Rose.t
      val subtract : Sigma.t -> Term.Bouquet.t -> Term.Bouquet.t -> Term.Bouquet.t
    end
    module Rose : sig
      val arity : Sigma.t -> Term.Rose.t -> Term.Rose.t
    end
  end
  module Chk : sig
    module Node : sig
      val arity : Sigma.t -> Term.Node.t -> Term.Rose.t -> unit
    end
  end
end
