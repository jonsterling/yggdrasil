open Cats
open Format
open Optics

module Diag : sig
  type 'a t = {
    lhs: 'a list;
    rhs: 'a list;
  } [@@deriving (eq, ord, show)]
  module T : sig
    include TyCon.TC1 with type 'a el = 'a t
  end
  module Functor : sig
    module T = T
    include Sig.FUNCTOR with module T := T
  end
  module Traversable : sig
    module T = T
    include Sig.TRAVERSABLE with module T := T
  end
end

module Rose : sig
  module Def : sig
    include module type of Def.Cofree.Make(Diag.Functor)
    include Sig.COMONAD with module T := T
    include Sig.FOLDABLE with module T := T
    include Sig.MONAD with module T := T
    include Sig.TRAVERSABLE with module T := T
  end

  include module type of Def
  include module type of Ext.Apply.Make(Def)
  include module type of Ext.Bind.Make(Def)
  include module type of Ext.Comonad.Make(Def)
  include module type of Ext.Extend.Make(Def)
  include module type of Ext.Foldable.Make(Def)
  include module type of Ext.Functor.Make(Def)
  include module type of Ext.Monad.Make(Def)
  include module type of Ext.Traversable.Make(Def)

  module Corolla : sig
    type nonrec 'a t = ('a t) list
    val equal : ('a -> 'a -> bool) -> ('a t -> 'a t -> bool)
    val compare : ('a -> 'a -> int) -> ('a t -> 'a t -> int)
    val pp : (formatter -> 'a -> unit) -> (formatter -> 'a t -> unit)
    val show : (formatter -> 'a -> unit) -> ('a t -> string)
  end

  val equal : ('a -> 'a -> bool) -> ('a t -> 'a t -> bool)
  val compare : ('a -> 'a -> int) -> ('a t -> 'a t -> int)
  val pp : (formatter -> 'a -> unit) -> (formatter -> 'a t -> unit)
  val show : (formatter -> 'a -> unit) -> ('a t -> string)
end

module List : sig
  module Lenses : sig
    module Rose : sig
      val node : ('a Rose.t, 'a) Lens.t
      val diag : ('a Rose.t, ('a Rose.t) Diag.t) Lens.t
      val lhs : unit -> ('a Rose.t, ('a Rose.t) list) Lens.t
      val rhs : unit -> ('a Rose.t, ('a Rose.t) list) Lens.t
    end
    module Diag : sig
      val lhs : ('a Diag.t, 'a list) Lens.t
      val rhs : ('a Diag.t, 'a list) Lens.t
    end
  end
  module Prisms : sig
    val nil : ('a list , 'a list, unit, 'b) PrismP.t
    val cons : ('a list, ('a * 'a list)) Prism.t
  end
end
