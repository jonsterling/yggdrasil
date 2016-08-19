module Rose : sig
  open Cats

  module Def : sig
    include module type of Def.Cofree.Make(Def.Functor.List)
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

  val equal : ('a -> 'a -> bool) -> ('a t -> 'a t -> bool)
  val compare : ('a -> 'a -> int) -> ('a t -> 'a t -> int)
  val pp : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'a t -> unit)
  val show : (Format.formatter -> 'a -> unit) -> ('a t -> string)

  module Bouquet : sig
    type nonrec 'a t = 'a t list
    [@@deriving eq, ord, show]
  end

  module Lenses : sig
    open Optics
    val head : ('a t, 'a) Optics.Lens.t
    val tail : ('a t, 'a t list) Lens.t
  end

  module Prisms : sig
    open Optics
    val nil : ('a list, 'a list, unit, 'b) PrismP.t
    val cons : ('a list, 'a * 'a list) Prism.t
  end
end
