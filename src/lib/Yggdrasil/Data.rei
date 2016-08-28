let module Rose: {
  open Cats;

  let module Def: {
    include module type Def.Cofree.Make Def.Functor.List;
    include Sig.COMONAD with module T := T;
    include Sig.FOLDABLE with module T := T;
    include Sig.MONAD with module T := T;
    include Sig.TRAVERSABLE with module T := T;
  };

  include module type Def;
  include module type Ext.Apply.Make Def;
  include module type Ext.Bind.Make Def;
  include module type Ext.Comonad.Make Def;
  include module type Ext.Extend.Make Def;
  include module type Ext.Foldable.Make Def;
  include module type Ext.Functor.Make Def;
  include module type Ext.Monad.Make Def;
  include module type Ext.Traversable.Make Def;

  let equal: ('a => 'a => bool) => t 'a => t 'a => bool;
  let compare: ('a => 'a => int) => t 'a => t 'a => int;
  let pp: (Format.formatter => 'a => unit) => Format.formatter => t 'a => unit;
  let show: (Format.formatter => 'a => unit) => t 'a => string;

  let module Bouquet: {
    type nonrec t 'a = list (t 'a) [@@deriving (eq, ord, show)];
  };

  let module Lenses: {
    open Optics;
    let head: Lens.t (t 'a) 'a;
    let tail: Lens.t (t 'a) (list (t 'a));
  };

  let module Prisms: {
    open Optics;
    let nil: PrismP.t (list 'a) (list 'a) unit 'b;
    let cons: Prism.t (list 'a) ('a, list 'a);
  };
};
