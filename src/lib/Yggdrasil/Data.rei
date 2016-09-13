open Cats;
open Format;
open Optics;

let module Diag: {
  type t 'a = {
    lhs: list 'a,
    rhs: list 'a,
  } [@@deriving (eq, ord, show)];
  let module T: {
    include TyCon.TC1 with type el 'a = t 'a;
  };
  let module Functor: {
    let module T = T;
    include Sig.FUNCTOR with module T := T;
  };
  let module Traversable: {
    let module T = T;
    include Sig.TRAVERSABLE with module T := T;
  };
};

let module Rose: {
  let module Def: {
    include module type Def.Cofree.Make Diag.Functor;
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

  let module Corolla: {
    type nonrec t 'a = list (t 'a);
    let equal: ('a => 'a => bool) => (t 'a => t 'a => bool);
    let compare: ('a => 'a => int) => (t 'a => t 'a => int);
    let pp: (formatter => 'a => unit) => (formatter => t 'a => unit);
    let show: (formatter => 'a => unit) => (t 'a => string);
  };

  let equal: ('a => 'a => bool) => (t 'a => t 'a => bool);
  let compare: ('a => 'a => int) => (t 'a => t 'a => int);
  let pp: (formatter => 'a => unit) => (formatter => t 'a => unit);
  let show: (formatter => 'a => unit) => (t 'a => string);
};

let module List: {
  let module Lenses: {
    let module Rose: {
      let node: Lens.t (Rose.t 'a) 'a;
      let diag: Lens.t (Rose.t 'a) (Diag.t (Rose.t 'a));
      let lhs: unit => Lens.t (Rose.t 'a) (list (Rose.t 'a));
      let rhs: unit => Lens.t (Rose.t 'a) (list (Rose.t 'a));
    };
    let module Diag: {
      let lhs: Lens.t (Diag.t 'a) (list 'a);
      let rhs: Lens.t (Diag.t 'a) (list 'a);
    };
  };

  let module Prisms: {
    let nil: PrismP.t (list 'a) (list 'a) unit 'b;
    let cons: Prism.t (list 'a) ('a, list 'a);
  };
};
