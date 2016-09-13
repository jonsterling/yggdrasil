open Cats;
open Format;
open Optics;

let module Diag = {
  let module L = Mod.Traversable.List;
  type t 'a = {
    lhs: list 'a,
    rhs: list 'a,
  } [@@deriving (eq, ord, show)];
  let module T = TyCon.TC1({ type nonrec t 'a = t 'a });
  let module Functor = {
    let module T = T;
    let map op { lhs, rhs }=> {
      let lhs = CCList.map op lhs;
      let rhs = CCList.map op rhs;
      { lhs, rhs };
    };
  };
  let module Foldable = {
    let module T = T;
    let fold_map (type m) (m: Sig.monoid m) act { lhs, rhs }=> {
      let module M = (val m);
      L.fold_map m act (lhs @ rhs)
    };
  };
  let module Traversable = {
    include Functor;
    include (Foldable: module type Foldable with module T := T);
    let traverse (type m) (m: Sig.applicative m) act { lhs, rhs } => {
      let module M = (val m);
      let lhs = M.T.el @@ L.traverse m act lhs;
      let rhs = M.T.el @@ L.traverse m act rhs;
      let ret = M.pure @@ fun lhs rhs => { lhs, rhs };
      M.T.co @@ M.apply (M.apply ret lhs) rhs;
    };
  };
};

let module Rose = {
  let module Def = {
    include Def.Cofree.Make Diag.Functor;
    include (Def.Comonad.Cofree Diag.Functor: Sig.COMONAD with module T := T);
    include (Def.Traversable.Cofree Diag.Functor Diag.Traversable: Sig.TRAVERSABLE with module T := T);
    let fork node corollas => Fork node corollas;
    let pure node => {
      let lhs = [];
      let rhs = [];
      Fork node { Diag.lhs, rhs };
    };
    let rec bind (Fork node { Diag.lhs:lhsSuffix, rhs:rhsSuffix }) k => switch (k node) {
      | Fork node { Diag.lhs:lhsPrefix, rhs:rhsPrefix } => {
        let lhs = List.append lhsPrefix @@ CCList.map (fun x => bind x k) lhsSuffix;
        let rhs = List.append rhsPrefix @@ CCList.map (fun x => bind x k) rhsSuffix;
        Fork node { Diag.lhs, rhs };
      };
    };
    let apply mf mx =>
      bind mf @@ fun f =>
      bind mx @@ fun x =>
      pure @@ f x;
  };

  include Def;
  include Ext.Apply.Make Def;
  include Ext.Bind.Make Def;
  include Ext.Comonad.Make Def;
  include Ext.Extend.Make Def;
  include Ext.Foldable.Make Def;
  include Ext.Functor.Make Def;
  include Ext.Monad.Make Def;
  include Ext.Traversable.Make Def;

  let module Derived: {
    let equal: ('a => 'a => bool) => (t 'a => t 'a => bool);
    let compare: ('a => 'a => int) => (t 'a => t 'a => int);
    let pp: (formatter => 'a => unit) => (formatter => t 'a => unit);
    let show: (formatter => 'a => unit) => (t 'a => string);
  } = {
    let rec equal eq_node (Fork node0 diag0) (Fork node1 diag1) => {
      eq_node node0 node1 &&
      CCList.equal (equal eq_node) diag0.Diag.lhs diag1.Diag.lhs &&
      CCList.equal (equal eq_node) diag0.Diag.rhs diag1.Diag.rhs;
    };
    let rec compare ord_node (Fork node0 diag0) (Fork node1 diag1) => {
      switch (ord_node node0 node1) {
      | 0 =>
        switch (CCList.compare (compare ord_node) diag0.Diag.lhs diag1.Diag.lhs) {
        | 0 =>  CCList.compare (compare ord_node) diag1.Diag.lhs diag1.Diag.rhs;
        | ord => ord;
        }
      | ord => ord;
      };
    };
    let rec pp pp_node fmt (Fork node diag) => {
      fprintf fmt "Fork(@[%a,@ %a@])"
        (pp_node) node
        (Diag.pp (pp pp_node)) diag;
    };
    let show pp_node => [%derive.show: t _ [@printer pp pp_node]];
  };

  let module Corolla: {
    type nonrec t 'a = list (t 'a);
    let equal: ('a => 'a => bool) => (t 'a => t 'a => bool);
    let compare: ('a => 'a => int) => (t 'a => t 'a => int);
    let pp: (formatter => 'a => unit) => (formatter => t 'a => unit);
    let show: (formatter => 'a => unit) => (t 'a => string);
  } = {
    type nonrec t 'a = list (t 'a);
    let equal eq_node => CCList.equal (Derived.equal eq_node);
    let compare ord_node => CCList.compare (Derived.compare ord_node);
    let pp pp_node => pp_print_list pp_sep::pp_print_space (Derived.pp pp_node);
    let show pp_node => [%derive.show: t _ [@printer pp pp_node]];
  };

  include Derived;
};

let module List = {
  let module Lenses = {
    [@@@warning "-27"];
    open Lens.Ops;
    let module Diag = {
      let lhs = {
        method get { Diag.lhs, _ } => lhs;
        method set lhs diag => { ...diag, Diag.lhs };
      };
      let rhs = {
        method get { Diag.rhs, _ } => rhs;
        method set rhs diag => { ...diag, Diag.rhs };
      };
    };
    let module Rose = {
      open Rose;
      let node = {
        method get = extract;
        method set n (Fork _ d) => Fork n d;
      };
      let diag = {
        method get (Fork _ d) => d;
        method set d (Fork n _) => Fork n d;
      };
      let lhs () => diag %>\* Diag.lhs;
      let rhs () => diag %>\* Diag.rhs;
    };
  };

  let module Prisms = {
    [@@@warning "-27"];
    open Amb.Coproduct;

    let nil = {
      method inj _ => [];
      method inv = fun
        | [] => inr ()
        | xs => inl xs
    };

    let cons = {
      method inj (x, xs) => [x, ...xs];
      method inv = fun
        | [x, ...xs] => inr (x, xs)
        | xs => inl xs
    };
  };
};
