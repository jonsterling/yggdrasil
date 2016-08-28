let module Rose = {
  open Cats;
  open Format;

  let module Def = {
    include Def.Cofree.Make Def.Functor.List;
    include (Def.Comonad.Cofree Def.Functor.List: Sig.COMONAD with module T := T);
    include (
      Def.Traversable.Cofree Def.Functor.List Def.Traversable.List:
        Sig.TRAVERSABLE with module T := T
    );
    let fork x xs => Fork x xs;
    let pure x => Fork x [];
    let rec bind (Fork x xs) k =>
      switch (k x) {
      | Fork x' xs' => Fork x' (List.append xs' @@ CCList.map (fun x => bind x k) xs)
      };
    let apply mf mx => bind mf @@ (fun f => bind mx @@ (fun x => pure @@ f x));
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

  let rec equal eq_elem (Fork x xs) (Fork y ys) => eq_elem x y && equal_bouquet eq_elem xs ys
  and equal_bouquet eq_elem xs ys => CCList.equal (equal eq_elem) xs ys;

  let rec compare ord_elem (Fork x xs) (Fork y ys) =>
    switch (ord_elem x y) {
    | 0 => compare_bouquet ord_elem xs ys
    | ord => ord
    }
  and compare_bouquet ord_elem xs ys => CCList.compare (compare ord_elem) xs ys;

  let rec pp pp_elem fmt (Fork x xs) =>
    fprintf fmt "@[<v>Fork@,(@[<h>@ %a@]@,,@[<h>@ %a@ @])@]" pp_elem x (pp_bouquet pp_elem) xs
  and pp_bouquet pp_elem fmt xs => {
    let pp_sep fmt () => fprintf fmt "@,,@[@ @]";
    fprintf fmt "@[<v 2>[@[";
    if (not (CCList.is_empty xs)) {
      fprintf fmt "@ "
    };
    fprintf fmt "@]%a@[" (pp_print_list pp_sep::pp_sep @@ pp pp_elem) xs;
    if (not (CCList.is_empty xs)) {
      fprintf fmt "@ "
    };
    fprintf fmt "@]]@]"
  };

  let show_poly pp_t pp_elem rose => {
    let buffer = Buffer.create 0;
    let fmt = formatter_of_buffer buffer;
    pp_t pp_elem fmt rose;
    pp_print_flush fmt ();
    Buffer.contents buffer
  };

  let show pp_elem => show_poly pp pp_elem;

  let module Bouquet = {
    type nonrec t 'a = list (Def.t 'a);
    let equal = equal_bouquet;
    let compare = compare_bouquet;
    let pp = pp_bouquet;
    let show pp_elem => show_poly pp_bouquet pp_elem;
  };

  let module Lenses = {
    let head = { as _;
      method get = extract;
      method set h (Fork _ t) => Fork h t;
    };
    let tail = { as _;
      method get (Fork _ t) => t;
      method set t (Fork h _) => Fork h t;
    };
  };

  let module Prisms = {
    open Amb;
    open Coproduct;

    let nil = { as _;
      method inj = const [];
      method inv = fun
        | [] => inr ()
        | xs => inl xs
    };

    let cons = { as _;
      method inj (x, xs) => [x, ...xs];
      method inv = fun
        | [x, ...xs] => inr (x, xs)
        | xs => inl xs
    };
  };
};
