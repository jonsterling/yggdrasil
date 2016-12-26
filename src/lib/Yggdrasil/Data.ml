open Cats
open Format

module Diag = struct
  module L = Mod.Traversable.List
  type 'a t = { lhs : 'a list; rhs : 'a list } [@@deriving (eq, ord)]
  module T = TyCon.TC1(struct type nonrec 'a t = 'a t end)

  module Functor = struct
    module T = T
    let map op { lhs; rhs } =
      let lhs = CCList.map op lhs in
      let rhs = CCList.map op rhs in
      { lhs; rhs }
  end

  module Foldable = struct
    module T = T
    let fold_map (type m) (m : m Sig.monoid) act { lhs; rhs } =
      let module M = (val m) in L.fold_map m act (lhs @ rhs)
  end

  module Traversable = struct
    include Functor
    include (Foldable : module type of Foldable with module T := T)
    let traverse (type m) (m : m Sig.applicative) act { lhs; rhs } =
      let module M = (val m) in
        let lhs = M.T.el @@ (L.traverse m act lhs) in
        let rhs = M.T.el @@ (L.traverse m act rhs) in
        let ret = M.pure @@ (fun lhs -> fun rhs -> { lhs; rhs }) in
        M.T.co @@ (M.apply (M.apply ret lhs) rhs)
  end

  let rec pp pp_a fmt diag =
    let pp_list fmt list =
      match list with
      | [] -> fprintf fmt "[]"
      | _ ->
          let pp_sep fmt () = fprintf fmt ",@ " in
          (fprintf fmt "@[<hov 2>[@ ";
            Fmt.list ~sep:pp_sep pp_a fmt list;
            fprintf fmt "@]@ ]") in
    fprintf fmt "%a(@[<hov -5>@[<hov -3>@,%a,@ %a@]@,)@]"
      (Fmt.styled `Green Fmt.string) "Diag" pp_list diag.lhs pp_list
      diag.rhs
  let show pp_a = [%derive.show: _ t [@printer pp pp_a]]
end
module Rose = struct
  module Def = struct
    include Def.Cofree.Make(Diag.Functor)
    include (Def.Comonad.Cofree(Diag.Functor) : Sig.COMONAD with module T := T)
    include (Def.Traversable.Cofree(Diag.Functor)(Diag.Traversable) : Sig.TRAVERSABLE with module T := T)
    let fork node corollas = Fork (node, corollas)
    let pure node =
      let lhs = [] in
      let rhs = [] in
      Fork (node, { Diag.lhs = lhs; rhs })
    let rec bind (Fork (node, { Diag.lhs = lhsSuffix; rhs = rhsSuffix })) k =
      match k node with
      | Fork (node, { Diag.lhs = lhsPrefix; rhs = rhsPrefix }) ->
          let lhs = List.append lhsPrefix @@ CCList.map (fun x -> bind x k) lhsSuffix in
          let rhs = List.append rhsPrefix @@ CCList.map (fun x -> bind x k) rhsSuffix in
          Fork (node, { Diag.lhs = lhs; rhs })
    let apply mf mx =
      bind mf @@ fun f ->
      bind mx @@ fun x ->
      pure @@ f x
  end

  include Def
  include Ext.Apply.Make(Def)
  include Ext.Bind.Make(Def)
  include Ext.Comonad.Make(Def)
  include Ext.Extend.Make(Def)
  include Ext.Foldable.Make(Def)
  include Ext.Functor.Make(Def)
  include Ext.Monad.Make(Def)
  include Ext.Traversable.Make(Def)

  module Derived : sig
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val pp : (formatter -> 'a -> unit) -> formatter -> 'a t -> unit
    val show : (formatter -> 'a -> unit) -> 'a t -> string
  end = struct
    let rec equal eq_node (Fork (node0, diag0)) (Fork (node1, diag1)) =
      eq_node node0 node1
      && CCList.equal (equal eq_node) diag0.Diag.lhs diag1.Diag.lhs
      && CCList.equal (equal eq_node) diag0.Diag.rhs diag1.Diag.rhs
    let rec compare ord_node (Fork (node0, diag0)) (Fork (node1, diag1)) =
      match ord_node node0 node1 with
      | 0 -> begin
        match CCList.compare (compare ord_node) diag0.Diag.lhs diag1.Diag.lhs with
        | 0 -> CCList.compare (compare ord_node) diag1.Diag.lhs diag1.Diag.rhs
        | ord -> ord
      end
      | ord -> ord
    let rec pp pp_a fmt (Fork (node, diag)) =
      fprintf fmt "%a(@[<hov -5>@[<hov -3>@,%a,@ %a@]@,)@]"
        (Fmt.styled `Green Fmt.string) "Fork" pp_a node
        (Diag.pp @@ pp pp_a) diag
    let show pp_node = [%derive.show: _ t [@printer pp pp_node]]
  end
  module Corolla : sig
    type nonrec 'a t = 'a t list
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val pp : (formatter -> 'a -> unit) -> formatter -> 'a t -> unit
    val show : (formatter -> 'a -> unit) -> 'a t -> string
  end = struct
    type nonrec 'a t = 'a t list
    let equal eq_node = CCList.equal (Derived.equal eq_node)
    let compare ord_node = CCList.compare (Derived.compare ord_node)
    let pp pp_node = Fmt.list ~sep:Fmt.sp (Derived.pp pp_node)
    let show pp_node = [%derive.show: _ t [@printer pp pp_node]]
  end
  include Derived
end
