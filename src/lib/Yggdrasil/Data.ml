module Rose = struct
  open Cats

  module Def = struct
    include (Def.Cofree.Make (Def.Functor.List))
    include (Def.Comonad.Cofree (Def.Functor.List) : Sig.COMONAD with module T := T)
    include (Def.Traversable.Cofree (Def.Functor.List) (Def.Traversable.List) : Sig.TRAVERSABLE with module T := T)

    let fork x xs = Fork (x, xs)

    let pure x = Fork (x, [])

    let rec bind (Fork (x, xs)) k = match k x with
      | Fork (x', xs') ->
        Fork (x', List.append xs' @@ CCList.map (fun x -> bind x k) xs)

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

  let rec equal eq_elem (Fork (x, xs)) (Fork (y, ys)) =
    eq_elem x y
    && equal_bouquet eq_elem xs ys
  and equal_bouquet eq_elem xs ys =
    CCList.equal (equal eq_elem) xs ys

  let rec compare ord_elem (Fork (x, xs)) (Fork (y, ys)) =
    match ord_elem x y with
    | 0 -> compare_bouquet ord_elem xs ys
    | ord -> ord
  and compare_bouquet ord_elem xs ys =
    CCList.compare (compare ord_elem) xs ys

  let rec pp pp_elem fmt (Fork (x, xs)) =
    Format.fprintf fmt "@[<v>Fork@,(@[<h>@ %a@]@,,@[<h>@ %a@ @])@]"
      (pp_elem) x
      (pp_bouquet pp_elem) xs
  and pp_bouquet pp_elem fmt xs =
    let pp_sep fmt () = Format.fprintf fmt "@,,@[@ @]" in
    Format.fprintf fmt "@[<v 2>[@["
  ; if not (CCList.is_empty xs) then
      Format.fprintf fmt "@ "
  ; Format.fprintf fmt "@]%a@["
      (Format.pp_print_list ~pp_sep @@ pp pp_elem) xs
  ; if not (CCList.is_empty xs) then
      Format.fprintf fmt "@ "
  ; Format.fprintf fmt "@]]@]"

  let show_poly pp_t pp_elem rose =
    let buffer = Buffer.create 0 in
    let fmt = Format.formatter_of_buffer buffer in
    pp_t pp_elem fmt rose;
    Format.pp_print_flush fmt ();
    Buffer.contents buffer

  let show pp_elem = show_poly pp pp_elem

  module Bouquet = struct
    type nonrec 'a t = 'a Def.t list
    let equal = equal_bouquet
    let compare = compare_bouquet
    let pp = pp_bouquet
    let show pp_elem = show_poly pp_bouquet pp_elem
  end

  module Lenses = struct
    let head = object
      method get = extract
      method set h (Fork (_, t)) = Fork (h, t)
    end

    let tail = object
      method get (Fork (_, t)) = t
      method set t (Fork (h, _)) = Fork (h, t)
    end
  end

  module Prisms = struct
    open Amb
    open Coproduct

    let nil = object
      method inj = const []
      method inv = function
        | [] -> inr ()
        | xs -> inl xs
    end

    let cons = object
      method inj (x, xs) = x :: xs
      method inv = function
        | x :: xs -> inr (x, xs)
        | xs -> inl xs
    end
  end
end
