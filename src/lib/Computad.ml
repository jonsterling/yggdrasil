open Syntax

module Map = struct
  include CCMap.Make(struct
      type t = Operator.t
      let compare = Operator.compare
    end)

  let print_ops pp_key pp_elt fmt map : unit =
    let open Format in
    let assoc fmt (key, elt) =
      fprintf fmt "@[<2>%a@ :@ %a@]"
        pp_key key
        pp_elt elt in
    let list =
      List.fast_sort
        (fun (lhs, _) (rhs, _) -> Operator.compare lhs rhs)
        (to_list map) in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list

  let print_rls pp_key pp_elt fmt map : unit =
    let open Format in
    let assoc  fmt (key, elt) =
      fprintf fmt "@[<v 2>%a@[@ @][@,%a@,]@]"
        pp_key key
        pp_elt elt in
    let list = List.fast_sort (fun (lhs, _) (rhs, _) -> Operator.compare lhs rhs) @@ to_list map in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
end

module Trie = struct
  include CCTrie.MakeList(struct
      type t = Syntax.Term.t
      let compare = Syntax.Term.compare
    end)
end

module Rules : sig
  type t = (Syntax.Term.t * Operator.t) Trie.t
  [@@deriving show]
end = struct
  let print fmt trie =
    let open Format in
    let list =
      List.fast_sort
        (fun (_, (_, lhs)) (_, (_, rhs)) -> Operator.compare lhs rhs)
        (Trie.to_list trie) in
    let assoc fmt = function
      | ([ dom ], (cod, op)) ->
        fprintf fmt "@[<2>%a@ :@ %a@,@ @[->@ %a@]@]"
          Operator.pp op
          Syntax.Term.pp dom
          Syntax.Term.pp cod
      | (dom, (cod, op)) ->
        fprintf fmt "@[<2>%a@ :@ %a@,@ @[->@ %a@]@]"
          Operator.pp op
          Syntax.Spine.pp dom
          Syntax.Term.pp cod in
    fprintf fmt "@[<v>%a@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
  type t = (Syntax.Term.t * Operator.t) Trie.t [@show.printer print]
  [@@deriving show]
end

type t = {
  ars : (Arity.t Map.t [@show.printer Map.print_ops Operator.pp Arity.pp]);
  dms : (Dimension.t Map.t [@show.printer Map.print_ops Operator.pp Dimension.pp]);
  prs : (Rules.t Map.t [@show.printer Map.print_rls Operator.pp Rules.pp]);
} [@@deriving show]

let init = {
  ars = Map.empty;
  dms = Map.empty;
  prs = Map.empty;
}

let bind sg dm { Cell.op; ar } = {
  dms = Map.add op dm sg.dms;
  ars = Map.add op ar sg.ars;
  prs = match [@warning "-4"] ar with
    | { Arity.dom = [ { Arity.dom = []; cod = Term.Ap { op = theta; sp } } ]; _ } when dm > 1 ->
      let update = function
        | None ->
          Some (Trie.add sp (ar.Arity.cod, op) Trie.empty)
        | Some pre ->
          Some (Trie.add sp (ar.Arity.cod, op) pre) in
      Map.update theta update sg.prs
    | _ ->
      sg.prs
}

let arity sg op =
  Map.find op sg.ars

let dimen sg op =
  Map.find op sg.dms

let rec stepTm sg tm =
  match [@warning "-4"] tm with
  | Term.Ap { op; sp } ->
    let sp = stepSp sg sp in
    begin
      (* Try to look up the normalization rule. For now we assume that if
         the term is well typed but the lookup fails then there is an
         implicit loop. This allows cells like `ff` to normalize without
         us having to keep track of unnecessary data. *)
      try
        let prs = Map.find op sg.prs in
        let (res, _) = Trie.find_exn sp prs in
        res
      with Not_found ->
        Term.Ap { op; sp }
    end

and stepSp sg sp =
  CCList.map (stepTm sg) sp

let rec normTm sg acc =
  let res = stepTm sg acc in
  if Syntax.Term.equal acc res then
    acc
  else
    normTm sg res
