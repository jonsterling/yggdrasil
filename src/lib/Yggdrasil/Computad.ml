open Format

module type S = sig
  open Syntax
  type t
  [@@deriving show]
  val empty : t
  val bind : t -> Term.Dim.t -> Term.Cell.t -> t
  val arity : t -> Term.Op.t -> Term.Rose.t
end

module Std = struct
  open Syntax

  module Map = struct
    include CCMap.Make(struct
        type t = Term.Op.t
        let compare = compare
      end)

    module Arities = struct
      let print pp_key pp_elt fmt map =
        let assoc fmt (key, elt) =
          fprintf fmt "@[<2>(cell@ %a@ %a)@]"
            pp_key key
            pp_elt elt in
        let list =
          List.fast_sort
            (fun (lhs, _) (rhs, _) -> String.compare lhs rhs)
            (to_list map) in
        fprintf fmt "@[<v 2>@[@  @]%a@,@]"
          (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
    end

    module Rules = struct
      let print pp_key pp_elt fmt map =
        let assoc  fmt (key, elt) =
          fprintf fmt "@[<v 2>%a@[@ @][@,%a@,]@]"
            pp_key key
            pp_elt elt in
        let list = List.fast_sort (fun (lhs, _) (rhs, _) -> String.compare lhs rhs) @@ to_list map in
        fprintf fmt "@[<v 2>@[@  @]%a@,@]"
          (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
    end
  end

  module Trie = struct
    include CCTrie.MakeList(struct
        type t = Term.Rose.t
        let compare = Term.Rose.compare
      end)
  end

  module Rules : sig
    type t = (Term.Rose.t * Term.Op.t) Trie.t
    [@@deriving show]
  end = struct
    let print fmt trie =
      let list =
        List.fast_sort
          (fun (_, (_, lhs)) (_, (_, rhs)) -> String.compare lhs rhs)
          (Trie.to_list trie) in
      let assoc fmt = function
        | ([ tm ], (cod, op)) ->
          fprintf fmt "@[<2>%a@ :@ %a@,@ @[->@ %a@]@]"
          (Term.Op.pp) op
          (Term.Rose.pp) tm
          (Term.Rose.pp) cod
        | (dom, (cod, op)) ->
          fprintf fmt "@[<2>%a@ :@ %a@,@ @[->@ %a@]@]"
            (Term.Op.pp) op
            (CCFormat.list Term.Rose.pp) dom
            (Term.Rose.pp) cod in
      fprintf fmt "@[<v>%a@]"
        (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
    type t = (Term.Rose.t * string) Trie.t [@show.printer print]
    [@@deriving show]
  end

  type t = {
    arities : (Term.Rose.t Map.t [@show.printer Map.Arities.print Term.Op.pp Term.Arity.pp]);
    rules : (Rules.t Map.t [@show.printer Map.Rules.print Term.Op.pp Rules.pp]);
  } [@@deriving show]

  let empty = {
    arities = Map.empty;
    rules = Map.empty;
  }

  let bind sigma dim { Term.Cell.name; arity } =
    let arities = Map.add name arity sigma.arities in
    let rules =
      match [@warning "-4"] arity with
      | Data.Rose.Fork (_, [ Data.Rose.Fork (Term.Node.Op theta, spine) ]) when dim > 1 ->
        let update = function
          | None ->
            Some (Trie.add spine (arity, name) Trie.empty)
          | Some pre ->
            Some (Trie.add spine (arity, name) pre) in
        Map.update theta update sigma.rules
      | _ ->
        sigma.rules in
    { arities; rules }

  let arity sigma op =
    Map.find op sigma.arities
end
