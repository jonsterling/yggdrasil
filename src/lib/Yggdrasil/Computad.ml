open Format

module type S = sig
  open Syntax.Term
  type t
  [@@deriving show]
  val empty : t
  val bind : t -> Dimension.t -> Cell.t -> t
  val arity : t -> Operator.t -> Rose.t
end

module Trie = struct
  open Syntax.Term
  include CCTrie.MakeList(struct
      type t = Rose.t
      let compare = Rose.compare
    end)
end

module Patterns : sig
  open Syntax.Term
  type t = (Rose.t * Operator.t) Trie.t
  [@@deriving show]
end = struct
  open Syntax.Term

  let print fmt trie =
    let list =
      List.fast_sort
        (fun (_pt0, (_ar0, op0)) (_pt1, (_ar1, op1)) -> Operator.compare op0 op1)
        (Trie.to_list trie) in
    let assoc fmt = function
      | ([ tm ], (cod, op)) ->
        fprintf fmt "@[<2>%a@ :@ %a@,@ @[->@ %a@]@]"
          (Operator.pp) op
          (Rose.pp 2) tm
          (Rose.pp 2) cod
      | (dom, (cod, op)) ->
        fprintf fmt "@[<2>%a@ :@ %a@,@ @[->@ %a@]@]"
          (Operator.pp) op
          (CCFormat.list @@ Rose.pp 2) dom
          (Rose.pp 2) cod in
    fprintf fmt "@[<v>%a@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
  type t = (Rose.t * string) Trie.t [@show.printer print]
  [@@deriving show]
end

module Map = struct
  open Syntax.Term
  include CCMap.Make(struct
      type t = Operator.t
      let compare = compare
    end)
end

open Syntax.Term

type t = {
  cells : Rose.t Map.t;
  dimensions : Dimension.t Map.t;
  rules : Patterns.t Map.t;
}

module Cells = struct
  let pp computad fmt map =
    let assoc fmt (op, ar) =
      let dm = Map.find op computad.dimensions in
      fprintf fmt "@[<2>[%a]@ (∂@ %a@ %a)@]"
        (Dimension.pp) (Map.find op computad.dimensions)
        (Operator.pp) op
        (Arity.pp dm) ar in
    let sort (op0, ar0) (op1, ar1) =
      match ((op0, Map.find op0 computad.dimensions), (op1, Map.find op1 computad.dimensions)) with
      | (op0, dm0), (op1, dm1) when dm0 < 2 && Dimension.equal dm0 dm1 ->
        begin
          match Rose.compare ar0 ar1 with
          | 0 -> Operator.compare op0 op1
          | ord -> ord
        end
      | (op0, dm0), (op1, dm1) ->
        begin
          match Dimension.compare dm0 dm1 with
          | 0 -> Operator.compare op0 op1
          | ord -> ord
        end in
    let list = List.fast_sort sort (Map.to_list map) in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
end

module Dimensions = struct
  let pp (computad : t) fmt map =
    let assoc fmt (op, dm) =
      fprintf fmt "@[<2>(dim@ %a@ %a)@]"
        (Operator.pp) op
        (Dimension.pp) dm in
    let sort od0 od1 =
      match (od0, od1) with
      | (op0, dm0), (op1, dm1) when dm0 < 2 && Dimension.equal dm0 dm1 ->
        begin
          match Rose.compare (Map.find op0 computad.cells) (Map.find op1 computad.cells) with
          | 0 -> Operator.compare op0 op1
          | ord -> ord
        end
      | (op0, dm0), (op1, dm1) ->
        begin
          match Dimension.compare dm0 dm1 with
          | 0 -> Operator.compare op0 op1
          | ord -> ord
        end in
    let list = List.fast_sort sort (Map.to_list map) in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
end

module Rules = struct
  let pp _computad fmt map =
    let assoc fmt (op, rules) =
      fprintf fmt "@[<v 2>%a@[@ @][@,%a@,]@]"
        (Operator.pp) op
        (Patterns.pp) rules in
    let list = List.fast_sort (fun (lhs, _) (rhs, _) -> String.compare lhs rhs) @@ Map.to_list map in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
end

let pp fmt computad =
  fprintf fmt "@,@[<v 2>computad:@,"
; if not (Map.is_empty computad.cells) then
    fprintf fmt "@,@[<v>cells:@,%a@]" (Cells.pp computad) computad.cells
; if not (Map.is_empty computad.rules) then
    fprintf fmt "@,@[<v>rules:@,%a@]"  (Rules.pp computad) computad.rules
; fprintf fmt "@]"

let show computad =
  let buffer = Buffer.create 0 in
  let fmt = formatter_of_buffer buffer in
  pp fmt computad;
  pp_print_flush fmt ();
  Buffer.contents buffer

let empty = {
  cells = Map.empty;
  dimensions = Map.empty;
  rules = Map.empty;
}

let bind sigma dim { Cell.name; arity } =
  let cells = Map.add name arity sigma.cells in
  let dimensions = Map.add name dim sigma.dimensions in
  let rules =
    match [@warning "-4"] arity with
    | Data.Rose.Fork (_, [ Data.Rose.Fork (Node.Op theta, spine) ]) when dim > 1 ->
      let update = function
        | None ->
          Some (Trie.add spine (arity, name) Trie.empty)
        | Some pre ->
          Some (Trie.add spine (arity, name) pre) in
      Map.update theta update sigma.rules
    | _ ->
      sigma.rules in
  { cells; dimensions; rules }

let arity sigma op =
  Map.find op sigma.cells
