open Format
open Syntax

module type Sig = sig
  type t [@@deriving show]
  val empty : t
  val bind : t -> Dimension.t -> Cell.t -> t
  val arity : t -> Name.Oper.t -> Frame.t
end

module Trie = CCTrie.MakeList(struct
  type t = Term.t
  let compare = Term.compare
end)

module Patterns : sig
  type t = Cell.t Trie.t [@@deriving show]
end = struct
  let print fmt (trie : Cell.t Trie.t) =
    let dim = 2 in
    let sort (_prefix0, cell0) (_prefix1, cell1) = Name.Oper.compare cell0.Cell.oname cell1.Cell.oname in
    let alist = List.fast_sort sort @@ Trie.to_list trie in
    let pp_tok fmt `Arrow = Fmt.string fmt "=>" in
    let pp_tok_utf_8 fmt `Arrow = Uuseg_string.pp_utf_8 fmt "⇒" in
    let pp_entry fmt = function
      | ([source], { Cell.frame = target; _ }) ->
        fprintf fmt "@[%a@,@ @[%a@ %a@]@]"
          (Term.pp dim) source
          (Fmt.if_utf_8 pp_tok_utf_8 pp_tok) `Arrow
          (Term.pp dim) target
      | (source, { Cell.frame = target; _ }) ->
        fprintf fmt "@[%a@,@ @[%a@ %a@]@]"
          (CCFormat.list @@ Term.pp dim) source
          (Fmt.if_utf_8 pp_tok_utf_8 pp_tok) `Arrow
          (Term.pp dim) target in
    fprintf fmt "@[<v>%a@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" pp_entry) alist
  type t = Cell.t Trie.t [@show.printer print] [@@deriving show]
end

module Map = CCMap.Make(struct
  type t = Name.Oper.t
  let compare = compare
end)

type t = {
  cells: Frame.t Map.t;
  dimensions: Dimension.t Map.t;
  rules: Patterns.t Map.t;
}

module Cells = struct
  let pp computad fmt map =
    let sort (op0, ar0) (op1, ar1) =
      let dm0 = Map.find op0 computad.dimensions in
      let dm1 = Map.find op1 computad.dimensions in
      if dm0 < 2 && Dimension.equal dm0 dm1 then
        match Term.compare ar0 ar1 with
        | 0 -> Name.Oper.compare op0 op1
        | ord -> ord
      else
        match Dimension.compare dm0 dm1 with
        | 0 -> Name.Oper.compare op0 op1
        | ord -> ord in
    let alist = List.fast_sort sort (Map.to_list map) in
    let pp_entry fmt (op, ar) =
      let dm = Map.find op computad.dimensions in
      fprintf fmt "@[<6>[%a]@ (%a@ %a@ %a)@]"
        (Dimension.pp) (Map.find op computad.dimensions)
        (Fmt.if_utf_8 Token.Pretty.pp_utf_8 Token.Pretty.pp) Token.KEYWORD_CELL
        (Name.Oper.pp) op
        (Frame.pp dm) ar in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" pp_entry) alist
end

module Dimensions = struct
  let pp computad fmt map =
    let sort od0 od1 =
      match (od0, od1) with
      | ((op0, dm0), (op1, dm1)) when dm0 < 2 && Dimension.equal dm0 dm1 ->
        let ar0 = Map.find op0 computad.cells in
        let ar1 = Map.find op1 computad.cells in
        begin
          match Term.compare ar0 ar1 with
          | 0 -> Name.Oper.compare op0 op1
          | ord -> ord
        end
      | ((op0, dm0), (op1, dm1)) ->
        match Dimension.compare dm0 dm1 with
        | 0 -> Name.Oper.compare op0 op1
        | ord -> ord
        in
    let alist = List.fast_sort sort @@ Map.to_list map in
    let pp_entry fmt (op, dm) =
      fprintf fmt "@[<2>(dim@ %a@ %a)@]"
      (Name.Oper.pp) op
      (Dimension.pp) dm in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" pp_entry) alist
end

module Rules = struct
  let pp _computad fmt map =
    let sort (lhs, _) (rhs, _) = String.compare lhs rhs in
    let alist = List.fast_sort sort @@ Map.to_list map in
    let pp_tok fmt = function
      | `Arrow -> Fmt.string fmt ":=" in
    let pp_tok_utf_8 fmt = function
      | `Arrow -> Uuseg_string.pp_utf_8 fmt "≜" in
    let pp_entry fmt (op, rules) =
      fprintf fmt "@[<v 2>%a@[@ %a@]@,%a@]"
        (Name.Oper.pp) op
        (Fmt.if_utf_8 pp_tok_utf_8 pp_tok) `Arrow
        (Patterns.pp) rules in
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list ~start:"" ~sep:"" ~stop:"" pp_entry) alist
end

let pp fmt computad =
  fprintf fmt "@,@[<v 2>computad:@,"
  ; if not @@ Map.is_empty computad.cells then
      fprintf fmt "@,@[<v>cells:@,%a@]"
        (Cells.pp computad) computad.cells
  ; if not @@ Map.is_empty computad.rules then
      fprintf fmt "@,@[<v>rules:@,%a@]"
        (Rules.pp computad) computad.rules
  ; fprintf fmt "@]"

let show = [%derive.show: t [@printer pp]]

let empty = {
  cells = Map.empty;
  dimensions = Map.empty;
  rules = Map.empty;
}

let bind sigma dim { Cell.oname; frame } =
  let open Data in
  let cells = Map.add oname frame sigma.cells in
  let dimensions = Map.add oname dim sigma.dimensions in
  let rules = match [@warning "-4"] frame with
    | Rose.Fork (face, { Diag.rhs = [Rose.Fork (Face.Var (Name.Oper oper), { Diag.rhs = args; _ })]; _ }) when dim > 1 ->
      let update trie =
        match trie with
        | None ->
          let frame = Frame.point face in
          let cell = { Cell.oname; frame } in
          Some (Trie.add args cell Trie.empty)
        | Some pre ->
          let frame = Frame.point face in
          let cell = { Cell.oname; frame } in
          Some (Trie.add args cell pre) in
      Map.update oper update sigma.rules
    | _ -> sigma.rules in
  { cells; dimensions; rules }

let arity sigma op = Map.find op sigma.cells
