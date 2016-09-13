open Format;
open Syntax;

module type Sig = {
  type t [@@deriving show];
  let empty: t;
  let bind: t => Dimension.t => Cell.t => t;
  let arity: t => Name.Oper.t => Frame.t;
};

let module Trie = CCTrie.MakeList {
  type t = Term.t;
  let compare = Term.compare;
};

let module Patterns: {
  type t = Trie.t Cell.t [@@deriving show];
} = {
  let print fmt (trie: Trie.t Cell.t) => {
    let dim = 2;
    let sort (_prefix0, cell0) (_prefix1, cell1) => Name.Oper.compare cell0.Cell.oname cell1.Cell.oname;
    let alist = List.fast_sort sort @@ Trie.to_list trie;
    let pp_entry fmt => fun
      | ([source], { Cell.frame: target, _ }) =>
        fprintf fmt "@[%a@,@ @[⇒@ %a@]@]"
          (Term.pp dim) source
          (Term.pp dim) target
      | (source, { Cell.frame: target, _ }) =>
        fprintf fmt "@[%a@,@ @[⇒@ %a@]@]"
          (CCFormat.list @@ Term.pp dim) source
          (Term.pp dim) target;
    fprintf fmt "@[<v>%a@]" (CCFormat.list start::"" sep::"" stop::"" pp_entry) alist
  };
  type t = Trie.t Cell.t [@show.printer print] [@@deriving show];
};

let module Map = CCMap.Make {
  type t = Name.Oper.t;
  let compare = compare;
};

type t = {
  cells: Map.t Frame.t,
  dimensions: Map.t Dimension.t,
  rules: Map.t Patterns.t,
};

let module Cells = {
  let pp computad fmt map => {
    let assoc fmt (op, ar) => {
      let dm = Map.find op computad.dimensions;
      fprintf fmt "@[<6>[%a]@ (∂@ %a@ %a)@]"
        (Dimension.pp) (Map.find op computad.dimensions)
        (Name.Oper.pp) op
        (Frame.pp dm) ar
    };
    let sort (op0, ar0) (op1, ar1) => {
      let dm0 = Map.find op0 computad.dimensions;
      let dm1 = Map.find op1 computad.dimensions;
      if (dm0 < 2 && Dimension.equal dm0 dm1) {
        switch (Term.compare ar0 ar1) {
        | 0 => Name.Oper.compare op0 op1
        | ord => ord
        };
      } else {
        switch (Dimension.compare dm0 dm1) {
        | 0 => Name.Oper.compare op0 op1
        | ord => ord
        };
      };
    };
    let list = List.fast_sort sort (Map.to_list map);
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list start::"" sep::"" stop::"" assoc) list
  };
};

let module Dimensions = {
  let pp (computad: t) fmt map => {
    let assoc fmt (op, dm) =>
      fprintf fmt "@[<2>(dim@ %a@ %a)@]"
      (Name.Oper.pp) op
      (Dimension.pp) dm;
    let sort od0 od1 => switch (od0, od1) {
      | ((op0, dm0), (op1, dm1)) when dm0 < 2 && Dimension.equal dm0 dm1 =>
        let ar0 = Map.find op0 computad.cells;
        let ar1 = Map.find op1 computad.cells;
        switch (Term.compare ar0 ar1) {
        | 0 => Name.Oper.compare op0 op1
        | ord => ord
        }
      | ((op0, dm0), (op1, dm1)) => switch (Dimension.compare dm0 dm1) {
        | 0 => Name.Oper.compare op0 op1
        | ord => ord
        }
      };
    let list = List.fast_sort sort (Map.to_list map);
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list start::"" sep::"" stop::"" assoc) list
  };
};

let module Rules = {
  let pp _computad fmt map => {
    let assoc fmt (op, rules) =>
      fprintf fmt "@[<v 2>%a@[@ ≜@]@,%a@]"
        (Name.Oper.pp) op
        (Patterns.pp) rules;
    let sort (lhs, _) (rhs, _) => String.compare lhs rhs;
    let list = List.fast_sort sort @@ Map.to_list map;
    fprintf fmt "@[<v 2>@[@  @]%a@,@]"
      (CCFormat.list start::"" sep::"" stop::"" assoc) list;
  };
};

let pp fmt computad => {
  fprintf fmt "@,@[<v 2>computad:@,";
  if (not @@ Map.is_empty computad.cells) {
    fprintf fmt "@,@[<v>cells:@,%a@]"
      (Cells.pp computad) computad.cells
  };
  if (not @@ Map.is_empty computad.rules) {
    fprintf fmt "@,@[<v>rules:@,%a@]"
      (Rules.pp computad) computad.rules
  };
  fprintf fmt "@]";
};

let show = [%derive.show: t [@printer pp]];

let empty = {
  cells: Map.empty,
  dimensions: Map.empty,
  rules: Map.empty,
};

let bind sigma dim { Cell.oname, frame } => {
  open Data;
  let cells = Map.add oname frame sigma.cells;
  let dimensions = Map.add oname dim sigma.dimensions;
  let rules = switch frame {
    | Rose.Fork face { Diag.rhs: [Rose.Fork (Face.Var (Name.Oper oper)) { Diag.rhs: args, _ }], _ } when dim > 1 =>
      let update trie => {
        switch trie {
        | None =>
          let frame = Frame.point face;
          let cell = { Cell.oname, frame };
          Some (Trie.add args cell Trie.empty);
        | Some pre =>
          let frame = Frame.point face;
          let cell = { Cell.oname, frame };
          Some (Trie.add args cell pre);
        };
      };
      Map.update oper update sigma.rules
    | _ => sigma.rules
  } [@warning "-4"];
  { cells, dimensions, rules }
};

let arity sigma op => Map.find op sigma.cells;
