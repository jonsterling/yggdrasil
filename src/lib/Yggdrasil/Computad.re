open Format;

module type S = {
  open Syntax.Term;
  type t [@@deriving show];
  let empty: t;
  let bind: t => Dimension.t => Cell.t => t;
  let arity: t => Operator.t => Rose.t;
};

let module Trie = {
  open Syntax.Term;
  include CCTrie.MakeList {
    type t = Rose.t;
    let compare = Rose.compare;
  };
};

let module Patterns: {
  open Syntax.Term;
  type t = Trie.t (Rose.t, Operator.t) [@@deriving show];
} = {
  open Syntax.Term;
  let print fmt trie => {
    let dim = 2;
    let list =
      List.fast_sort
        (fun (_pt0, (_ar0, op0)) (_pt1, (_ar1, op1)) => Operator.compare op0 op1)
        (Trie.to_list trie);
    let assoc fmt => fun
      | ([dom], (cod, _op)) =>
        fprintf fmt "@[%a@,@ @[⇒@;<2>%a@]@]"
          (Rose.pp dim) dom
          (Rose.pp dim) cod
      | (dom, (cod, _op)) =>
        fprintf fmt "@[%a@,@ @[⇒@;<2>%a@]@]"
          (CCFormat.list @@ Rose.pp dim) dom
          (Rose.pp dim) cod;
    fprintf fmt "@[<v>%a@]" (CCFormat.list start::"" sep::"" stop::"" assoc) list
  };
  type t = Trie.t (Rose.t, string) [@show.printer print] [@@deriving show];
};

let module Map = {
  open Syntax.Term;
  include CCMap.Make {
    type t = Operator.t;
    let compare = compare;
  };
};

open Syntax.Term;

type t = {
  cells: Map.t Rose.t,
  dimensions: Map.t Dimension.t,
  rules: Map.t Patterns.t,
};

let module Cells = {
  let pp computad fmt map => {
    let assoc fmt (op, ar) => {
      let dm = Map.find op computad.dimensions;
      fprintf fmt "@[<6>[%a]@ (∂@ %a@ %a)@]"
        (Dimension.pp) (Map.find op computad.dimensions)
        (Operator.pp) op
        (Arity.pp dm) ar
    };
    let sort (op0, ar0) (op1, ar1) => {
      let dm0 = Map.find op0 computad.dimensions;
      let dm1 = Map.find op1 computad.dimensions;
      switch ((op0, dm0), (op1, dm1)) {
      | ((op0, dm0), (op1, dm1)) when dm0 < 2 && Dimension.equal dm0 dm1 => switch (Rose.compare ar0 ar1) {
        | 0 => Operator.compare op0 op1
        | ord => ord
        }
      | ((op0, dm0), (op1, dm1)) => switch (Dimension.compare dm0 dm1) {
        | 0 => Operator.compare op0 op1
        | ord => ord
        }
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
      (Operator.pp) op
      (Dimension.pp) dm;
    let sort od0 od1 => switch (od0, od1) {
      | ((op0, dm0), (op1, dm1)) when dm0 < 2 && Dimension.equal dm0 dm1 =>
        let ar0 = Map.find op0 computad.cells;
        let ar1 = Map.find op1 computad.cells;
        switch (Rose.compare ar0 ar1) {
        | 0 => Operator.compare op0 op1
        | ord => ord
        }
      | ((op0, dm0), (op1, dm1)) => switch (Dimension.compare dm0 dm1) {
        | 0 => Operator.compare op0 op1
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
        (Operator.pp) op
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

let show computad => {
  let buffer = Buffer.create 0;
  let fmt = formatter_of_buffer buffer;
  pp fmt computad;
  pp_print_flush fmt ();
  Buffer.contents buffer;
};

let empty = {
  cells: Map.empty,
  dimensions: Map.empty,
  rules: Map.empty,
};

let bind sigma dim { Cell.name: name, arity } => {
  open Data.Rose;
  let cells = Map.add name arity sigma.cells;
  let dimensions = Map.add name dim sigma.dimensions;
  let rules = switch arity {
    | Fork res [Fork (Node.Op theta) args] when dim > 1 =>
      let update = fun
        | None => Some (Trie.add args (Arity.pt res, name) Trie.empty)
        | Some pre => Some (Trie.add args (Arity.pt res, name) pre);
      Map.update theta update sigma.rules
    | _ => sigma.rules
  } [@warning "-4"];
  { cells, dimensions, rules }
};

let arity sigma op => Map.find op sigma.cells;
