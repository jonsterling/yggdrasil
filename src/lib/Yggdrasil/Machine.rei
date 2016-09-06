open Format;

let module Endo: {
  type t 'a = 'a => 'a;
};

let module Syntax: {
  let module Var: {
    type t = int;
  };
  let module Term: {
    type t =
      | App t t
      | Lam t
      | Var Var.t
      ;
  };
  let module Sub: {
    type t 'a =
      | Cmp (t 'a) (t 'a)
      | Dot 'a (t 'a)
      | Id
      | Shift
      ;
    let map: ('a => 'b) => (t 'a => t 'b);
    let apply: t Term.t => Endo.t Term.t;
  };
};

let module Zip: {
  open Syntax;
  type t 'a =
    | App0 (t 'a) 'a
    | App1 'a (t 'a)
    | Halt
    | Lam (t 'a)
    ;
  let map: ('a => 'b) => (t 'a => t 'b);
  let apply: t Term.t => Endo.t Term.t;
};

let module Clo: {
  open Syntax;
  type t =
    | Clo Term.t (Sub.t t);
  let from: t => Term.t;
};

let module Pretty: {
  let module Delim: {
    type t;
  };
  let module Prec: {
    type t = int;
  };
  let module Name: {
    type t;
    let gen: unit => int => option string;
  };
  let module Env: {
    type t;
    let mk: unit => t;
  };

  type printer 'a = Env.t => Prec.t => formatter => 'a => unit;

  let module Term: {
    let pp: printer Syntax.Term.t;
  };
  let module Sub: {
    let pp: printer 'a => printer (Syntax.Sub.t 'a);
  };
  let module Clo: {
    let pp: printer Clo.t;
  };
  let module Zip: {
    let pp: printer 'a => printer (Zip.t 'a);
  };
};

let module Machine: {
  open Syntax;
  type t = {
    clo: Clo.t,
    ctx: Zip.t Clo.t,
  };
  let into: Term.t => t;
  let from: t => Term.t;
  let pp: formatter => string => t => unit;
  let halted: t => bool;
  let step: t => t;
  let norm: Syntax.Term.t => Syntax.Term.t;
};

let module Run: {
  let go: unit => Syntax.Term.t;
};
