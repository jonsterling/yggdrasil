open Format;

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
    let sub: Term.t => t Term.t => Term.t;
  };
};

let module Zip: {
  type t 'a =
    | App0 (t 'a) 'a
    | App1 'a (t 'a)
    | Halt
    | Lam (t 'a)
    ;
};

let module Clo: {
  type t =
    | Clo Syntax.Term.t (Syntax.Sub.t t);
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
  type t = {
    clo: Clo.t,
    ctx: Zip.t Clo.t,
  };
  let pp: formatter => t => unit;
  let step: t => t;
  let into: Syntax.Term.t => t;
};

let module Run: {
  type stepFun = unit => unit;
  let init: unit => stepFun;
};
