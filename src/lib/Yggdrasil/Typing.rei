let module T = Syntax.Term;

let module Ctx: {
  type t [@@deriving (eq, ord)];
  let empty: t;
  let push: t => list T.Bind.t => t;
  let arity: t => T.Variable.t => T.Rose.t;
};

let module Inf: {
  let module Node: {
    let arity: Computad.t => Ctx.t => T.Node.t => T.Rose.t;
    let subtract: Computad.t => Ctx.t => T.Bouquet.t => T.Bouquet.t => T.Bouquet.t;
  };
  let module Rose: {
    let arity: Computad.t => Ctx.t => T.Rose.t => T.Rose.t;
  };
};
let module Chk: {
  let module Node: {
    let arity: Computad.t => Ctx.t => T.Node.t => T.Rose.t => unit;
  };
};
