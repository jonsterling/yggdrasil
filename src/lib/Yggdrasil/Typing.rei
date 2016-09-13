let module S = Syntax;

let module Ctx: {
  type t [@@deriving (eq, ord)];
  let empty: t;
  let push: t => S.Scope.Term.t => t;
  let arity: t => S.Name.Term.t => S.Frame.t;
};

let module Chk: {
  let module Face: {
    let arity: Computad.t => Ctx.t => S.Face.t => S.Frame.t => unit;
  };
};
let module Inf: {
  let module Face: {
    let arity: Computad.t => Ctx.t => S.Face.t => S.Frame.t;
    let subtract: Computad.t => Ctx.t => S.Niche.t => S.Complex.t => S.Niche.t;
  };
  let module Term: {
    let arity: Computad.t => Ctx.t => S.Term.t => S.Frame.t;
  };
};
