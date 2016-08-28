module type S = {
  open Syntax.Term;
  type t [@@deriving show];
  let empty: t;
  let bind: t => Dimension.t => Cell.t => t;
  let arity: t => Operator.t => Rose.t;
};

include S;
