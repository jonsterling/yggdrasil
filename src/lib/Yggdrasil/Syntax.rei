let module Term: {
  open Format;

  let module Dimension: {
    type t = int [@@deriving (eq, ord, show)];
  };

  let module Operator: {
    type t = string [@@deriving (eq, ord, show)];
  };

  let module Variable: {
    type t = string [@@deriving (eq, ord, show)];
  };

  let module rec Bind: {
    type t = (Variable.t, Rose.t) [@@deriving (eq, ord, show)];
  } and Bouquet: {
    type t = Data.Rose.Bouquet.t Node.t [@@deriving (eq, ord)];
  } and Node: {
    type t =
      | Ap Rose.t
      | Lm (list Bind.t) t
      | Op Operator.t
      | Var Variable.t
      [@@deriving (eq, ord)];
    let pp: Dimension.t => formatter => t => unit;
    let show: Dimension.t => t => string;
    let node: (formatter => Rose.t => unit) => (formatter => Node.t => unit);
    let ap: Node.t => Bouquet.t => t;
    let op: Operator.t => t;
  } and Rose: {
    type t = Data.Rose.t Node.t [@@deriving (eq, ord)];
    let pp: Dimension.t => formatter => t => unit;
    let show: Dimension.t => t => string;
    let ap: Rose.t => Bouquet.t => Rose.t;
    let op: Operator.t => Bouquet.t => Rose.t;
  };

  let module Arity: {
    let pp: Dimension.t => formatter => Rose.t => unit;
    let pt: Node.t => Rose.t;
    let show: Dimension.t => Rose.t => string;
  };

  let module Cell: {
    type t = {
      name: Operator.t,
      arity: Rose.t,
    } [@@deriving (eq, ord)];
  };

  let (*@): Node.t => Bouquet.t => Node.t;
  let (-->): Bouquet.t => Node.t => Rose.t;
  let (<:): Operator.t => Rose.t => Cell.t;
  let (<!): Operator.t => Node.t => Cell.t;

  let module Builtin: {
    let star: Node.t;
  };
};
