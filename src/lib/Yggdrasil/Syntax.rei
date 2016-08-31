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
  type t = (Variable.t, Frame.t) [@@deriving (eq, ord, show)];
}

and Complex: {
  type t = Data.Rose.Corolla.t Face.t [@@deriving (eq, ord)];
}

and Face: {
  type t =
    | Ap Term.t
    | Lam Telescope.t t
    | Op Operator.t
    | Var Variable.t
    [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let pp_node: (formatter => Term.t => unit) => (formatter => t => unit);
  let show: Dimension.t => t => string;
  let ap: Face.t => Complex.t => t;
  let op: Operator.t => t;
}

and Frame: {
  type t = Term.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let point: Face.t => t;
}

and Niche: {
  type t = Complex.t [@@deriving (eq, ord)];
}

and Telescope: {
  type t = list Bind.t [@@deriving (eq, ord)];
}

and Term: {
  type t = Data.Rose.t Face.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: t => Complex.t => t;
  let op: Operator.t => Complex.t => t;
};

let module Cell: {
  type t = {
    op: Operator.t,
    frame: Frame.t,
  } [@@deriving (eq, ord)];
};

let (*@): Face.t => Complex.t => Face.t;
let (-->): Niche.t => Face.t => Frame.t;
let (<:): Operator.t => Frame.t => Cell.t;
let (<!): Operator.t => Face.t => Cell.t;

let module Builtin: {
  let star: Face.t;
};
