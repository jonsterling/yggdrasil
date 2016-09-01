open Format;
let module R = Data.Rose;

let module Dimension: {
  type t = int [@@deriving (eq, ord, show)];
};

let module Operator: {
  type t = string [@@deriving (eq, ord, show)];
};

let module Variable: {
  let module Meta: {
    type t = string [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = string [@@deriving (eq, ord, show)];
  };
};

let module rec Bind: {
  let module Meta: {
    type t = (Variable.Meta.t, Frame.t) [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = (Variable.Term.t, Frame.t) [@@deriving (eq, ord, show)];
  };
}

and Complex: {
  type t = R.Corolla.t Scoped.t [@@deriving (eq, ord)];
}

and Face: {
  type t =
    | Lm Telescope.Meta.t Telescope.Term.t t
    | Op Operator.t
    | Tm Term.t
    | VarM Variable.Meta.t
    | VarT Variable.Term.t
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

and Scoped: {
  type t = {
    tele: Telescope.Meta.t,
    face: Face.t,
  };
}

and Telescope: {
  let module Meta: {
    type t = list Bind.Meta.t [@@deriving (eq, ord)];
  };
  let module Term: {
    type t = list Bind.Term.t [@@deriving (eq, ord)];
  };
}

and Term: {
  type t = R.t Scoped.t [@@deriving (eq, ord)];
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
