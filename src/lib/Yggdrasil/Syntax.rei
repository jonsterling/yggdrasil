open Data;
open Format;

let module Dimension: {
  type t = int [@@deriving (eq, ord, show)];
};

let module Name: {
  let module Meta: {
    type t = string [@@deriving (eq, ord, show)];
  };
  let module Oper: {
    type t = string [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = string [@@deriving (eq, ord, show)];
  };
  type t =
    | Meta Meta.t
    | Oper Oper.t
    | Term Term.t
    [@@deriving (eq, ord, show)];
};

let module rec Bind: {
  let module Meta: {
    type t = (Name.Meta.t, Frame.t) [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = (Name.Term.t, Frame.t) [@@deriving (eq, ord, show)];
  };
}

and Complex: {
  type t = Rose.Corolla.t Node.t [@@deriving (eq, ord)];
}

and Face: {
  type t =
    | Rho Term.t
    | Abs Scope.Meta.t Scope.Term.t t
    | Var Name.t
    [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let pp_node: (formatter => Term.t => unit) => (formatter => t => unit);
  let show: Dimension.t => t => string;
  let ap: Face.t => Complex.t => t;
  let op: Name.Oper.t => t;
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

and Node: {
  type t = Face.t;
}

and Scope: {
  let module Meta: {
    type t = list Bind.Meta.t [@@deriving (eq, ord)];
  };
  let module Term: {
    type t = list Bind.Term.t [@@deriving (eq, ord)];
  };
}

and Term: {
  type t = Rose.t Node.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: t => Complex.t => t;
  let op: Name.Oper.t => Complex.t => t;
};

let module Cell: {
  type t = {
    oname: Name.Oper.t,
    frame: Frame.t,
  } [@@deriving (eq, ord)];
};

let (*@<): Face.t => Complex.t => Term.t;
let (*@): Face.t => Complex.t => Face.t;
let (-->): Niche.t => Face.t => Frame.t;
let (<:): Name.Oper.t => Frame.t => Cell.t;
let (<!): Name.Oper.t => Face.t => Cell.t;

let module Builtin: {
  let star: Face.t;
};
