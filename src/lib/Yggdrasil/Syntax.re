open Format;
let module R = Data.Rose;

let module Dimension = {
  type t = int [@@deriving (eq, ord, show)];
};

let module Operator = {
  type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
};

let module Variable: {
  let module Meta: {
    type t = string [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = string [@@deriving (eq, ord, show)];
  };
} = {
  let module Meta = {
    type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
  };
  let module Term = {
    type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
  };
};

let module rec Bind: {
  let module Meta: {
    type t = (Variable.Meta.t, Frame.t) [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = (Variable.Term.t, Frame.t) [@@deriving (eq, ord, show)];
  };
} = {
  let module Meta = {
    type t = (Variable.Meta.t, Frame.t) [@@deriving (eq, ord)];
    let pp fmt (x, ar) =>
      fprintf fmt "(∂@ %a@ %a)"
        (pp_print_string) x
        (Frame.pp 0) ar;
    let show = [%derive.show: t [@printer pp]];
  };
  let module Term = {
    type t = (Variable.Term.t, Frame.t) [@@deriving (eq, ord)];
    let pp fmt (x, ar) =>
      fprintf fmt "(∂@ %a@ %a)"
        (pp_print_string) x
        (Frame.pp 0) ar;
    let show = [%derive.show: t [@printer pp]];
  };
}

and Complex: {
  type t = R.Corolla.t Scoped.t [@@deriving (eq, ord)];
} = {
  type t = R.Corolla.t Scoped.t;
  let equal = R.Corolla.equal Scoped.equal;
  let compare = R.Corolla.compare Scoped.compare;
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
  let pp_node: (formatter => Term.t => unit) => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: Face.t => Complex.t => t;
  let op: Operator.t => t;
} = {
  type t =
    | Lm Telescope.Meta.t Telescope.Term.t t
    | Op Operator.t
    | Tm Term.t
    | VarM Variable.Meta.t
    | VarT Variable.Term.t
  [@@deriving (eq, ord)];
  let rec pp_node pp_rose fmt tm => switch tm {
    | Tm rho =>
      fprintf fmt "%a"
        (pp_rose) rho
    | Lm _ [x] e =>
      fprintf fmt "@[<2>(λ@ %a@ @[<2>%a@])@]"
        (Bind.Term.pp) x
        (pp_node pp_rose) e
    | Lm _ xs e =>
      let pp_sep fmt () => fprintf fmt "@ ";
      fprintf fmt "@[<2>(λ@ [%a]@ @[<2>%a@])@]"
        (pp_print_list pp_sep::pp_sep Bind.Term.pp) xs
        (pp_node pp_rose) e
    | Op theta =>
      fprintf fmt "%a"
        (Operator.pp) theta
    | VarM x =>
      fprintf fmt "%a"
        (Variable.Meta.pp) x
    | VarT x =>
      fprintf fmt "%a"
        (Variable.Term.pp) x
    };
  let pp dim => pp_node @@ Term.pp dim;
  let show dim => [%derive.show: t [@printer pp dim]];

  let ap face complex => {
    let tele = [];
    let scoped = { Scoped.tele, face };
    Tm (R.Fork scoped complex);
  };

  let op oper => Op oper;
}

and Frame: {
  type t = Term.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let point: Face.t => t;
} = {
  type t = Term.t;
  let equal = Term.equal;
  let compare = Term.compare;
  let rec pp dim fmt (R.Fork { Scoped.face, _ } complex: t) => {
    let pp_sep fmt () => fprintf fmt "@ ";
    switch complex {
    | [] =>
      fprintf fmt "%a"
        (Face.pp_node @@ Term.pp dim) face
    | [term] =>
      fprintf fmt "@[<1>(→@ %a@ %a)@]"
        (Term.pp dim) term
        (Face.pp dim) face
    | _ =>
      fprintf fmt "@[<1>(→@ [%a]@ %a)@]"
        (pp_print_list pp_sep::pp_sep @@ Term.pp dim) complex
        (Face.pp dim) face
    }
  };
  let show dim => [%derive.show: Term.t [@printer pp dim]];
  let point face => {
    let tele = [];
    let scoped = { Scoped.tele, face };
    R.pure scoped;
  };
}

and Niche: {
  type t = Complex.t [@@deriving (eq, ord)];
} = {
  type t = Complex.t;
  let equal = Complex.equal;
  let compare = Complex.compare;
  let rec pp dim fmt (R.Fork { Scoped.face, _ } complex) => {
    let pp_sep fmt () => fprintf fmt "@ ";
    switch complex {
    | [] =>
      fprintf fmt "%a"
        (Face.pp_node @@ Term.pp dim) face
    | [term] =>
      fprintf fmt "@[<1>(→@ %a@ %a)@]"
        (Term.pp dim) term
        (Face.pp dim) face
    | _ =>
      fprintf fmt "@[<1>(→@ [%a]@ %a)@]"
        (pp_print_list pp_sep::pp_sep @@ Term.pp dim) complex
        (Face.pp dim) face
    }
  };
  let show dim => [%derive.show: Term.t [@printer pp dim]];
  let pt cod => R.pure cod;
}

and Scoped: {
  type t = {
    tele: Telescope.Meta.t,
    face: Face.t,
  } [@@deriving (eq, ord)];
} = {
  type t = {
    tele: Telescope.Meta.t,
    face: Face.t,
  } [@@deriving (eq, ord)];
}

and Telescope: {
  let module Meta: {
    type t = list Bind.Meta.t [@@deriving (eq, ord)];
  };
  let module Term: {
    type t = list Bind.Term.t [@@deriving (eq, ord)];
  };
} = {
  let module Meta = {
    type t = list Bind.Meta.t [@@deriving (eq, ord)];
  };
  let module Term = {
    type t = list Bind.Term.t [@@deriving (eq, ord)];
  };
}

and Term: {
  type t = R.t Scoped.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: t => Complex.t => t;
  let op: Operator.t => Complex.t => t;
} = {
  type t = R.t Scoped.t [@@deriving (eq, ord)];
  let rec pp dim fmt (R.Fork { Scoped.face, _ } complex: t) => {
    let pp_sep fmt () => fprintf fmt "@ ";
    switch complex {
    | [] => fprintf fmt "%a" (Face.pp dim) face
    | _ when dim < 2 =>
      fprintf fmt "@[<2>(→@ %a@ %a)@]"
        (Face.pp dim) face
        (pp_print_list pp_sep::pp_sep @@ pp dim) complex
    | _ =>
      fprintf fmt "@[<2>(%a@ %a)@]"
        (Face.pp dim) face
        (pp_print_list pp_sep::pp_sep @@ pp dim) complex
    }
  };
  let show dim => [%derive.show: t [@printer pp dim]];
  let ap term complex => {
    let tele = [];
    let face = Face.Tm term;
    let scoped = { Scoped.tele, face };
    R.Fork scoped complex;
  };
  let op oper complex => {
    let tele = [];
    let face = Face.Op oper;
    let scoped = { Scoped.tele, face };
    R.Fork scoped complex;
  };
};

let module Cell = {
  type t = {
    op: Operator.t,
    frame: Frame.t,
  } [@@deriving (eq, ord)];
};

let (*@) face complex => {
  let tele = [];
  let scoped = { Scoped.tele, face };
  Face.Tm (R.Fork scoped complex);
};

let (-->) niche face => {
  let tele = [];
  let scoped = { Scoped.tele, face };
  R.Fork scoped niche;
};

let (<:) op frame => {
  { Cell.op, frame };
};

let (<!) op face => {
  { Cell.op, frame: Frame.point face };
};

let module Builtin = {
  let star = Face.op "type";
};
