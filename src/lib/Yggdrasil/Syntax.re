open Data;
open Format;

let module Dimension = {
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
} = {
  let module Meta = {
    type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
  };
  let module Oper = {
    type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
  };
  let module Term = {
    type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
  };
  type t =
    | Meta Meta.t
    | Oper Oper.t
    | Term Term.t
    [@@deriving (eq, ord)];
  let pp fmt => fun
  | Meta varM => Meta.pp fmt varM
  | Oper varO => Oper.pp fmt varO
  | Term varT => Term.pp fmt varT;
  let show = [%derive.show: t];
};

let module rec Bind: {
  let module Meta: {
    type t = (Name.Meta.t, Frame.t) [@@deriving (eq, ord, show)];
  };
  let module Term: {
    type t = (Name.Term.t, Frame.t) [@@deriving (eq, ord, show)];
  };
} = {
  let module Meta = {
    type t = (Name.Meta.t, Frame.t) [@@deriving (eq, ord)];
    let pp fmt (x, ar) =>
      fprintf fmt "(∂@ %a@ %a)"
        (pp_print_string) x
        (Frame.pp 0) ar;
    let show = [%derive.show: t [@printer pp]];
  };
  let module Term = {
    type t = (Name.Term.t, Frame.t) [@@deriving (eq, ord)];
    let pp fmt (x, ar) =>
      fprintf fmt "(∂@ %a@ %a)"
        (pp_print_string) x
        (Frame.pp 0) ar;
    let show = [%derive.show: t [@printer pp]];
  };
}

and Complex: {
  type t = Rose.Corolla.t Node.t [@@deriving (eq, ord)];
} = {
  type t = Rose.Corolla.t Node.t;
  let equal = Rose.Corolla.equal Face.equal;
  let compare = Rose.Corolla.compare Face.compare;
}

and Face: {
  type t =
    | Rho Term.t
    | Abs Scope.Meta.t Scope.Term.t t
    | Var Name.t
    [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let pp_node: (formatter => Term.t => unit) => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: Face.t => Complex.t => t;
  let op: Name.Oper.t => t;
} = {
  type t =
    | Rho Term.t
    | Abs Scope.Meta.t Scope.Term.t t
    | Var Name.t
    [@@deriving (eq, ord)];
  let rec pp_node pp_rose fmt tm => switch tm {
    | Rho term => pp_rose fmt term
    | Abs _ [x] e =>
      fprintf fmt "@[<2>(λ@ %a@ @[<2>%a@])@]"
        (Bind.Term.pp) x
        (pp_node pp_rose) e
    | Abs _ xs e =>
      let pp_sep fmt () => fprintf fmt "@ ";
      fprintf fmt "@[<2>(λ@ [%a]@ @[<2>%a@])@]"
        (pp_print_list pp_sep::pp_sep Bind.Term.pp) xs
        (pp_node pp_rose) e
    | Var var => Name.pp fmt var
  };
  let pp dim => pp_node @@ Term.pp dim;
  let show dim => [%derive.show: t [@printer pp dim]];

  let ap face complex => {
    let lhs = [];
    let rhs = complex;
    let complex = { Diag.lhs, rhs };
    Rho (Rose.Fork face complex);
  };

  let op oper => Var (Name.Oper oper);
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
  let rec pp dim fmt (Rose.Fork face { Diag.rhs: complex, _ }) => {
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
  let point face => Rose.pure face;
}

and Niche: {
  type t = Complex.t [@@deriving (eq, ord)];
} = {
  type t = Complex.t;
  let equal = Complex.equal;
  let compare = Complex.compare;
  let rec pp dim fmt (Rose.Fork face { Diag.rhs: complex, _ }) => {
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
  let pt cod => Rose.pure cod;
}

and Node: {
  type t = Face.t;
} = {
  type t = Face.t;
}

and Scope: {
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
  type t = Rose.t Face.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: t => Complex.t => t;
  let op: Name.Oper.t => Complex.t => t;
} = {
  type t = Rose.t Face.t [@@deriving (eq)];
  let compare tm0 tm1 => {
    Rose.compare (fun _ _ => -1) tm0 tm1;
  };
  let rec pp dim fmt (Rose.Fork face { Diag.rhs: complex, _ }) => {
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
    let face = Face.Rho term;
    let lhs = [];
    let rhs = complex;
    let complex = { Diag.lhs, rhs };
    Rose.Fork face complex;
  };
  let op varO complex => {
    let face = Face.Var (Name.Oper varO);
    let lhs = [];
    let rhs = complex;
    let complex = { Diag.lhs, rhs };
    Rose.Fork face complex;
  };
};

let module Cell = {
  type t = {
    op: Name.Oper.t,
    frame: Frame.t,
  } [@@deriving (eq, ord)];
};

let (*@<) face complex => {
  let lhs = [];
  let rhs = complex;
  let complex = { Diag.lhs, rhs };
  Rose.Fork face complex;
};

let (*@) face complex => {
  let lhs = [];
  let rhs = complex;
  let complex = { Diag.lhs, rhs };
  Face.Rho (Rose.Fork face complex);
};

let (-->) niche face => {
  let lhs = [];
  let rhs = niche;
  let niche = { Diag.lhs, rhs };
  Rose.Fork face niche;
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
