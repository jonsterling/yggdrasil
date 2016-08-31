open Format;
let module R = Data.Rose;

let module Dimension = {
  type t = int [@@deriving (eq, ord, show)];
};

let module Operator = {
  type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
};

let module Variable = {
  type t = string [@show.printer pp_print_string] [@@deriving (eq, ord, show)];
};

let module rec Bind: {
  type t = (Variable.t, Frame.t) [@@deriving (eq, ord, show)];
} = {
  type t = (Variable.t, Frame.t) [@@deriving (eq, ord)];
  let pp fmt (x, ar) =>
    fprintf fmt "(∂@ %a@ %a)"
      (pp_print_string) x
      (Frame.pp 0) ar;
  let show = [%derive.show: t [@printer pp]];
}

and Complex: {
  type t = R.Corolla.t Face.t [@@deriving (eq, ord)];
} = {
  type t = R.Corolla.t Face.t [@@deriving (eq, ord)];
}

and Face: {
  type t =
    | Nest Term.t
    | Lm Telescope.t t
    | Op Operator.t
    | Var Variable.t
  [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let pp_node: (formatter => Term.t => unit) => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: Face.t => Complex.t => t;
  let op: Operator.t => t;
} = {
  type t =
    | Nest Term.t
    | Lm Telescope.t t
    | Op Operator.t
    | Var Variable.t
  [@@deriving (eq, ord)];
  let rec pp_node pp_rose fmt tm => switch tm {
  | Nest rho =>
      fprintf fmt "%a"
        (pp_rose) rho
    | Lm [x] e =>
      fprintf fmt "@[<2>(λ@ %a@ @[<2>%a@])@]"
        (Bind.pp) x
        (pp_node pp_rose) e
    | Lm xs e =>
      let pp_sep fmt () => fprintf fmt "@ ";
      fprintf fmt "@[<2>(λ@ [%a]@ @[<2>%a@])@]"
        (pp_print_list pp_sep::pp_sep Bind.pp) xs
        (pp_node pp_rose) e
    | Op theta =>
      fprintf fmt "%a"
        (Operator.pp) theta
    | Var x =>
      fprintf fmt "%a"
        (Variable.pp) x
    };
  let pp dim => pp_node @@ Term.pp dim;
  let show dim => [%derive.show: t [@printer pp dim]];
  let ap hd sp => Nest (R.Fork hd sp);
  let op head => Op head;
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
  let rec pp dim fmt (R.Fork hd sp) => {
    let pp_sep fmt () => fprintf fmt "@ ";
    switch sp {
    | [] =>
      fprintf fmt "%a"
        (Face.pp_node @@ Term.pp dim) hd
    | [tm] =>
      fprintf fmt "@[<1>(→@ %a@ %a)@]"
        (Term.pp dim) tm
        (Face.pp dim) hd
    | _ =>
      fprintf fmt "@[<1>(→@ [%a]@ %a)@]"
        (pp_print_list pp_sep::pp_sep @@ Term.pp dim) sp
        (Face.pp dim) hd
    }
  };
  let show dim => [%derive.show: Term.t [@printer pp dim]];
  let point cod => R.pure cod;
}

and Niche: {
  type t = Complex.t [@@deriving (eq, ord)];
} = {
  type t = Complex.t;
  let equal = Complex.equal;
  let compare = Complex.compare;
  let rec pp dim fmt (R.Fork hd sp) => {
    let pp_sep fmt () => fprintf fmt "@ ";
    switch sp {
    | [] =>
      fprintf fmt "%a"
        (Face.pp_node @@ Term.pp dim) hd
    | [tm] =>
      fprintf fmt "@[<1>(→@ %a@ %a)@]"
        (Term.pp dim) tm
        (Face.pp dim) hd
    | _ =>
      fprintf fmt "@[<1>(→@ [%a]@ %a)@]"
        (pp_print_list pp_sep::pp_sep @@ Term.pp dim) sp
        (Face.pp dim) hd
    }
  };
  let show dim => [%derive.show: Term.t [@printer pp dim]];
  let pt cod => R.pure cod;
}

and Telescope: {
  type t = list Bind.t [@@deriving (eq, ord)];
} = {
  type t = list Bind.t [@@deriving (eq, ord)];
}

and Term: {
  type t = R.t Face.t [@@deriving (eq, ord)];
  let pp: Dimension.t => formatter => t => unit;
  let show: Dimension.t => t => string;
  let ap: t => Complex.t => t;
  let op: Operator.t => Complex.t => t;
} = {
  type t = R.t Face.t [@@deriving (eq, ord)];
  let rec pp dim fmt (R.Fork hd sp) => {
    let pp_sep fmt () => fprintf fmt "@ ";
    switch sp {
    | [] => fprintf fmt "%a" (Face.pp dim) hd
    | _ when dim < 2 =>
      fprintf fmt "@[<2>(→@ %a@ %a)@]"
        (Face.pp dim) hd
        (pp_print_list pp_sep::pp_sep @@ pp dim) sp
    | _ =>
      fprintf fmt "@[<2>(%a@ %a)@]"
        (Face.pp dim) hd
        (pp_print_list pp_sep::pp_sep @@ pp dim) sp
    }
  };
  let show dim => [%derive.show: t [@printer pp dim]];
  let ap head spine => R.Fork (Face.Nest head) spine;
  let op head spine => R.Fork (Face.Op head) spine;
};

let module Cell = {
  type t = {
    op: Operator.t,
    frame: Frame.t,
  } [@@deriving (eq, ord)];
};

let (*@) head spine => Face.Nest (R.Fork head spine);
let (-->) dom cod => R.Fork cod dom;
let (<:) op frame => { Cell.op, frame };
let (<!) op face => { Cell.op, frame: Frame.point face };

let module Builtin = {
  let star = Face.op "type";
};
