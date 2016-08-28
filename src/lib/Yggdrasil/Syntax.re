let module Term = {
  open Data.Rose;
  open Format;

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
    type t = (Variable.t, Rose.t) [@@deriving (eq, ord, show)];
  } = {
    type t = (Variable.t, Rose.t) [@@deriving (eq, ord)];
    let pp fmt (x, ar) =>
      fprintf fmt "(∂@ %a@ %a)"
        (pp_print_string) x
        (Rose.pp 0) ar;
    let show bind => {
      let buffer = Buffer.create 0;
      let fmt = formatter_of_buffer buffer;
      pp fmt bind;
      pp_print_flush fmt ();
      Buffer.contents buffer
    };
  }

  and Bouquet: {
    type t = Data.Rose.Bouquet.t Node.t [@@deriving (eq, ord)];
  } = {
    type t = Data.Rose.Bouquet.t Node.t [@@deriving (eq, ord)];
  }

  and Node: {
    type t =
      | Ap Rose.t
      | Lm (list Bind.t) t
      | Op Operator.t
      | Var Variable.t
    [@@deriving (eq, ord)];
    let pp: Dimension.t => formatter => t => unit;
    let show: Dimension.t => t => string;
    let node: (formatter => Rose.t => unit) => formatter => Node.t => unit;
    let ap: Node.t => Bouquet.t => t;
    let op: Operator.t => t;
  } = {
    type t =
      | Ap Rose.t
      | Lm (list Bind.t) t
      | Op Operator.t
      | Var Variable.t
    [@@deriving (eq, ord)];
    let rec node pp_rose fmt tm =>
      switch tm {
      | Ap rho =>
        fprintf fmt "%a"
          (pp_rose) rho
      | Lm [x] e =>
        fprintf fmt "@[<2>(λ@ %a@ @[<2>%a@])@]"
        (Bind.pp) x
        (node pp_rose) e
      | Lm xs e =>
        let pp_sep fmt () => fprintf fmt "@ ";
        fprintf fmt "@[<2>(λ@ [%a]@ @[<2>%a@])@]"
          (pp_print_list pp_sep::pp_sep Bind.pp) xs
          (node pp_rose) e
      | Op theta =>
        fprintf fmt "%a"
          (Operator.pp) theta
      | Var x =>
        fprintf fmt "%a"
          (Variable.pp) x
      };
    let pp dim => node @@ Rose.pp dim;
    let show dim node => {
      let buffer = Buffer.create 0;
      let fmt = formatter_of_buffer buffer;
      pp dim fmt node;
      pp_print_flush fmt ();
      Buffer.contents buffer
    };
    let ap hd sp => Ap (Fork hd sp);
    let op head => Op head;
  }

  and Rose: {
    type t = Data.Rose.t Node.t [@@deriving (eq, ord)];
    let pp: Dimension.t => formatter => t => unit;
    let show: Dimension.t => t => string;
    let ap: Rose.t => Bouquet.t => Rose.t;
    let op: Operator.t => Bouquet.t => Rose.t;
  } = {
    type t = Data.Rose.t Node.t [@@deriving (eq, ord)];
    let rec pp dim fmt (Data.Rose.Fork hd sp) => {
      let pp_sep fmt () => fprintf fmt "@ ";
      switch sp {
      | [] => fprintf fmt "%a" (Node.pp dim) hd
      | _ when dim < 2 =>
        fprintf fmt "@[<2>(->@ %a@ %a)@]"
          (Node.pp dim) hd
          (pp_print_list pp_sep::pp_sep @@ pp dim) sp
      | _ =>
        fprintf fmt "@[<2>(%a@ %a)@]"
          (Node.pp dim) hd
          (pp_print_list pp_sep::pp_sep @@ pp dim) sp
      }
    };
    let show dim rose => {
      let buffer = Buffer.create 0;
      let fmt = formatter_of_buffer buffer;
      pp dim fmt rose;
      pp_print_flush fmt ();
      Buffer.contents buffer
    };
    let ap head spine => Fork (Node.Ap head) spine;
    let op head spine => Fork (Node.Op head) spine;
  };

  let module Arity = {
    let rec pp dim fmt (Data.Rose.Fork hd sp) => {
      let pp_sep fmt () => fprintf fmt "@ ";
      switch sp {
      | [] =>
        fprintf fmt "%a"
          (Node.node @@ Rose.pp dim) hd
      | [tm] =>
        fprintf fmt "@[<1>(->@ %a@ %a)@]"
          (Rose.pp dim) tm
          (Node.pp dim) hd
      | _ =>
        fprintf fmt "@[<1>(->@ [%a]@ %a)@]"
          (pp_print_list pp_sep::pp_sep @@ Rose.pp dim) sp
          (Node.pp dim) hd
      }
    };
    let show dim arity => {
      let buffer = Buffer.create 0;
      let fmt = formatter_of_buffer buffer;
      pp dim fmt arity;
      pp_print_flush fmt ();
      Buffer.contents buffer
    };
    let pt cod =>
      Data.Rose.pure cod;
  };

  let module Cell = {
    type t = {
      name: Operator.t,
      arity: Rose.t,
    } [@@deriving (eq, ord)];
  };

  let (*@) head spine => Node.Ap (Fork head spine);
  let (-->) dom cod => Fork cod dom;
  let (<:) name arity => {
    Cell.name: name,
    arity,
  };
  let (<!) name cod => {
    Cell.name: name,
    arity: Arity.pt cod,
  };

  let module Builtin = {
    let star = Node.op "type";
  };
};
