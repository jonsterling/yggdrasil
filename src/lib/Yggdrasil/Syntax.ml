open Data
open Format

module Dimension = struct
  type t = int [@@deriving (eq, ord, show)]
end

module Name : sig
  module Meta : sig
    type t = string [@@deriving (eq, ord, show)]
  end
  module Oper : sig
    type t = string [@@deriving (eq, ord, show)]
  end
  module Term : sig
    type t = string [@@deriving (eq, ord, show)]
  end
  type t =
    | Meta of Meta.t
    | Oper of Oper.t
    | Term of Term.t
  [@@deriving (eq, ord, show)]
end = struct
  module Meta = struct
    type t = string [@show.printer Fmt.string] [@@deriving (eq, ord, show)]
  end
  module Oper = struct
    type t = string [@show.printer Fmt.string] [@@deriving (eq, ord, show)]
  end
  module Term = struct
    type t = string [@show.printer Fmt.string] [@@deriving (eq, ord, show)]
  end
  type t =
    | Meta of Meta.t
    | Oper of Oper.t
    | Term of Term.t
  [@@deriving (eq, ord)]
  let pp fmt = function
    | Meta varM -> Meta.pp fmt varM
    | Oper varO -> Oper.pp fmt varO
    | Term varT -> Term.pp fmt varT
  let show = [%derive.show: t]
end

module rec Bind : sig
  module Meta : sig
    type t = Name.Meta.t * Frame.t [@@deriving (eq, ord, show)]
  end
  module Term : sig
    type t = Name.Term.t * Frame.t [@@deriving (eq, ord, show)]
  end
end = struct
  module Meta = struct
    type t = Name.Meta.t * Frame.t [@@deriving (eq, ord)]
    let pp fmt (x, ar) =
      fprintf fmt "(%a@ %a@ %a)"
        (Fmt.if_utf_8 Token.Pretty.pp_utf_8 Token.Pretty.pp) Token.KEYWORD_CELL
        (Fmt.string) x
        (Frame.pp 0) ar
    let show = [%derive.show: t [@printer pp]]
  end
  module Term = struct
    type t = Name.Term.t * Frame.t [@@deriving (eq, ord)]
    let pp fmt (x, ar) =
      fprintf fmt "(%a@ %a@ %a)"
        (Fmt.if_utf_8 Token.Pretty.pp_utf_8 Token.Pretty.pp) Token.KEYWORD_CELL
        (Fmt.string) x
        (Frame.pp 0) ar
    let show = [%derive.show: t [@printer pp]]
  end
end

and Complex : sig
  type t = Node.t Rose.Corolla.t [@@deriving (eq, ord)]
end = struct
  type t = Node.t Rose.Corolla.t
  let equal = Rose.Corolla.equal Face.equal
  let compare = Rose.Corolla.compare Face.compare
end

and Face : sig
  type t =
    | Rho of Term.t
    | Abs of Scope.Meta.t * Scope.Term.t * t
    | Var of Name.t
  [@@deriving (eq, ord)]
  val pp : Dimension.t -> formatter -> t -> unit
  val pp_node : (formatter -> Term.t -> unit) -> formatter -> t -> unit
  val show : Dimension.t -> t -> string
  val ap : Face.t -> Complex.t -> t
  val op : Name.Oper.t -> t
end = struct
  type t =
    | Rho of Term.t
    | Abs of Scope.Meta.t * Scope.Term.t * t
    | Var of Name.t
  [@@deriving (eq, ord)]
  let rec pp_node pp_rose fmt tm = match tm with
    | Rho term -> pp_rose fmt term
    | Abs (_, [x], e) ->
      fprintf fmt "@[<2>(%a@ %a@ @[<2>%a@])@]"
        (Fmt.if_utf_8 Token.Pretty.pp_utf_8 Token.Pretty.pp) Token.KEYWORD_LAMBDA
        (Bind.Term.pp) x
        (pp_node pp_rose) e
    | Abs (_, xs, e) ->
      let sep fmt () = fprintf fmt "@ " in
      fprintf fmt "@[<2>(%a@ [%a]@ @[<2>%a@])@]"
        (Fmt.if_utf_8 Token.Pretty.pp_utf_8 Token.Pretty.pp) Token.KEYWORD_LAMBDA
        (Fmt.list ~sep Bind.Term.pp) xs
        (pp_node pp_rose) e
    | Var var -> Name.pp fmt var

  let pp dim = pp_node @@ Term.pp dim
  let show dim = [%derive.show: t [@printer pp dim]]

  let ap face complex =
    let lhs = [] in
    let rhs = complex in
    let complex = { Diag.lhs; rhs } in
    Rho (Rose.Fork (face, complex))

  let op oper = Var (Name.Oper oper)
end

and Frame : sig
  type t = Term.t [@@deriving (eq, ord)]
  val pp : Dimension.t -> formatter -> t -> unit
  val show : Dimension.t -> t -> string
  val point : Face.t -> t
end = struct
  type t = Term.t
  let equal = Term.equal
  let compare = Term.compare
  let rec pp dim fmt (Rose.Fork (face, { Diag.rhs = complex; _ })) =
    let sep fmt () = fprintf fmt "@ " in
    match complex with
    | [] ->
      fprintf fmt "%a"
        (Face.pp_node @@ Term.pp dim) face
    | [term] ->
      fprintf fmt "@[<1>(→@ %a@ %a)@]"
        (Term.pp dim) term
        (Face.pp dim) face
    | _ ->
      fprintf fmt "@[<1>(→@ [%a]@ %a)@]"
        (Fmt.list ~sep @@ Term.pp dim) complex
        (Face.pp dim) face
  let show dim = [%derive.show: Term.t [@printer pp dim]]
  let point face = Rose.pure face
end

and Niche : sig
  type t = Complex.t [@@deriving (eq, ord)]
end = struct
  type t = Complex.t
  let equal = Complex.equal
  let compare = Complex.compare
  let rec pp dim fmt (Rose.Fork (face, { Diag.rhs = complex; _ })) =
    let sep fmt () = fprintf fmt "@ " in
    match complex with
    | [] ->
      fprintf fmt "%a"
        (Face.pp_node @@ Term.pp dim) face
    | [term] ->
      fprintf fmt "@[<1>(→@ %a@ %a)@]"
        (Term.pp dim) term
        (Face.pp dim) face
    | _ ->
      fprintf fmt "@[<1>(→@ [%a]@ %a)@]"
        (Fmt.list ~sep @@ Term.pp dim) complex
        (Face.pp dim) face
  let show dim = [%derive.show: Term.t [@printer pp dim]]
  let pt cod = Rose.pure cod
end

and Node : sig
  type t = Face.t
end = struct
  type t = Face.t
end

and Scope : sig
  module Meta : sig
    type t = Bind.Meta.t list [@@deriving (eq, ord)]
  end
  module Term : sig
    type t = Bind.Term.t list [@@deriving (eq, ord)]
  end
end = struct
  module Meta = struct
    type t = Bind.Meta.t list [@@deriving (eq, ord)]
  end
  module Term = struct
    type t = Bind.Term.t list [@@deriving (eq, ord)]
  end
end

and Term : sig
  type t = Face.t Rose.t [@@deriving (eq, ord)]
  val pp: Dimension.t -> formatter -> t -> unit
  val show: Dimension.t -> t -> string
  val ap: t -> Complex.t -> t
  val op: Name.Oper.t -> Complex.t -> t
end = struct
  type t = Face.t Rose.t [@@deriving (eq)]
  let compare tm0 tm1 = Rose.compare (fun _ _ -> -1) tm0 tm1
  let rec pp dim fmt (Rose.Fork (face, { Diag.rhs = complex; _ })) =
    let sep fmt () = fprintf fmt "@ " in
    match complex with
    | [] -> fprintf fmt "%a" (Face.pp dim) face
    | _ when dim < 2 ->
      fprintf fmt "@[<2>(→@ %a@ %a)@]"
        (Face.pp dim) face
        (Fmt.list ~sep @@ pp dim) complex
    | _ ->
      fprintf fmt "@[<2>(%a@ %a)@]"
        (Face.pp dim) face
        (Fmt.list ~sep @@ pp dim) complex
  let show dim = [%derive.show: t [@printer pp dim]]
  let ap term complex =
    let face = Face.Rho term in
    let lhs = [] in
    let rhs = complex in
    let complex = { Diag.lhs; rhs } in
    Rose.Fork (face, complex)
  let op varO complex =
    let face = Face.Var (Name.Oper varO) in
    let lhs = [] in
    let rhs = complex in
    let complex = { Diag.lhs; rhs } in
    Rose.Fork (face, complex)
end

module Cell = struct
  type t = {
    oname: Name.Oper.t;
    frame: Frame.t;
  } [@@deriving (eq, ord)]
end

let ( *@< ) face complex =
  let lhs = [] in
  let rhs = complex in
  let complex = { Diag.lhs; rhs } in
  Rose.Fork (face, complex)

let ( *@ ) face complex =
  let lhs = [] in
  let rhs = complex in
  let complex = { Diag.lhs; rhs } in
  Face.Rho (Rose.Fork (face, complex))

let ( --> ) niche face =
  let lhs = [] in
  let rhs = niche in
  let niche = { Diag.lhs; rhs } in
  Rose.Fork (face, niche)

let ( <: ) oname frame =
  { Cell.oname; frame }

let ( <! ) oname face =
  { Cell.oname; frame = Frame.point face }

module Builtin = struct
  let star = Face.op "type"
end
