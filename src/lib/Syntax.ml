module Dimension : sig
  type t = int
  [@@deriving eq, ord, show]
end = struct
  type t = int
  [@@deriving eq, ord, show]
end

module Operator : sig
  type t = string
  [@@deriving eq, ord, show]
end = struct
  type t = string [@show.printer fun fmt -> Format.fprintf fmt "%s"]
  [@@deriving eq, ord, show]
end

module rec Spine : sig
  type 'a t = 'a list
  [@@deriving eq, ord, show]
end = struct
  type 'a t = 'a list
  [@@deriving eq, ord]

  let pp pp_elt fmt sp =
    let open Format in
    let sep fmt () =
      fprintf fmt "@,,@ " in
    fprintf fmt "[@[<2>%a@]]"
      (pp_print_list ~pp_sep:sep pp_elt) sp

  let show pp_elt =
    Pretty.show @@ pp pp_elt
end

and Term : sig
  type t =
    | Ap of {
      op : Operator.t;
      sp : t Spine.t;
    }
  [@@deriving eq, ord, show]
  val ( *@ ) : Operator.t -> t Spine.t -> t
  val ap : Operator.t -> t Spine.t -> t
  val op : Operator.t -> t
end = struct
  type t =
    | Ap of {
      op : Operator.t;
      sp : t Spine.t;
    }
  [@@deriving eq, ord]

  let ap op sp =
    Ap { op; sp }

  let rec pp fmt ar =
    let open Format in
    match ar with
    | Ap { op; sp = [] } ->
      fprintf fmt "%a"
        Operator.pp op
    | Ap { op; sp } ->
      fprintf fmt "@[%a@ %a@]"
        Operator.pp op
        (Spine.pp pp) sp

  let show =
    Pretty.show pp

  let op op =
    ap op []

  let ( *@ ) =
    ap
end

module Arity : sig
  type t = {
    dom : Term.t Spine.t;
    cod : Term.t;
  } [@@deriving eq, ord, show]
  val ( --> ) : Term.t Spine.t -> Term.t -> t
  val pt : 'a -> 'a
  (*val pt : Term.t -> t*)
end = struct
  type t = {
    dom : Term.t Spine.t;
    cod : Term.t;
  } [@@deriving eq, ord]

  let rec pp fmt ar =
    let open Format in
    match ar with
    | { dom = []; cod } ->
      fprintf fmt "%a"
        Term.pp cod
    | { dom = [ dom ]; cod } ->
      fprintf fmt "%a@,@ @[->@ %a@]"
        Term.pp dom
        Term.pp cod
    | { dom; cod } ->
      let sep fmt () =
        fprintf fmt "@,,@ " in
      fprintf fmt "[%a]@,@ @[->@ %a@]"
        (pp_print_list ~pp_sep:sep Term.pp) dom
        Term.pp cod

  let show =
    Pretty.show pp

  let ( --> ) dom cod =
    { dom; cod }

  let pt x = x

  (*let pt cod =
    { dom = []; cod }*)
end

module Cell : sig
  type t = {
    op : Operator.t;
    ar : Arity.t;
  } [@@deriving eq, ord, show]
  val source : t -> Term.t Spine.t
  val target : t -> Term.t
  val ( <: ) : Operator.t -> Arity.t -> t
  val ( <! ) : Operator.t -> Term.t -> t
end = struct
  type t = {
    op : Operator.t;
    ar : Arity.t;
  } [@@deriving eq, ord, show]

  let source tm =
    tm.ar.Arity.dom

  let target tm =
    tm.ar.Arity.cod

  let ( <: ) op ar =
    { op; ar }

  (*let ( <! ) op cod =
    { op; ar = Arity.pt cod }*)
  let ( <! ) op cod =
    { op; ar = { Arity.dom = []; cod } }
end
