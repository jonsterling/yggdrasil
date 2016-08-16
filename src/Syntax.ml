module rec Spine : sig
  type t = Term.t list
  [@@deriving eq, ord, show]
end = struct
  type t = Term.t list
  [@@deriving eq, ord]

  let pp fmt sp =
    let open Format in
    let sep fmt () =
      fprintf fmt "@,,@ " in
    fprintf fmt "[@[<2>%a@]]"
      (pp_print_list ~pp_sep:sep Term.pp) sp

  let show = Pretty.show pp
end

and Term : sig
  type t =
    | Ap of {
      op : Operator.t;
      sp : Spine.t;
    }
  [@@deriving eq, ord, show]
  val ( *@ ) : Operator.t -> Spine.t -> t
  val ap : Operator.t -> Spine.t -> t
  val op : Operator.t -> t
end = struct
  type t =
    | Ap of {
      op : Operator.t;
      sp : Spine.t;
    }
  [@@deriving eq, ord]

  let ap op sp =
    Ap { op; sp }

  let pp fmt ar =
    let open Format in
    match ar with
    | Ap { op; sp = [] } ->
      fprintf fmt "%a"
        Operator.pp op
    | Ap { op; sp } ->
      fprintf fmt "@[%a@ %a@]"
        Operator.pp op
        Spine.pp sp

  let show = Pretty.show pp

  let op op =
    ap op []
  let ( *@ ) =
    ap
end