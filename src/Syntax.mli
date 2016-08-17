module rec Spine : sig
  type t = Term.t list
  [@@deriving eq, ord, show]
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
end
