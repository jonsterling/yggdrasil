type t = {
  dom : t list;
  cod : Syntax.Term.t;
} [@@deriving eq, ord, show]
val ( --> ) : t list -> Syntax.Term.t -> t
val pt : Syntax.Term.t -> t
