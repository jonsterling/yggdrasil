type t = {
  op : Operator.t;
  ar : Arity.t;
} [@@deriving eq, ord, show]
val source : t -> Arity.t list
val target : t -> Syntax.Term.t
val ( <: ) : Operator.t -> Arity.t -> t
val ( <! ) : Operator.t -> Syntax.Term.t -> t