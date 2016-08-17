type t
[@@deriving show]

val init : t
val bind : t -> Dimension.t -> Declaration.t -> t
val arity : t -> Operator.t -> Arity.t
val dimen : t -> Operator.t -> Dimension.t
val normTm : t -> Syntax.Term.t -> Syntax.Term.t
