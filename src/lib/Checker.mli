open Syntax

val spine_infer_check : Computad.t -> Term.t Spine.t -> Term.t Spine.t -> Term.t Spine.t
val term_infer_check : Computad.t -> Term.t -> Term.t -> Term.t Spine.t
val term_infer_infer : Computad.t -> Term.t -> Arity.t
