open Format
open Syntax

type name
type env

val supply : unit -> env

val arity : formatter -> Term.Rose.t -> unit
val term  : formatter -> Term.Node.t -> unit
