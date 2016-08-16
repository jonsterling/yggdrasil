open Arity

type t = {
  op : Operator.t;
  ar : Arity.t;
} [@@deriving eq, ord, show]

let source tm =
  tm.ar.dom
let target tm =
  tm.ar.cod
let ( <: ) op ar =
  { op; ar }
let ( <! ) op cod =
  { op; ar = pt cod }
