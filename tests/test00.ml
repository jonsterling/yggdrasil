open Yggdrasil
open Format
open Syntax

module N = Term.Node
module R = Term.Rose

open Term
open Term.Arity

module Computad = Typing.Make(Computad.Std)

let sg =
  Computad.empty
let star =
  N.op "type"

let sg =
  Computad.bind sg 0 ("bool" <! star)
let bool =
  N.op "bool"

let sg =
  Computad.bind sg 1 ("ff" <! bool)
let sg =
  Computad.bind sg 1 ("tt" <! bool)
let sg =
  Computad.bind sg 1 ("not" <: [ pt bool ] --> bool)
let sg =
  Computad.bind sg 1 ("con" <: [ pt bool; pt bool ] --> bool)
let ff =
  N.op "ff"
let tt =
  N.op "tt"
let not =
  N.op "not"
let con =
  N.op "con"

(*let sg =
  bind sg 2 ("not/ff" <: [ pt @@ "not" *@ [ ff ] ] --> tt)
let sg =
  bind sg 2 ("not/tt" <: [ pt @@ "not" *@ [ tt ] ] --> ff)
let not_ff =
  op "not-ff"
let not_tt =
  op "not-tt"

let sg =
  bind sg 2 ("con/ff/ff" <: [ pt @@ "con" *@ [ ff; ff ] ] --> ff)
let sg =
  bind sg 2 ("con/ff/tt" <: [ pt @@ "con" *@ [ ff; tt ] ] --> ff)
let sg =
  bind sg 2 ("con/tt/ff" <: [ pt @@ "con" *@ [ tt; ff ] ] --> ff)
let sg =
  bind sg 2 ("con/tt/tt" <: [ pt @@ "con" *@ [ tt; tt ] ] --> tt)
let con_ff_ff =
  op "con-ff-ff"
let con_ff_tt =
  op "con-ff-tt"
let con_tt_ff =
  op "con-tt-ff"
let con_tt_tt =
  op "con-tt-tt"

let sg =
  bind sg 0 ("nat" <! star)
let nat =
  op "nat"

let sg =
  bind sg 1 ("zero" <! nat)
let sg =
  bind sg 1 ("succ" <: [ pt nat ] --> nat)
let zero =
  op "zero"
let succ =
  op "succ"

(*let sg =
  bind sg 0 ("list" <! star)
let list =
  op "list"

let sg =
  bind sg 1 ("nil" <! list)
let sg =
  bind sg 1 ("cons" <: [ pt nat; pt list ] --> list)
let sg =
  bind sg 1 ("map" <: [ [ pt nat ] --> nat; pt list ] --> list)
let nil =
  op "nil"
let cons =
  op "cons"
let map =
  op "map"

let sg =
  bind sg 2 ("map/nil" <: [ pt @@ "map" *@ [ succ; nil ] ] --> nil)
let sg =
  bind sg 2 ("map/cons"  <: [ pt @@ "map" *@ [ succ; "cons" *@ [ zero; nil ] ] ] --> "cons" *@ [ "succ" *@ [ zero ]; "map" *@ [ succ; nil ] ])*)
*)

let analyze node =
  let rose = Computad.Inf.Node.arity sg node in
  let () =
    fprintf std_formatter "@.@[<v>@[<hv 2>term:@ %a@]@,@[<hv 2>type:@ %a@]@,@]"
    N.pp node
    R.pp rose
  ; pp_print_flush std_formatter () in
  rose

let () =
  fprintf std_formatter "%a"
    Computad.pp sg

let () =
  let rose = analyze @@ not *@ [ pt ff ] in
  assert (Rose.equal rose @@ pt bool)

(*
let () =
  let (_ar, tm) = analyze @@ "not" *@ [ tt ] in
  assert (tm = ff)

let () =
  let (_ar, tm) = analyze @@ "con" *@ [ ff; ff ] in
  assert (tm = ff)

let () =
  let (_ar, tm) = analyze @@ "con" *@ [ "con" *@ [ tt; tt ]; ff ] in
  assert (tm = ff)

let () =
  let (_ar, tm) = analyze @@ "con" *@ [ "con" *@ [ tt; tt ]; tt ] in
  assert (tm = tt)

let () =
  let (_ar, tm) = analyze @@ "con" *@ [ "con" *@ [ tt; tt ]; "not" *@ [ ff ] ] in
  assert (tm = tt)*)

(*let () =
  let res = normalize @@ "map" *@ [ succ; nil ] in
  assert (res = nil)

let () =
  let res = normalize @@ "map" *@ [ succ; "cons" *@ [ zero; nil ] ] in
  assert (res = "cons" *@ [ "succ" *@ [ zero ]; nil ])*)
