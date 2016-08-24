open Yggdrasil
open Format
open Syntax

module A = Term.Arity
module N = Term.Node
module R = Term.Rose

open Term
open Term.Arity

module Computad = Typing.Make(Computad.Std)

let sg = Computad.empty
let star = N.op "type"

let sg = Computad.bind sg 0 ("bool" <! star)
let bool = N.op "bool"
let sg = Computad.bind sg 1 ("ff" <! bool)
let sg = Computad.bind sg 1 ("tt" <! bool)
let sg = Computad.bind sg 1 ("not" <: [ pt bool ] --> bool)
let sg = Computad.bind sg 1 ("and" <: [ pt bool; pt bool ] --> bool)
let ff = N.op "ff"
let tt = N.op "tt"
let not = N.op "not"
let con = N.op "and"
let sg = Computad.bind sg 2 ("not/ff" <: [ pt @@ not *@ [ pt ff ] ] --> tt)
let sg = Computad.bind sg 2 ("not/tt" <: [ pt @@ not *@ [ pt tt ] ] --> ff)
let sg = Computad.bind sg 2 ("and/ff/ff" <: [ pt @@ con *@ [ pt ff; pt ff ] ] --> ff)
let sg = Computad.bind sg 2 ("and/ff/tt" <: [ pt @@ con *@ [ pt ff; pt tt ] ] --> ff)
let sg = Computad.bind sg 2 ("and/tt/ff" <: [ pt @@ con *@ [ pt tt; pt ff ] ] --> ff)
let sg = Computad.bind sg 2 ("and/tt/tt" <: [ pt @@ con *@ [ pt tt; pt tt ] ] --> tt)
let and_ff_ff = N.op "and-ff-ff"
let and_ff_tt = N.op "and-ff-tt"
let and_tt_ff = N.op "and-tt-ff"
let and_tt_tt = N.op "and-tt-tt"

let sg = Computad.bind sg 0 ("nat" <! star)
let nat = N.op "nat"
let sg = Computad.bind sg 1 ("zero" <! nat)
let sg = Computad.bind sg 1 ("succ" <: [ pt nat ] --> nat)
let sg = Computad.bind sg 1 ("add"  <: [ pt nat; pt nat ] --> nat)
let zero = N.op "zero"
let succ = N.op "succ"
let add  = N.op "add"

let sg = Computad.bind sg 0 ("list" <! star)
let list = N.op "list"
let sg = Computad.bind sg 1 ("nil" <! list)
let sg = Computad.bind sg 1 ("cons" <: [ pt nat; pt list ] --> list)
let sg = Computad.bind sg 1 ("map" <: [ [ pt nat] --> nat; pt list ] --> list)
let nil = N.op "nil"
let cons = N.op "cons"
let map = N.op "map"
(*let sg = Computad.bind sg 2 ("map/nil" <: [ pt @@ map *@ [ pt succ; pt nil ] ] --> nil)
let sg = Computad.bind sg 2 ("map/cons" <: [ pt @@ map *@ [ pt succ; pt @@ cons *@ [ pt zero; pt nil ] ] ] --> cons *@ [ pt @@ succ *@ [ pt zero ]; pt nil ])*)

let analyze node =
  let rose = Computad.Inf.Node.arity sg node in
  let () =
    fprintf std_formatter "@.@[<v>@[<hv 2>term:@ %a@]@,@[<hv 2>type:@ %a@]@,@]"
    (N.pp 2) node
    (A.pp 0) rose
  ; pp_print_flush std_formatter () in
  rose

let () =
  fprintf std_formatter "%a"
    Computad.pp sg

let () =
  let rose = analyze @@ not *@ [ pt ff ] in
  assert (Rose.equal rose @@ pt bool)

(*let () =
  let rose = analyze @@ not *@ [ pt tt ] in
  assert (Rose.equal rose @@ pt bool)*)

let () =
  let rose = analyze @@ con *@ [] in
  (assert (Rose.equal rose @@ [ pt bool; pt bool ] --> bool))

let () =
  let rose = analyze @@ con *@ [ pt ff ] in
  (assert (Rose.equal rose @@ [ pt bool ] --> bool))

let () =
  let rose = analyze @@ con *@ [ pt ff; pt ff ] in
  (assert (Rose.equal rose @@ pt bool))

(*let () =
  let rose = analyze @@ nil in
  (assert (Rose.equal rose @@ pt list))

let () =
  let rose = analyze @@ cons in
  (assert (Rose.equal rose @@ [ pt nat; pt list ] --> list))*)

let () =
  let rose = analyze @@ map in
  (assert (Rose.equal rose @@ [ [ pt nat ] --> nat; pt list ] --> list))

let () =
  let rose = analyze @@ map *@ [ pt succ ] in
  (assert (Rose.equal rose @@ [ pt list ] --> list))

let () =
  let rose = analyze @@ map *@ [ pt succ; pt nil ] in
  (assert (Rose.equal rose @@ pt list))

let () =
  let rose = analyze @@ map *@ [] *@ [ pt succ ] *@ [ pt nil ] in
  (assert (Rose.equal rose @@ pt list))

let () =
  let rose = analyze @@ map *@ [ pt succ ] *@ [ pt nil ] in
  (assert (Rose.equal rose @@ pt list))
