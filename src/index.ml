module Op = struct
  [@@@warning "-39"]
  type t = string
  [@@deriving eq, ord, show]
end

module Tp = struct
  [@@@warning "-39"]
  type t = string
  [@@deriving eq, ord, show]
end

module rec Sp : sig
  type t = Tm.t list
  [@@deriving eq, ord, show]
end = struct
  [@@@warning "-39"]
  type t = Tm.t list
  [@@deriving eq, ord, show]
end

and Tm : sig
  type t =
    | Id of { tp : Tp.t }
    | Ap of { op : Op.t; sp : Sp.t }
  [@@deriving eq, ord, show]
  val ap : Op.t -> Sp.t -> t
  val op : Op.t -> t
end = struct
  [@@@warning "-39"]
  type t =
    | Id of { tp : Tp.t }
    | Ap of { op : Op.t; sp : Sp.t }
  [@@deriving eq, ord, show]
  let ap op sp = Ap { op; sp }
  let op op = ap op []
end

module Ar = struct
  [@@@warning "-39"]
  type t = { dom : Tm.t list; cod : Tm.t }
  [@@deriving eq, ord, show]
  let mk dom cod = { dom; cod }
end

module Decl : sig
  type t = { op : Op.t; ar : Ar.t }
  [@@deriving eq, ord, show]
  val source : t -> Tm.t list
  val target : t -> Tm.t
end = struct
  [@@@warning "-39"]
  open Ar
  type t = { op : Op.t; ar : Ar.t }
  [@@deriving eq, ord, show]
  let source tm = tm.ar.dom
  let target tm = tm.ar.cod
end

module Sign : sig
  type t = Decl.t list
  [@@deriving eq, ord, show]
  val find : t -> Op.t -> Ar.t option
end = struct
  [@@@warning "-39"]
  open Decl
  type t = Decl.t list
  [@@deriving eq, ord, show]
  let rec find gamma theta =
    match gamma with
    | [] ->
      None
    | { op; ar } :: _ when Op.equal op theta ->
      Some ar
    | _ :: gamma ->
      find gamma theta
end

module Computad : sig
  type t = Sign.t list
  [@@deriving eq, ord, show]
  val find : t -> Op.t -> Ar.t option
end = struct
  [@@@warning "-39"]
  type t = Sign.t list
  [@@deriving eq, ord, show]
  let rec find gamma op =
    match gamma with
    | [] ->
      None
    | sigma :: gamma ->
      match Sign.find sigma op with
      | None ->
        find gamma op
      | arity ->
        arity
end

module Examples = struct
  open Ar
  open Decl
  let star : Op.t = "*"

  let types : Sign.t =
    let delta = [] in
    let delta = {
      op = "bool";
      ar = { dom = []; cod = Tm.op star };
    } :: delta in
    delta
  let bool : Tm.t = Tm.op "bool"

  let terms : Sign.t =
    let delta = [] in
    let delta = {
      op = "ff";
      ar = Ar.mk [] bool;
    } :: delta in
    let delta = {
      op = "tt";
      ar = Ar.mk [] bool;
    } :: delta in
    let delta = {
      op = "con";
      ar = Ar.mk [ bool; bool ] bool;
    } :: delta in
    delta
  let ff = Tm.op "ff"
  let tt = Tm.op "tt"
  let con = Tm.op "con"

  let rules : Sign.t =
    let delta = [] in
    let delta = {
      op = "con-ff-ff";
      ar = Ar.mk [ Tm.ap "con" [ ff; ff ] ] ff;
    } :: delta in
    let delta = {
      op = "con-ff-tt";
      ar = Ar.mk [ Tm.ap "con" [ ff; tt ] ] ff;
    } :: delta in
    let delta = {
      op = "con-tt-ff";
      ar = Ar.mk [ Tm.ap "con" [ tt; ff ] ] ff;
    } :: delta in
    let delta = {
      op = "con-tt-tt";
      ar = Ar.mk [ Tm.ap "con" [ tt; tt ] ] tt;
    } :: delta in
    delta
  let con_ff_ff = Tm.op "con-ff-ff"
  let con_ff_tt = Tm.op "con-ff-tt"
  let con_tt_ff = Tm.op "con-tt-ff"
  let con_tt_tt = Tm.op "con-tt-tt"

  let computad : Computad.t = [ types; terms; rules ]
  let () = Printf.printf "%s\n" @@ Computad.show computad
end