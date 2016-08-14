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
  val ( *@ ) : Op.t -> Sp.t -> t
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
  let ( *@ ) = ap
end

module Ar = struct
  [@@@warning "-39"]
  type t = { dom : Tm.t list; cod : Tm.t }
  [@@deriving eq, ord, show]
  let mk dom cod = { dom; cod }
  let ( --> ) = mk
end

module Decl : sig
  type t = { op : Op.t; ar : Ar.t }
  [@@deriving eq, ord, show]
  val source : t -> Tm.t list
  val target : t -> Tm.t
  val ( <: ) : Op.t -> Ar.t -> t
  val ( <! ) : Op.t -> Tm.t -> t
end = struct
  [@@@warning "-39"]
  open Ar
  type t = { op : Op.t; ar : Ar.t }
  [@@deriving eq, ord, show]
  let source tm = tm.ar.dom
  let target tm = tm.ar.cod
  let ( <: ) op ar = { op; ar }
  let ( <! ) op cod = { op; ar = { dom = []; cod }}
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
  open Tm

  let star = op "*"

  let types : Sign.t =
    ("bool" <! star) :: []
  let bool = op "bool"

  let terms : Sign.t =
    ("ff" <! bool) ::
    ("tt" <! bool) ::
    ("con" <: [ bool; bool ] --> bool) :: []
  let ff = op "ff"
  let tt = op "tt"
  let con = op "con"

  let rules : Sign.t =
    ("con-ff-ff" <: [ "con" *@ [ ff; ff ] ] --> ff) ::
    ("con-ff-tt" <: [ "con" *@ [ ff; tt ] ] --> ff) ::
    ("con-tt-ff" <: [ "con" *@ [ tt; ff ] ] --> ff) ::
    ("con-tt-tt" <: [ "con" *@ [ tt; tt ] ] --> tt) :: []
  let con_ff_ff = op "con-ff-ff"
  let con_ff_tt = op "con-ff-tt"
  let con_tt_ff = op "con-tt-ff"
  let con_tt_tt = op "con-tt-tt"

  let computad : Computad.t = [ types; terms; rules ]
  let () = Printf.printf "%s\n" @@ Computad.show computad
end