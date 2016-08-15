module Dm = struct
  type t = int
  [@@deriving eq, ord, show]
end

module Op = struct
  type t = string
  [@@deriving eq, ord, show]
end

module Tp = struct
  type t = string
  [@@deriving eq, ord, show]
end

module rec Sp : sig
  type t = Tm.t list
  [@@deriving eq, ord, show]
end = struct
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
  type t =
    | Id of { tp : Tp.t }
    | Ap of { op : Op.t; sp : Sp.t }
  [@@deriving eq, ord, show]

  let ap op sp =
    Ap { op; sp }
  let op op =
    ap op []
  let ( *@ ) =
    ap
end

module Ar : sig
  type t = {
    dom : Tm.t list;
    cod : Tm.t list;
    inv : bool;
  }
  [@@deriving eq, ord, show]
  val ( --> ) : Tm.t list -> Tm.t list -> t
  val ( -=> ) : Tm.t list -> Tm.t list -> t
end = struct
  type t = {
    dom : Tm.t list;
    cod : Tm.t list;
    inv : bool;
  }
  [@@deriving eq, ord, show]

  let ( --> ) dom cod =
    { dom; cod; inv = false }
  let ( -=> ) dom cod =
    { dom; cod; inv = true }
end

module Decl : sig
  type t = {
    op : Op.t;
    ar : Ar.t;
  }
  [@@deriving eq, ord, show]
  val source : t -> Tm.t list
  val target : t -> Tm.t list
  val ( <: ) : Op.t -> Ar.t -> t
  val ( <! ) : Op.t -> Tm.t list -> t
end = struct
  open Ar

  type t = {
    op : Op.t;
    ar : Ar.t;
  }
  [@@deriving eq, ord, show]

  let source tm =
    tm.ar.dom
  let target tm =
    tm.ar.cod
  let ( <: ) op ar =
    { op; ar }
  let ( <! ) op cod =
    { op; ar = [] --> cod }
end

module Computad : sig
  type t
  [@@deriving show]
  val init : t
  val bind : t -> Dm.t -> Decl.t -> t
  val arity : t -> Op.t -> Ar.t
  val dimen : t -> Op.t -> Dm.t
end = struct
  open Ar
  open Decl
  open Tm

  module Map = struct
    include CCMap.Make(struct
        type t = Op.t
        let compare = Op.compare
      end)
  end

  module Set = struct
    include CCSet.Make(struct
        type t = Op.t
        let compare = Op.compare
      end)
  end

  type t = {
    ars :  (Ar.t Map.t [@printer Map.print ~arrow:" := " Op.pp Ar.pp]);
    dms :  (Dm.t Map.t [@printer Map.print ~arrow:" := " Op.pp Dm.pp]);
    rls : (Set.t Map.t [@printer Map.print ~arrow:" := " Op.pp (Set.print Op.pp)]);
  }
  [@@deriving show]

  let init = {
    ars = Map.empty;
    dms = Map.empty;
    rls = Map.empty;
  }
  let bindCell sg dm { op; ar } = {
    dms = Map.add op dm sg.dms;
    ars = Map.add op ar sg.ars;
    rls = match [@warning "-4"] ar with
      | { dom = [ Ap { op = theta; _ } ]; _ } when dm > 1 ->
        let update = function
          | None ->
            Some (Set.add op Set.empty)
          | Some rls ->
            Some (Set.add op rls) in
        Map.update theta update sg.rls
      | _ ->
        sg.rls
  }
  let bind sg dm de =
    let sg = bindCell sg dm de in
    if de.ar.inv then
      bindCell sg dm {
        op = "inv-" ^ de.op;
        ar = {
          de.ar with
          dom = de.ar.cod;
          cod = de.ar.dom;
        }
      }
    else
      sg
  let arity sg op =
    Map.find op sg.ars
  let dimen sg op =
    Map.find op sg.dms
end

module Examples = struct
  open Ar
  open Computad
  open Decl
  open Tm

  let sg =
    init
  let star =
    op "*"

  let sg =
    bind sg 0 ("bool" <! [ star ])
  let bool =
    op "bool"

  let sg =
    bind sg 1 ("ff" <! [ bool ])
  let sg =
    bind sg 1 ("tt" <! [ bool ])
  let sg =
    bind sg 1 ("not" <: [ bool ] --> [ bool ])
  let sg =
    bind sg 1 ("con" <: [ bool; bool ] --> [ bool ])
  let ff =
    op "ff"
  let tt =
    op "tt"
  let con =
    op "con"

  let sg =
    bind sg 2 ("not-ff" <: [ "not" *@ [ ff ] ] --> [ tt ])
  let sg =
    bind sg 2 ("not-tt" <: [ "not" *@ [ tt ] ] --> [ ff ])
  let not_ff =
    op "not-ff"
  let not_tt =
    op "not-tt"

  let sg =
    bind sg 2 ("con-ff-ff" <: [ "con" *@ [ ff; ff ] ] -=> [ ff ])
  let sg =
    bind sg 2 ("con-ff-tt" <: [ "con" *@ [ ff; tt ] ] -=> [ ff ])
  let sg =
    bind sg 2 ("con-tt-ff" <: [ "con" *@ [ tt; ff ] ] -=> [ ff ])
  let sg =
    bind sg 2 ("con-tt-tt" <: [ "con" *@ [ tt; tt ] ] -=> [ tt ])
  let con_ff_ff =
    op "con-ff-ff"
  let con_ff_tt =
    op "con-ff-tt"
  let con_tt_ff =
    op "con-tt-ff"
  let con_tt_tt =
    op "con-tt-tt"

  let () =
    Printf.printf "%s\n"
    @@ Computad.show sg
end