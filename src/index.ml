module Dm = struct
  type t = int
  [@@deriving eq, ord, show]
end

module Op = struct
  type t = string [@printer fun fmt -> Format.fprintf fmt "%s"]
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
    [@@deriving eq, ord]

  let ap op sp =
    Ap { op; sp }

  let pp fmt = function
    | Ap { op; sp = [] } ->
      Format.fprintf fmt "%a"
        Op.pp op
    | Ap { op; sp } ->
      Format.fprintf fmt "%a %a"
        Op.pp op
        Sp.pp sp
    | Id { tp } ->
      Format.fprintf fmt "id[%a]"
        Tp.pp tp

  let show tm =
    let buffer = Buffer.create 0 in
    let fmt = Format.formatter_of_buffer buffer in
    let () = pp fmt tm in
    let () = Format.pp_print_flush fmt () in
    Buffer.contents buffer

  let op op =
    ap op []
  let ( *@ ) =
    ap
end

module Ar : sig
  type t = {
    dom : Tm.t list;
    cod : Tm.t;
  }
  [@@deriving eq, ord, show]
  val ( --> ) : Tm.t list -> Tm.t -> t
end = struct
  type t = {
    dom : Tm.t list;
    cod : Tm.t;
  }
  [@@deriving eq, ord]

  let pp fmt = function
    | { dom = [ dom ]; cod } ->
      Format.fprintf fmt "%a -> %a"
        Tm.pp dom
        Tm.pp cod
    | { dom; cod } ->
      Format.fprintf fmt "%a -> %a"
        Sp.pp dom
        Tm.pp cod

  let show ar =
    let buffer = Buffer.create 0 in
    let fmt = Format.formatter_of_buffer buffer in
    let () = pp fmt ar in
    let () = Format.pp_print_flush fmt () in
    Buffer.contents buffer

  let ( --> ) dom cod =
    { dom; cod }
end

module Decl : sig
  type t = {
    op : Op.t;
    ar : Ar.t;
  }
  [@@deriving eq, ord, show]
  val source : t -> Tm.t list
  val target : t -> Tm.t
  val ( <: ) : Op.t -> Ar.t -> t
  val ( <! ) : Op.t -> Tm.t -> t
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
  type t [@@deriving show]
  val init : t
  val bind : t -> Dm.t -> Decl.t -> t
  val arity : t -> Op.t -> Ar.t
  val dimen : t -> Op.t -> Dm.t
  val normSp : t -> Sp.t -> Sp.t
  val normTm : t -> Tm.t -> Tm.t
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

  module Trie = struct
    include CCTrie.MakeList(struct
      type t = Tm.t
      let compare = Tm.compare
    end)
  end

  module Pr : sig
    type t = (Tm.t * Op.t) Trie.t
    [@@deriving show]
  end = struct
    type pair = Tm.t list * (Tm.t * Op.t)
    [@@deriving show]
    let print fmt trie = CCList.print pp_pair fmt (Trie.to_list trie)
    type t = (Tm.t * Op.t) Trie.t [@printer print]
    [@@deriving show]
  end

  type t = {
    ars : (Ar.t Map.t [@printer Map.print ~arrow:" := " Op.pp Ar.pp]);
    dms : (Dm.t Map.t [@printer Map.print ~arrow:" := " Op.pp Dm.pp]);
    prs : (Pr.t Map.t [@printer Map.print ~arrow:" := " Op.pp Pr.pp]);
  } [@@deriving show]

  let init = {
    ars = Map.empty;
    dms = Map.empty;
    prs = Map.empty;
  }

  let bind sg dm { op; ar } = {
    dms = Map.add op dm sg.dms;
    ars = Map.add op ar sg.ars;
    prs = match [@warning "-4"] ar with
      | { dom = [ Ap { op = theta; sp } ]; _ } when dm > 1 ->
        let update = function
          | None ->
            Some (Trie.add sp (ar.cod, op) Trie.empty)
          | Some pre ->
            Some (Trie.add sp (ar.cod, op) pre) in
        Map.update theta update sg.prs
      | _ ->
        sg.prs
  }

  let arity sg op =
    Map.find op sg.ars

  let dimen sg op =
    Map.find op sg.dms

  let rec normTm sg tm =
    match [@warning "-4"] tm with
    | Ap { op; sp } when not (CCList.is_empty sp) ->
      let sp = normSp sg sp in
      let prs = Map.find op sg.prs in
      let (res, _) = Trie.find_exn sp prs in
      res
    | _ -> tm
  and normSp sg sp =
    CCList.map (normTm sg) sp
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
    bind sg 0 ("bool" <! star)
  let bool =
    op "bool"

  let sg =
    bind sg 1 ("ff" <! bool)
  let sg =
    bind sg 1 ("tt" <! bool)
  let sg =
    bind sg 1 ("not" <: [ bool ] --> bool)
  let sg =
    bind sg 1 ("con" <: [ bool; bool ] --> bool)
  let ff =
    op "ff"
  let tt =
    op "tt"
  let not =
    op "not"
  let con =
    op "con"

  let sg =
    bind sg 2 ("not-ff" <: [ "not" *@ [ ff ] ] --> tt)
  let sg =
    bind sg 2 ("not-tt" <: [ "not" *@ [ tt ] ] --> ff)
  let not_ff =
    op "not-ff"
  let not_tt =
    op "not-tt"

  let sg =
    bind sg 2 ("con-ff-ff" <: [ "con" *@ [ ff; ff ] ] --> ff)
  let sg =
    bind sg 2 ("con-ff-tt" <: [ "con" *@ [ ff; tt ] ] --> ff)
  let sg =
    bind sg 2 ("con-tt-ff" <: [ "con" *@ [ tt; ff ] ] --> ff)
  let sg =
    bind sg 2 ("con-tt-tt" <: [ "con" *@ [ tt; tt ] ] --> tt)
  let con_ff_ff =
    op "con-ff-ff"
  let con_ff_tt =
    op "con-ff-tt"
  let con_tt_ff =
    op "con-tt-ff"
  let con_tt_tt =
    op "con-tt-tt"

  let normalize term =
    let norm = Computad.normTm sg term in
    Printf.printf "term: %s\nnorm: %s\n\n"
      (Tm.show term)
      (Tm.show norm)

  let () =
    Printf.printf "%s\n\n"
    @@ Computad.show sg

  let () =
    normalize @@ "not" *@ [ ff ]
  let () =
    normalize @@ "not" *@ [ tt ]
  let () =
    normalize @@ "con" *@ [ ff; ff ]
  let () =
    normalize @@ "con" *@ [ "con" *@ [ tt; tt ]; ff ]
  let () =
    normalize @@ "con" *@ [ "con" *@ [ tt; tt ]; tt ]
end