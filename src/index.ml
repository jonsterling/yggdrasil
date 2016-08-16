module Util : sig
  val show : (Format.formatter -> 'a -> unit) -> ('a -> string)
end = struct
  let show pp_obj obj =
    let buffer = Buffer.create 0 in
    let fmt = Format.formatter_of_buffer buffer in
    pp_obj fmt obj;
    Format.pp_print_flush fmt ();
    Buffer.contents buffer
end

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
  [@@deriving eq, ord]

  let pp fmt sp =
    let open Format in
    let sep fmt () =
      fprintf fmt "@,,@ " in
    fprintf fmt "[@[<2>%a@]]"
      (pp_print_list ~pp_sep:sep Tm.pp) sp

  let show = Util.show pp
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
  [@@deriving eq, ord]

  let ap op sp =
    Ap { op; sp }

  let pp fmt = function
    | Ap { op; sp = [] } ->
      Format.fprintf fmt "%a"
        Op.pp op
    | Ap { op; sp = [ tm ] } ->
      Format.fprintf fmt "%a@ %a"
        Op.pp op
        Tm.pp tm
    | Ap { op; sp } ->
      Format.fprintf fmt "%a@ %a"
        Op.pp op
        Sp.pp sp
    | Id { tp } ->
      Format.fprintf fmt "id[%a]"
        Tp.pp tp

  let show = Util.show pp

  let op op =
    ap op []
  let ( *@ ) =
    ap
end

module Ar : sig
  type t = {
    dom : Sp.t;
    cod : Tm.t;
  } [@@deriving eq, ord, show]
  val ( --> ) : Sp.t -> Tm.t -> t
end = struct
  type t = {
    dom : Sp.t;
    cod : Tm.t;
  } [@@deriving eq, ord]

  let pp fmt = function
    | { dom = []; cod } ->
      Format.fprintf fmt "%a"
        Tm.pp cod
    | { dom = [ dom ]; cod } ->
      Format.fprintf fmt "%a@ ->@ %a"
        Tm.pp dom
        Tm.pp cod
    | { dom; cod } ->
      Format.fprintf fmt "%a@ ->@ %a"
        Sp.pp dom
        Tm.pp cod

  let show = Util.show pp

  let ( --> ) dom cod =
    { dom; cod }
end

module Decl : sig
  type t = {
    op : Op.t;
    ar : Ar.t;
  } [@@deriving eq, ord, show]
  val source : t -> Sp.t
  val target : t -> Tm.t
  val ( <: ) : Op.t -> Ar.t -> t
  val ( <! ) : Op.t -> Tm.t -> t
end = struct
  open Ar

  type t = {
    op : Op.t;
    ar : Ar.t;
  } [@@deriving eq, ord, show]

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

    let print_ops pp_key pp_elt fmt map : unit =
      let open Format in
      let assoc fmt (key, elt) =
        fprintf fmt "@[<2>%a@ :@ %a@]"
          pp_key key
          pp_elt elt in
      let list =
        List.fast_sort
          (fun (lhs, _) (rhs, _) -> Op.compare lhs rhs)
          (to_list map) in
      fprintf fmt "@[<v 2>@[@  @]%a@,@]"
        (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list

    let print_rls pp_key pp_elt fmt map : unit =
      let open Format in
      let assoc  fmt (key, elt) =
        fprintf fmt "@[<v 2>%a@[@ @][@,%a@,]@]"
          pp_key key
          pp_elt elt in
      let list = List.fast_sort (fun (lhs, _) (rhs, _) -> Op.compare lhs rhs) @@ to_list map in
      fprintf fmt "@[<v 2>@[@  @]%a@,@]"
        (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
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
    let print fmt trie =
      let open Format in
      let list =
        List.fast_sort
          (fun (_, (_, lhs)) (_, (_, rhs)) -> Op.compare lhs rhs)
          (Trie.to_list trie) in
      let assoc fmt = function
        | ([ dom ], (cod, op)) ->
          fprintf fmt "@[%a@ :@ %a@ ->@ %a@]"
            Op.pp op
            Tm.pp dom
            Tm.pp cod
        | (dom, (cod, op)) ->
          fprintf fmt "@[%a@ :@ %a@ ->@ %a@]"
            Op.pp op
            Sp.pp dom
            Tm.pp cod in
      fprintf fmt "@[<v>%a@]"
        (CCFormat.list ~start:"" ~sep:"" ~stop:"" assoc) list
    type t = (Tm.t * Op.t) Trie.t [@printer print]
    [@@deriving show]
  end

  type t = {
    ars : (Ar.t Map.t [@printer Map.print_ops Op.pp Ar.pp]);
    dms : (Dm.t Map.t [@printer Map.print_ops Op.pp Dm.pp]);
    prs : (Pr.t Map.t [@printer Map.print_rls Op.pp Pr.pp]);
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
    | Ap { op; sp } ->
      let sp = normSp sg sp in
      begin
        (* Try to look up the normalization rule. For now we assume that if
           the term is well typed but the lookup fails then there is an
           implicit loop. This allows cells like `ff` to normalize without
           us having to keep track of unnecessary data. *)
        try
          let prs = Map.find op sg.prs in
          let (res, _) = Trie.find_exn sp prs in
          res
        with Not_found -> tm
      end
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
    op "type"

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

  let sg =
    bind sg 0 ("circle" <! star)
  let circle =
    op "circle"

  let sg =
    bind sg 1 ("base" <! circle)
  let base =
    op "base"

  let sg =
    bind sg 2 ("loop" <: [ base ] --> base )
  let loop =
    op "loop"

  let sg =
    bind sg 0 ("interval" <! star)
  let interval =
    op "interval"

  let sg =
    bind sg 1 ("zero" <! interval)
  let sg =
    bind sg 1 ("one" <! interval)
  let zero =
    op "zero"
  let one =
    op "one"

  let sg =
    bind sg 2 ("segment" <: [ zero ] --> one )
  let segment =
    op "segment"

  let normalize term =
    let norm = Computad.normTm sg term in
    Format.fprintf Format.std_formatter "@.\n@[<hv>term:@ %a\nnorm:@ %a@]"
      Tm.pp term
      Tm.pp norm

  let () =
    Format.fprintf Format.std_formatter "%a"
      Computad.pp sg

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
  let () =
    normalize @@ "con" *@ [ "con" *@ [ tt; tt ]; "not" *@ [ ff ] ]
  let () =
    normalize @@ base
  let () =
    normalize @@ zero
end
