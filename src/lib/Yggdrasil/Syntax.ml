module Term = struct
  module Dim = struct
    type t = int
    [@@deriving eq, ord, show]
  end

  module Op = struct
    type t = string
    [@@deriving eq, ord, show]
    let pp = Format.pp_print_string
    let show op = op
  end

  module rec Node : sig
    type t =
      | Op of Op.t
      | Rho of Rose.t
    [@@deriving eq, ord, show]
    val node : (Format.formatter -> Rose.t -> unit) -> (Format.formatter -> Node.t -> unit)
    val op : Op.t -> t
    val rho : Node.t -> Bouquet.t -> t
  end = struct
    open Format

    type t =
      | Op of Op.t
      | Rho of Rose.t
    [@@deriving eq, ord]

    let node pp_rose fmt tm =
      match tm with
      | Op op ->
        fprintf fmt "%a"
          (pp_print_string) op
      | Rho rho ->
        fprintf fmt "%a"
          (pp_rose) rho

    let pp =
      node Rose.pp

    let show node =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp fmt node
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer

    let op head =
      Op head

    let rho head spine =
      Rho (Data.Rose.Fork (head, spine))
  end

  and Rose : sig
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord, show]
    val rho : Rose.t -> Bouquet.t -> Rose.t
    val op : Op.t -> Bouquet.t -> Rose.t
  end = struct
    open Format
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord]

    let rec pp fmt (Data.Rose.Fork (hd, sp)) =
      let pp_sep fmt () = fprintf fmt "@ " in
      match sp with
      | [] ->
        fprintf fmt "%a"
          (Node.pp) hd
      | _ ->
        fprintf fmt "@[<2>(%a@ %a)@]"
          (Node.pp) hd
          (pp_print_list ~pp_sep pp) sp

    let show rose =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp fmt rose
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer

    let rho head spine =
      Data.Rose.Fork (Node.Rho head, spine)

    let op head spine =
      Data.Rose.Fork (Node.Op head, spine)
  end

  and Bouquet : sig
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord, show]
  end = struct
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord, show]
  end

  module Arity = struct
    open Format

    let rec pp fmt (Data.Rose.Fork (hd, sp)) =
      let pp_sep fmt () = fprintf fmt "@ " in
      match sp with
      | [] ->
        fprintf fmt "%a"
          (Node.node pp) hd
      | tm :: [] ->
        fprintf fmt "@[<1>(->@ %a@ %a)@]"
          (pp) tm
          (Node.node pp) hd
      | _ ->
        fprintf fmt "@[<1>(->@ [%a]@ %a)@]"
          (pp_print_list ~pp_sep pp) sp
          (Node.node pp) hd

    let show arity =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp fmt arity
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer

    let pt cod =
      Data.Rose.pure cod
  end

  module Cell = struct
    type t = {
      name : Op.t;
      arity : Rose.t;
    } [@@deriving eq, ord, show]
  end

  let ( *@ ) head spine =
    Node.Rho (Data.Rose.Fork (head, spine))

  let ( --> ) dom cod =
    Data.Rose.Fork (cod, dom)

  let ( <: ) name arity =
    { Cell.name; arity }

  let ( <! ) name cod =
    { Cell.name; arity = Arity.pt cod }
end
