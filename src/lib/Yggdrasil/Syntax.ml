module Term = struct
  open Data.Rose
  open Format

  module Dimension = struct
    type t = int
    [@@deriving eq, ord, show]
  end

  module Operator = struct
    type t = string [@show.printer pp_print_string]
    [@@deriving eq, ord, show]
  end

  module Var = struct
    type t = string [@show.printer pp_print_string]
    [@@deriving eq, ord, show]
  end

  module rec Bind : sig
    type t = Var.t * Rose.t
    [@@deriving eq, ord, show]
  end = struct
    type t = Var.t * Rose.t
    [@@deriving eq, ord]

    let pp fmt (x, ar) =
      fprintf fmt "(∂@ %a@ %a)"
        (pp_print_string) x
        (Rose.pp 0) ar

    let show bind =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp fmt bind
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer
  end

  and Node : sig
    type t =
      | Ap of Rose.t
      | Lm of Bind.t list * t
      | Op of Operator.t
      | Var of Var.t
    [@@deriving eq, ord]
    val pp : Dimension.t -> formatter -> t -> unit
    val show : Dimension.t -> t -> string
    val node : (formatter -> Rose.t -> unit) -> (formatter -> Node.t -> unit)
    val ap : Node.t -> Bouquet.t -> t
    val op : Operator.t -> t
  end = struct

    type t =
      | Ap of Rose.t
      | Lm of Bind.t list * t
      | Op of Operator.t
      | Var of Var.t
    [@@deriving eq, ord]

    let rec node pp_rose fmt tm =
      match tm with
      | Ap rho ->
        fprintf fmt "%a"
          (pp_rose) rho
      | Lm ([x], e) ->
        fprintf fmt "@[<2>(λ@ %a@ @[<2>%a@])@]"
          (Bind.pp) x
          (node pp_rose) e
      | Lm (xs, e) ->
        let pp_sep fmt () = fprintf fmt "@ " in
        fprintf fmt "@[<2>(λ@ [%a]@ @[<2>%a@])@]"
          (pp_print_list ~pp_sep Bind.pp) xs
          (node pp_rose) e
      | Op theta ->
        fprintf fmt "%a"
          (Operator.pp) theta
      | Var x ->
        fprintf fmt "%a"
          (Var.pp) x

    let pp dim =
      node @@ Rose.pp dim

    let show dim node =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp dim fmt node
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer

    let ap head spine =
      Ap (Fork (head, spine))

    let op head =
      Op head
  end

  and Rose : sig
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord]
    val pp : Dimension.t -> formatter -> t -> unit
    val show : Dimension.t -> t -> string
    val ap : Rose.t -> Bouquet.t -> Rose.t
    val op : Operator.t -> Bouquet.t -> Rose.t
  end = struct
    type t = Node.t Data.Rose.t
    [@@deriving eq, ord]

    let rec pp dim fmt (Data.Rose.Fork (hd, sp)) =
      let pp_sep fmt () = fprintf fmt "@ " in
      match sp with
      | [] ->
        fprintf fmt "%a"
          (Node.pp dim) hd
      | _ when dim < 2 ->
        fprintf fmt "@[<2>(->@ %a@ %a)@]"
          (Node.pp dim) hd
          (pp_print_list ~pp_sep @@ pp dim) sp
      | _ ->
        fprintf fmt "@[<2>(%a@ %a)@]"
          (Node.pp dim) hd
          (pp_print_list ~pp_sep @@ pp dim) sp

    let show dim rose =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp dim fmt rose
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer

    let ap head spine =
      Fork (Node.Ap head, spine)

    let op head spine =
      Fork (Node.Op head, spine)
  end

  and Bouquet : sig
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord]
  end = struct
    type t = Node.t Data.Rose.Bouquet.t
    [@@deriving eq, ord]
  end

  module Arity = struct
    let rec pp dim fmt (Data.Rose.Fork (hd, sp)) =
      let pp_sep fmt () = fprintf fmt "@ " in
      match sp with
      | [] ->
        fprintf fmt "%a"
          (Node.node @@ pp dim) hd
      | tm :: [] ->
        fprintf fmt "@[<1>(->@ %a@ %a)@]"
          (Rose.pp dim) tm
          (Node.pp dim) hd
      | _ ->
        fprintf fmt "@[<1>(->@ [%a]@ %a)@]"
          (pp_print_list ~pp_sep @@ Rose.pp dim) sp
          (Node.pp dim) hd

    let show dim arity =
      let buffer = Buffer.create 0 in
      let fmt = formatter_of_buffer buffer in
      pp dim fmt arity
    ; pp_print_flush fmt ()
    ; Buffer.contents buffer

    let pt cod =
      Data.Rose.pure cod
  end

  module Cell = struct
    type t = {
      name : Operator.t;
      arity : Rose.t;
    } [@@deriving eq, ord]
  end

  let ( *@ ) head spine =
    Node.Ap (Fork (head, spine))

  let ( --> ) dom cod =
    Fork (cod, dom)

  let ( <: ) name arity =
    { Cell.name; arity }

  let ( <! ) name cod =
    { Cell.name; arity = Arity.pt cod }
end
