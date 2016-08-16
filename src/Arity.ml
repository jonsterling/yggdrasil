type t = {
  dom : t list;
  cod : Syntax.Term.t;
} [@@deriving eq, ord]

let rec pp fmt ar =
  let open Format in
  match ar with
  | { dom = []; cod } ->
    fprintf fmt "%a"
      Syntax.Term.pp cod
  | { dom = [ dom ]; cod } ->
    fprintf fmt "%a@,@ @[->@ %a@]"
      pp dom
      Syntax.Term.pp cod
  | { dom; cod } ->
    let sep fmt () =
      fprintf fmt "@,,@ " in
    fprintf fmt "[%a]@,@ @[->@ %a@]"
      (pp_print_list ~pp_sep:sep pp) dom
      Syntax.Term.pp cod

let show = Pretty.show pp

let ( --> ) dom cod =
  { dom; cod }

let pt cod =
  { dom = []; cod }
