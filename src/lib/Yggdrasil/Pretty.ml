open Data.Rose
open Format
open Syntax

type name = string
type env = name list * name Stream.t

let pretty_suffix : int -> string =
  let subscript = function
    | 0 -> "₀"
    | 1 -> "₁"
    | 2 -> "₂"
    | 3 -> "₃"
    | 4 -> "₄"
    | 5 -> "₅"
    | 6 -> "₆"
    | 7 -> "₇"
    | 8 -> "₈"
    | 9 -> "₉"
    | _ -> failwith "bad subscript" in
  let rec go acc = function
    | 0 -> acc
    | n -> go (subscript (n mod 10) ^ acc) (n / 10) in
  go ""

let gen_name : unit -> (int -> name option) =
  let offset = 97 in
  let width = 26 in
  fun () i ->
    let code = (i mod width) + offset in
    let char = Char.chr code in
    let prime = i / width in
    let suffix = pretty_suffix (prime) in
    let name = Char.escaped char ^ suffix in
    Some name

let supply : unit -> env =
  fun () -> ([], Stream.from @@ gen_name ())

let node rose ppf tm =
  let open Term in
  match tm with
  | Node.Op op ->
    fprintf ppf "%a"
      (pp_print_string) op
  | Node.Rho rho ->
    fprintf ppf "%a"
      (rose) rho

let rec arity ppf (Fork (hd, sp)) =
  let pp_sep fmt () = fprintf fmt "@ " in
  match sp with
  | [] ->
    fprintf ppf "%a"
      (node arity) hd
  | tm :: [] ->
    fprintf ppf "@[<1>(->@ %a@ %a)@]"
      (arity) tm
      (node arity) hd
  | _ ->
    fprintf ppf "@[<1>(->@ [%a]@ %a)@]"
      (pp_print_list ~pp_sep arity) sp
      (node arity) hd

let rec rose_term ppf (Fork (hd, sp)) =
  let pp_sep fmt () = fprintf fmt "@ " in
  match sp with
  | [] ->
    fprintf ppf "%a"
      (node rose_term) hd
  | _ ->
    fprintf ppf "@[<2>(%a@ %a)@]"
      (node rose_term) hd
      (pp_print_list ~pp_sep rose_term) sp

let term  = node rose_term
