open Format

module Endo = struct
  type 'a t = 'a -> 'a
end

module Syntax = struct
  module Var = struct
    type t = int
  end
  module Term = struct
    type t =
      | App of t * t
      | Lam of t
      | Var of Var.t
  end
  module Sub = struct
    type 'a t =
      | Cmp of 'a t * 'a t
      | Dot of 'a * 'a t
      | Id
      | Shift

    let map f sgm =
      let rec go = function
        | Cmp (sgm0, sgm1) -> Cmp (go sgm0, go sgm1)
        | Dot (a, sgm) -> Dot (f a, go sgm)
        | Id -> Id
        | Shift -> Shift in
      go sgm

    let rec apply sgm e =
      match (sgm, e) with
      | (sgm, Term.App (e0, e1)) -> Term.App (apply sgm e0, apply sgm e1)
      | (sgm, Term.Lam e) -> Term.Lam (apply (Dot (Term.Var 0, Cmp (sgm, Shift))) e)
      | (Dot (e, _), Term.Var 0) -> e
      | (Dot (_, sgm), Term.Var i) -> apply sgm (Term.Var (i - 1))
      | (Id, Term.Var i) -> Term.Var i
      | (Shift, Term.Var i) -> Term.Var (i + 1)
      | (Cmp (rho, sgm), e) -> apply sgm (apply rho e)
  end
end

module Zip = struct
  open Syntax
  type 'a t =
    | App0 of 'a t * 'a
    | App1 of 'a * 'a t
    | Halt
    | Lam of 'a t

  let map f sgm =
    let rec go = function
      | App0 (zip, e1) -> App0 (go zip, f e1)
      | App1 (e0, zip) -> App1 (f e0, go zip)
      | Halt -> Halt
      | Lam zip -> Lam (go zip)
    in
    go sgm

  let rec apply zip acc = match zip with
    | App0 (zip, e1) -> apply zip @@ Term.App (acc, e1)
    | App1 (e0, zip) -> apply zip @@ Term.App (e0, acc)
    | Halt -> acc
    | Lam zip -> apply zip @@ Term.Lam acc
end

module Clo = struct
  open Syntax
  type t =
    | Clo of Term.t * t Sub.t
  let rec from (Clo (term, sgm)) = Sub.apply (Sub.map from sgm) term;
end

module Pretty = struct
  module Delim = struct
    type t = string
    let pp prev next fmt token = if (prev < next) then fprintf fmt "%s" token
  end
  module Prec = struct
    type t = int
    open Syntax.Term
    let calc = function
      | App (_, _) -> 1
      | Lam _ -> 2
      | Var _ -> 0
  end
  module Name = struct
    type t = string
    let suffix =
      let script = function
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
        | n -> go (script (n mod 10) ^ acc) (n / 10) in
      go ""

    let gen =
      let offset = 97 in
      let width = 26 in
      fun () i ->
        let code = i mod width + offset in
        let char = Char.chr code in
        let prime = i / width in
        let suffix = suffix prime in
        let name = Char.escaped char ^ suffix in
        Some name
  end

  module Env = struct
    type t = {
      used : Name.t list;
      rest : Name.t Stream.t;
    }
    let mk () =
      let used = [] in
      let rest = Stream.from @@ Name.gen () in
      { used; rest }
  end

  type 'a printer = Env.t -> Prec.t -> formatter -> 'a -> unit

  module Term = struct
    open Syntax.Term
    let rec pp ({ Env.used = used; rest } as env) prev fmt e =
      let next = Prec.calc e in
      match e with
      | App (e0, e1) ->
        fprintf fmt "@[%a%a@ %a%a@]"
          (Delim.pp prev next) "("
          (pp env 1) e0
          (pp env 0) e1
          (Delim.pp prev next) ")"
      | Lam e ->
        let name = Stream.next rest in
        let env = { env with Env.used = name::used } in
        fprintf fmt "%aλ%a.%a%a"
          (Delim.pp prev next) "("
          (Fmt.string) name
          (pp env next) e
          (Delim.pp prev next) ")"
      | Var index ->
        fprintf fmt "%s" @@ try List.nth used index with
        | _ -> "#" ^ string_of_int index
  end

  module Sub = struct
    open Syntax.Sub
    let rec pp pp_elem env prev fmt = function
      | Cmp (sgm1, sgm0) ->
        fprintf fmt "@[%a;@ %a@]"
          (pp pp_elem env prev) sgm1
          (pp pp_elem env prev) sgm0
      | Dot (e, sgm) ->
        fprintf fmt "@[%a@ ·@ %a@]"
          (pp_elem env prev) e
          (pp pp_elem env prev) sgm
      | Id ->
        fprintf fmt "ι"
      | Shift ->
        fprintf fmt "↑"
  end

  module Clo = struct
    let rec pp env prev fmt (Clo.Clo (e, sgm)) =
      let next = Prec.calc e in
      fprintf fmt "@[%a%a%a[%a]@]"
        (Delim.pp prev next) "("
        (Term.pp env next) e
        (Delim.pp prev next) ")"
        (Sub.pp pp env next) sgm
  end

  module Zip = struct
    open Zip
    let rec pp pp_elem env prev fmt = function
      | App0 (zip, elem) ->
        fprintf fmt "inl@[<v -1>⟨@,%a@,%a⟩@]"
          (pp pp_elem env prev) zip
          (pp_elem env prev) elem
      | App1 (elem, zip) ->
        fprintf fmt "inr@[<v -1>⟨@,%a@,%a⟩@]"
          (pp_elem env prev) elem
          (pp pp_elem env prev) zip
      | Halt ->
        fprintf fmt "halt"
      | Lam zip ->
        fprintf fmt "lam@[<v -1>⟨@,%a⟩@]"
          (pp pp_elem env prev) zip
  end
end

module Machine = struct
  type t = {
    clo : Clo.t;
    ctx : Clo.t Zip.t;
  }

  let into e =
    let open Clo in
    let open Syntax.Sub in
    let clo = Clo (e, Id) in
    let ctx = Zip.Halt in
    { clo; ctx }

  let from { clo; ctx } = Zip.apply (Zip.map Clo.from ctx) (Clo.from clo)

  let pp fmt rule state =
    fprintf fmt "@[<v>ctx  ::@[<v -5>@,%a@]@,clo  ::@[<v -5>@,%a@]@,rule ::@[<v -5>@,%a@]@,term ::@[<v -5>@,%a@]@]@."
      (Pretty.Zip.pp Pretty.Clo.pp (Pretty.Env.mk ()) 2) state.ctx
      (Pretty.Clo.pp (Pretty.Env.mk ()) 2) state.clo
      (Fmt.string) rule
      (Pretty.Term.pp (Pretty.Env.mk ()) 2) (from state)

  let halted state =
    let open Clo in
    let open Syntax.Sub in
    let open Syntax.Term in
    match [@warning "-4"] state with
    | { clo = Clo (Var _, Id); _ } -> true
    | _ -> false

  let step state =
    let open Clo in
    let open Syntax.Sub in
    let open Syntax.Term in
    let rule = ref "" in
    let state = match [@warning "-4"] state with
      (* left *)
      | { clo = Clo (App (e0, e1), sgm); ctx } ->
        let clo = Clo (e0, sgm) in
        let ctx = Zip.App0 (ctx, Clo (e1, sgm)) in
        rule := "LEFT"
      ; { clo; ctx }
      (* beta *)
      | { clo = Clo (Lam e, sgm); ctx = Zip.App0 (ctx, c0) } ->
        let clo = Clo (e, Cmp (Dot (c0, sgm), Id)) in
        rule := "BETA"
      ; { clo; ctx }
      (* lambda *)
      | { clo = Clo (Lam e, sgm); ctx } ->
        let clo = Clo (e, Cmp (Dot (Clo (Var 0, Id), Cmp (sgm, Shift)), Id)) in
        let ctx = Zip.Lam ctx in
        rule := "LAMBDA"
      ; { clo; ctx }
      (* associate *)
      | { clo = Clo (Var n, Cmp (Cmp (pi, rho), sgm)); ctx } ->
        let clo = Clo (Var n, Cmp (pi, Cmp (rho, sgm))) in
        rule := "ASSOCIATE"
      ; { clo; ctx }
      (* head *)
      | { clo = Clo (Var 0, Cmp (Dot (Clo (e, pi), _), sgm)); ctx } ->
        let clo = Clo (e, Cmp (pi, sgm)) in
        rule := "HEAD"
      ; { clo; ctx }
      (* tail *)
      | { clo = Clo (Var n, Cmp (Dot (Clo (_, _), rho), sgm)); ctx } ->
        let clo = Clo (Var (n - 1), Cmp (rho, sgm)) in
        rule := "TAIL"
      ; { clo; ctx }
      (* shift *)
      | { clo = Clo (Var n, Cmp (Shift, sgm)); ctx } ->
        let clo = Clo (Var (n + 1), sgm) in
        rule := "SHIFT"
      ; { clo; ctx }
      (* id *)
      | { clo = Clo (Var n, Cmp (Id, sgm)); ctx } ->
        let clo = Clo (Var n, sgm) in
        rule := "ID"
      ; { clo; ctx }
      | _ ->
        pp std_formatter !rule state
      ; failwith "bad state" in
    pp std_formatter !rule state
  ; state

  let norm e =
    let count = ref 0 in
    let state = ref (into e) in
    while (not (halted !state)) do
      fprintf std_formatter "@\n--- step[%d] ---@\n" !count
    ; incr count
    ; state := step !state
    done
  ; from !state
end

module Test = struct
  open Syntax.Term
  let l e = Lam e
  let ( *@ ) e0 e1 = App (e0, e1)
  let ff = l (l (Var 1))
  let tt = l (l (Var 0))
  let zero = l (l (Var 1))
  let succ = l (l (l (Var 0 *@ Var 2)))
  let one = succ *@ zero
  let two = succ *@ one
  let three = succ *@ two
  let const = l (l (Var 1))
  let fix = l (l (Var 1 *@ (Var 0 *@ Var 0)) *@ l (Var 1 *@ (Var 0 *@ Var 0)))
  let add = fix *@ l (l (l (Var 1 *@ Var 0 *@ l (succ *@ Var 3 *@ Var 0 *@ Var 1))))
  let init = l (l (Var 0) *@ l (l (Var 1)))
end

module Run = struct
  let go () = Machine.norm Test.init
end
