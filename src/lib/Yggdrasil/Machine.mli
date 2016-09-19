open Format

module Endo : sig
  type 'a t = 'a -> 'a
end

module Syntax : sig
  module Var : sig
    type t = int
  end
  module Term : sig
    type t =
      | App of t * t
      | Lam of t
      | Var of Var.t
  end
  module Sub : sig
    type 'a t =
      | Cmp of 'a t * 'a t
      | Dot of 'a * 'a t
      | Id
      | Shift
    val map : ('a -> 'b) -> ('a t -> 'b t)
    val apply : Term.t t -> Term.t Endo.t
  end
end

module Zip : sig
  open Syntax
  type 'a t =
    | App0 of 'a t * 'a
    | App1 of 'a * 'a t
    | Halt
    | Lam of 'a t
  val map : ('a -> 'b) -> ('a t -> 'b t)
  val apply : Term.t t -> Term.t Endo.t
end

module Clo : sig
  open Syntax
  type t =
    | Clo of Term.t * t Sub.t
  val from : t -> Term.t
end

module Pretty : sig
  module Delim : sig
    type t
  end
  module Prec : sig
    type t = int
  end
  module Name : sig
    type t
    val gen : unit -> int -> string option
  end
  module Env : sig
    type t
    val mk : unit -> t
  end

  type 'a printer = Env.t -> Prec.t -> formatter -> 'a -> unit

  module Term : sig
    val pp : Syntax.Term.t printer
  end
  module Sub : sig
    val pp : 'a printer -> ('a Syntax.Sub.t) printer
  end
  module Clo : sig
    val pp : Clo.t printer
  end
  module Zip : sig
    val pp : 'a printer -> ('a Zip.t) printer
  end
end

module Machine : sig
  open Syntax
  type t = {
    clo : Clo.t;
    ctx : Clo.t Zip.t;
  }
  val into : Term.t -> t
  val from : t -> Term.t
  val pp : formatter -> string -> t -> unit
  val halted : t -> bool
  val step : t -> t
  val norm : Syntax.Term.t -> Syntax.Term.t
end

module Run : sig
  val go : unit -> Syntax.Term.t
end
