module S = Syntax
module Ctx : sig
  type t [@@deriving (eq, ord)]
  val empty : t
  val push : t -> S.Scope.Term.t -> t
  val arity : t -> S.Name.Term.t -> S.Frame.t
end = struct
  type t = S.Scope.Term.t [@@deriving (eq, ord)]
  let empty = []
  let push = List.append
  let arity gamma x =
    let pred (y, _) = S.Name.Term.equal x y in
    let (_, ar) = List.find pred gamma in ar
end
module Sig = struct
  module Chk = struct
    module type Face  = sig
      val arity : Computad.t -> Ctx.t -> S.Face.t -> S.Frame.t -> unit
    end
  end
  module Inf = struct
    module type Face = sig
      val arity : Computad.t -> Ctx.t -> S.Face.t -> S.Frame.t
      val subtract : Computad.t -> Ctx.t -> S.Niche.t -> S.Complex.t -> S.Niche.t
    end
    module type Term = sig
      val arity : Computad.t -> Ctx.t -> S.Term.t -> S.Frame.t
    end
    module type Name = sig
      val arity : Computad.t -> Ctx.t -> S.Name.t -> S.Frame.t
    end
  end
  module type Chk = sig
    module Face : Chk.Face
  end
  module type Inf = sig
    module Face : Inf.Face
    module Term : Inf.Term
  end
end
module rec Chk:Sig.Chk = struct
  module Face = struct
    let arity sigma gamma face frame =
      assert (S.Term.equal (Inf.Face.arity sigma gamma face) frame)
  end
end
and Inf : Sig.Inf = struct
  module rec Face:Sig.Inf.Face = struct
    open Data
    open S.Face
    let rec arity sigma gamma tm =
      match tm with
      | Rho rho -> Term.arity sigma gamma rho
      | Abs (_, xs, e) ->
        let Rose.Fork (cod,{ Diag.rhs = rhs;_}) = arity sigma (Ctx.push gamma xs) e in
        let lhs = [] in
        let rhs = (CCList.map snd xs) @ rhs in
        let diag = { Diag.rhs = rhs; lhs } in
        Rose.Fork (cod, diag)
      | Var var -> Name.arity sigma gamma var
    and subtract sigma gamma doms sp =
      match (doms, sp) with
      | (doms, []) -> doms
      | (dom :: doms, tm :: sp) ->
        let () = Chk.Face.arity sigma gamma (Rho tm) dom in
        subtract sigma gamma doms sp
      | _ -> assert false
  end
  and Term : Sig.Inf.Term = struct
    open Data
    let arity sigma gamma (Rose.Fork (face, { Diag.rhs = complex; _ })) =
      match Face.arity sigma gamma face with
      | Rose.Fork (cod, { Diag.rhs = dom0;_}) ->
        let lhs = [] in
        let rhs = Face.subtract sigma gamma dom0 complex in
        let dom1 = { Diag.lhs = lhs; rhs } in
        Rose.Fork (cod, dom1)
  end
  and Name : Sig.Inf.Name = struct
    let arity sigma gamma name =
      match name with
      | S.Name.Meta _ -> assert false
      | S.Name.Oper varO -> Computad.arity sigma varO
      | S.Name.Term varT -> Ctx.arity gamma varT
  end
end
