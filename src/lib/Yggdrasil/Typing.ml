module Make (Sigma : Computad.S) = struct
  open Data.Rose
  open Syntax
  include Sigma

  module Ctx : sig
    type t
    [@@deriving eq, ord]
    val init : t
    val push : t -> Term.Bind.t list -> t
    val arity : t -> Term.Var.t -> Term.Rose.t
  end = struct
    type t = Term.Bind.t list
    [@@deriving eq, ord]
    let init = []
    let push = List.append
    let arity gamma x =
      let pred (y, _) = Term.Var.equal x y in
      let (_, ar) = List.find pred gamma in
      ar
  end

  module Sig = struct
    module Chk = struct
      module type Node = sig
        val arity : Sigma.t -> Ctx.t -> Term.Node.t -> Term.Rose.t -> unit
      end
    end
    module Inf = struct
      module type Node = sig
        val arity : Sigma.t -> Ctx.t -> Term.Node.t -> Term.Rose.t
        val subtract : Sigma.t -> Ctx.t -> Term.Bouquet.t -> Term.Bouquet.t -> Term.Bouquet.t
      end
      module type Rose = sig
        val arity : Sigma.t -> Ctx.t -> Term.Rose.t -> Term.Rose.t
      end
    end
    module type Chk = sig
      module Node : Chk.Node
    end
    module type Inf = sig
      module Node : Inf.Node
      module Rose : Inf.Rose
    end
  end

  module rec Inf : Sig.Inf = struct
    module rec Node : Sig.Inf.Node = struct
      open Term.Node
      let rec arity sigma gamma tm =
        match [@warning "-4"] tm with
        | Ap rho ->
          Rose.arity sigma gamma rho
        | Op op ->
          Sigma.arity sigma op
        | Lm (xs, e) ->
          let dom0 = List.map snd xs in
          let Fork (cod, dom1) = arity sigma (Ctx.push gamma xs) e in
          Fork (cod, dom0 @ dom1)
        | Var x ->
          Ctx.arity gamma x

      and subtract sigma gamma doms sp =
        match (doms, sp) with
        | doms, [] ->
          doms
        | (dom :: doms), (tm :: sp) ->
          let () = Chk.Node.arity sigma gamma (Ap tm) dom in
          subtract sigma gamma doms sp
        | _ ->
          assert false
    end
    and Rose : Sig.Inf.Rose = struct
      let arity sigma gamma (Fork (hd, sp)) =
        let Fork (cod, dom0) = Node.arity sigma gamma hd in
        let dom1 = Node.subtract sigma gamma dom0 sp in
        Fork (cod, dom1)
    end
  end
  and Chk : Sig.Chk = struct
    module Node = struct
      let arity sigma gamma tm ar =
        assert (Term.Rose.equal (Inf.Node.arity sigma gamma tm) ar)
    end
  end
end
