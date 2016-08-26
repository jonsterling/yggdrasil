
open Data.Rose
module T = Syntax.Term

module Ctx : sig
  type t
  [@@deriving eq, ord]
  val init : t
  val push : t -> T.Bind.t list -> t
  val arity : t -> T.Variable.t -> T.Rose.t
end = struct
  type t = T.Bind.t list
  [@@deriving eq, ord]
  let init = []
  let push = List.append
  let arity gamma x =
    let pred (y, _) = T.Variable.equal x y in
    let (_, ar) = List.find pred gamma in
    ar
end

module S = struct
  module Chk = struct
    module type Node = sig
      val arity : Computad.t -> Ctx.t -> T.Node.t -> T.Rose.t -> unit
    end
  end
  module Inf = struct
    module type Node = sig
      val arity : Computad.t -> Ctx.t -> T.Node.t -> T.Rose.t
      val subtract : Computad.t -> Ctx.t -> T.Bouquet.t -> T.Bouquet.t -> T.Bouquet.t
    end
    module type Rose = sig
      val arity : Computad.t -> Ctx.t -> T.Rose.t -> T.Rose.t
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

module rec Inf : S.Inf = struct
  module rec Node : S.Inf.Node = struct
    open T.Node
    let rec arity sigma gamma tm =
      match tm with
      | Ap rho ->
        Rose.arity sigma gamma rho
      | Op op ->
        Computad.arity sigma op
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
  and Rose : S.Inf.Rose = struct
    let arity sigma gamma (Fork (hd, sp)) =
      let Fork (cod, dom0) = Node.arity sigma gamma hd in
      let dom1 = Node.subtract sigma gamma dom0 sp in
      Fork (cod, dom1)
  end
end
and Chk : S.Chk = struct
  module Node = struct
    let arity sigma gamma tm ar =
      assert (T.Rose.equal (Inf.Node.arity sigma gamma tm) ar)
  end
end
