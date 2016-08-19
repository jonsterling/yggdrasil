module Make (Sigma : Computad.S) = struct
  open Syntax
  include Sigma

  module Sig = struct
    module Chk = struct
      module type Node = sig
        val arity : Sigma.t -> Term.Node.t -> Term.Rose.t -> unit
      end
    end
    module Inf = struct
      module type Node = sig
        val arity : Sigma.t -> Term.Node.t -> Term.Rose.t
        val subtract : Sigma.t -> Term.Bouquet.t -> Term.Bouquet.t -> Term.Bouquet.t
      end
      module type Rose = sig
        val arity : Sigma.t -> Term.Rose.t -> Term.Rose.t
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
      let rec arity sigma tm =
        match [@warning "-4"] tm with
        | Term.Node.Op op ->
          Sigma.arity sigma op
        | Term.Node.Rho rho ->
          Rose.arity sigma rho
      and subtract sigma doms sp =
        match (doms, sp) with
        | doms, [] ->
          doms
        | (dom :: doms), (tm :: sp) ->
          let () = Chk.Node.arity sigma (Term.Node.Rho tm) dom in
          subtract sigma doms sp
        | _ ->
          assert false
    end
    and Rose : Sig.Inf.Rose = struct
      let arity sigma (Data.Rose.Fork (hd, sp)) =
        let (Data.Rose.Fork (cod, doms)) = Node.arity sigma hd in
        let doms' = Node.subtract sigma doms sp in
        Data.Rose.Fork (cod, doms')
    end
  end
  and Chk : Sig.Chk = struct
    module Node = struct
      let arity sigma tm ar =
        assert (Term.Rose.equal (Inf.Node.arity sigma tm) ar)
    end
  end
end
