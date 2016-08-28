open Data.Rose;

let module T = Syntax.Term;

let module Ctx: {
  type t [@@deriving (eq, ord)];
  let empty: t;
  let push: t => list T.Bind.t => t;
  let arity: t => T.Variable.t => T.Rose.t;
} = {
  type t = list T.Bind.t [@@deriving (eq, ord)];
  let empty = [];
  let push = List.append;
  let arity gamma x => {
    let pred (y, _) => T.Variable.equal x y;
    let (_, ar) = List.find pred gamma;
    ar
  };
};

let module S = {
  let module Chk = {
    module type Node = {let arity: Computad.t => Ctx.t => T.Node.t => T.Rose.t => unit;};
  };
  let module Inf = {
    module type Node = {
      let arity: Computad.t => Ctx.t => T.Node.t => T.Rose.t;
      let subtract: Computad.t => Ctx.t => T.Bouquet.t => T.Bouquet.t => T.Bouquet.t;
    };
    module type Rose = {let arity: Computad.t => Ctx.t => T.Rose.t => T.Rose.t;};
  };
  module type Chk = {let module Node: Chk.Node;};
  module type Inf = {let module Node: Inf.Node; let module Rose: Inf.Rose;};
};

let module rec Chk: S.Chk = {
  let module Node = {
    let arity sigma gamma tm ar => assert (T.Rose.equal (Inf.Node.arity sigma gamma tm) ar);
  };
}
and Inf: S.Inf = {
  let module rec Node: S.Inf.Node = {
    open T.Node;
    let rec arity sigma gamma tm =>
      switch tm {
      | Ap rho => Rose.arity sigma gamma rho
      | Op op => Computad.arity sigma op
      | Lm xs e =>
        let dom0 = List.map snd xs;
        let Fork cod dom1 = arity sigma (Ctx.push gamma xs) e;
        Fork cod (dom0 @ dom1)
      | Var x => Ctx.arity gamma x
      }
    and subtract sigma gamma doms sp =>
      switch (doms, sp) {
      | (doms, []) => doms
      | ([dom, ...doms], [tm, ...sp]) =>
        let () = Chk.Node.arity sigma gamma (Ap tm) dom;
        subtract sigma gamma doms sp
      | _ => assert false
      };
  }
  and Rose: S.Inf.Rose = {
    let arity sigma gamma (Fork hd sp) =>
      switch (Node.arity sigma gamma hd) {
      | Fork cod dom0 =>
        let dom1 = Node.subtract sigma gamma dom0 sp;
        Fork cod dom1
      };
  };
};
