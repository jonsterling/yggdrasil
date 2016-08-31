let module R = Data.Rose;
let module S = Syntax;

let module Ctx: {
  type t [@@deriving (eq, ord)];
  let empty: t;
  let push: t => S.Telescope.t => t;
  let arity: t => S.Variable.t => S.Frame.t;
} = {
  type t = S.Telescope.t [@@deriving (eq, ord)];
  let empty = [];
  let push = List.append;
  let arity gamma x => {
    let pred (y, _) => S.Variable.equal x y;
    let (_, ar) = List.find pred gamma;
    ar
  };
};

let module Sig = {
  let module Chk = {
    module type Face = {
      let arity: Computad.t => Ctx.t => S.Face.t => S.Frame.t => unit;
    };
  };
  let module Inf = {
    module type Face = {
      let arity: Computad.t => Ctx.t => S.Face.t => S.Frame.t;
      let subtract: Computad.t => Ctx.t => S.Niche.t => S.Complex.t => S.Niche.t;
    };
    module type Term = {
      let arity: Computad.t => Ctx.t => S.Term.t => S.Frame.t;
    };
  };
  module type Chk = {
    let module Face: Chk.Face;
  };
  module type Inf = {
    let module Face: Inf.Face;
    let module Term: Inf.Term;
  };
};

let module rec Chk: Sig.Chk = {
  let module Face = {
    let arity sigma gamma tm ar =>
      assert (S.Term.equal (Inf.Face.arity sigma gamma tm) ar);
  };
}
and Inf: Sig.Inf = {
  let module rec Face: Sig.Inf.Face = {
    open S.Face;
    let rec arity sigma gamma tm => switch tm {
      | Nest rho => Term.arity sigma gamma rho
      | Op op => Computad.arity sigma op
      | Lm xs e =>
        let dom0 = CCList.map snd xs;
        let R.Fork cod dom1 = arity sigma (Ctx.push gamma xs) e;
        R.Fork cod (dom0 @ dom1)
      | Var x => Ctx.arity gamma x
      }
    and subtract sigma gamma doms sp => switch (doms, sp) {
      | (doms, []) => doms
      | ([dom, ...doms], [tm, ...sp]) =>
        let () = Chk.Face.arity sigma gamma (Nest tm) dom;
        subtract sigma gamma doms sp
      | _ => assert false
      };
  }
  and Term: Sig.Inf.Term = {
    let arity sigma gamma (R.Fork hd sp) => switch (Face.arity sigma gamma hd) {
      | R.Fork cod dom0 =>
        let dom1 = Face.subtract sigma gamma dom0 sp;
        R.Fork cod dom1
      };
  };
};
