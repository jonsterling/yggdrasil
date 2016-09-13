let module S = Syntax;

let module Ctx: {
  type t [@@deriving (eq, ord)];
  let empty: t;
  let push: t => S.Scope.Term.t => t;
  let arity: t => S.Name.Term.t => S.Frame.t;
} = {
  type t = S.Scope.Term.t [@@deriving (eq, ord)];
  let empty = [];
  let push = List.append;
  let arity gamma x => {
    let pred (y, _) => S.Name.Term.equal x y;
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
    module type Name = {
      let arity: Computad.t => Ctx.t => S.Name.t => S.Frame.t;
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
    let arity sigma gamma face frame =>
      assert (S.Term.equal (Inf.Face.arity sigma gamma face) frame);
  };
}
and Inf: Sig.Inf = {
  let module rec Face: Sig.Inf.Face = {
    open Data;
    open S.Face;
    let rec arity sigma gamma tm => switch tm {
      | Rho rho => Term.arity sigma gamma rho;
      | Abs _ xs e =>
        let Rose.Fork cod { Diag.rhs, _ } = arity sigma (Ctx.push gamma xs) e;
        let lhs = [];
        let rhs = CCList.map snd xs @ rhs;
        let diag = { Diag.rhs, lhs };
        Rose.Fork cod diag;
      | Var var => Name.arity sigma gamma var;
      }
    and subtract sigma gamma doms sp => switch (doms, sp) {
      | (doms, []) => doms;
      | ([dom, ...doms], [tm, ...sp]) =>
        let () = Chk.Face.arity sigma gamma (Rho tm) dom;
        subtract sigma gamma doms sp;
      | _ => assert false;
      };
  }
  and Term: Sig.Inf.Term = {
    open Data;
    let arity sigma gamma (Rose.Fork face { Diag.rhs: complex, _ }) => {
      switch (Face.arity sigma gamma face) {
      | Rose.Fork cod { Diag.rhs: dom0, _ } =>
        let lhs = [];
        let rhs  = Face.subtract sigma gamma dom0 complex;
        let dom1 = { Diag.lhs, rhs };
        Rose.Fork cod dom1;
      };
    };
  }
  and Name: Sig.Inf.Name = {
    let arity sigma gamma name => {
      switch name {
      | S.Name.Meta _ => assert false;
      | S.Name.Oper varO => Computad.arity sigma varO;
      | S.Name.Term varT => Ctx.arity gamma varT;
      };
    };
  };
};
