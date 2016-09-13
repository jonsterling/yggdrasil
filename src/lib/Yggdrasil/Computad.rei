open Syntax;

module type Sig = {
  type t [@@deriving show];
  let empty: t;
  let bind: t => Dimension.t => Cell.t => t;
  let arity: t => Name.Oper.t => Frame.t;
};

include Sig;
