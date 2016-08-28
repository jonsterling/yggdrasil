let module Make: (M: Cats.Sig.MONAD) => {
  include module type ParserSpec.Make M;
};

let module Id: module type Make Cats.Mod.Monad.Identity;
