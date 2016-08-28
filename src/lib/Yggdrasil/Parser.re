let module Make (M: Cats.Sig.MONAD) => {
  include ParserSpec.Make M;
};

let module Id = Make Cats.Mod.Monad.Identity;
