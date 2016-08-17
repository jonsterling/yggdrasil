module Make (M : Cats.Sig.MONAD) = struct
  include ParserSpec.Make(M)
end

module Id = Make(Cats.Mod.Monad.Identity)