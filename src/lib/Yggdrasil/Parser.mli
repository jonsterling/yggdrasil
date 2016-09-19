module Make (M : Cats.Sig.MONAD) : sig
  include module type of ParserSpec.Make(M)
end

module Id : module type of Make(Cats.Mod.Monad.Identity)
