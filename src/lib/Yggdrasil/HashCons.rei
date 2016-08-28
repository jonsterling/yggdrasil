let module Interner: {
  let module Tag: {
    type t = int;
  };
  type node +'a = {
    obj: 'a,
    tag: Tag.t,
    key: int,
  };
  type t 'a;
  let create: int => t 'a;
  let clear: t 'a => unit;
  let intern: t 'a => 'a => node 'a;
};
