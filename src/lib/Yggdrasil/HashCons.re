let module Interner = {

  let module Tag = {
    type t = int;
    let counter = ref 0;
    let gen () => {
      incr counter;
      !counter;
    };
  };

  type node +'a = {
    obj: 'a,
    tag: Tag.t,
    key: int,
  };

  type t 'a = {
    mutable array: array (Weak.t (node 'a)),
    mutable count: int,
    mutable limit: int,
  };

  let array_min = 7;
  let array_max = Sys.max_array_length;
  let array_lim = 3;
  let array_lim_step = 100;

  let create size => {
    let size = if (size < array_min) array_min else size;
    let size = if (size > array_max) array_max else size;
    let bucket = Weak.create 0;
    {
      array: Array.make size bucket,
      count: 0,
      limit: array_lim,
    }
  };

  let clear table => {
    let empty = Weak.create 0;
    for i in 0 to (Array.length table.array - 1) {
      table.array.(i) = empty
    };
    table.count = 0;
    table.limit = array_lim;
  };

  let module Size = {
    let next n => min (array_lim * n / 2 + array_lim) (Sys.max_array_length - 1);
  };

  let fold f table init => {
    let rec go i bucket acc =>
      if (i >= Weak.length bucket) {
        acc
      } else {
        switch (Weak.get bucket i) {
        | Some node => go (i + 1) bucket @@ f node acc
        | None => go (i + 1) bucket acc
        }
      };
    Array.fold_right (go 0) table.array init
  };

  let rec resize table => {
    let len_old = Array.length table.array;
    let len_new = Size.next len_old;
    if (len_new > len_old) {
      let table_old = table;
      let table_new = create len_new;
      table_new.limit = table_old.limit + array_lim_step;
      ignore @@ fold (fun node () => insert table_new node) table_old ();
      table_old.array = table_new.array;
      table_old.limit = table_old.limit + 2;
    }
  }

  and insert table node => {
    let index = node.key mod Array.length table.array;
    let bucket_old = table.array.(index);
    let size_old = Weak.length bucket_old;
    let rec go i =>
      if (i >= size_old) {
        let size_new = min (size_old + array_lim) @@ Sys.max_array_length - 1;
        if (size_new <= size_old) {
          failwith "cannot resize bucket";
        };
        let bucket_new = Weak.create size_new;
        Weak.blit bucket_old 0 bucket_new 0 size_old;
        Weak.set bucket_new i @@ Some node;
        table.array.(index) = bucket_new;
        table.count = table.count + (size_new - size_old);
        if (table.count > table.limit * Array.length table.array) {
          resize table;
        };
      } else if (Weak.check bucket_old i) {
        go @@ i + 1;
      } else {
        Weak.set bucket_old i @@ Some node;
      };
    go 0
  };

  let intern table obj => {
    let key = Hashtbl.hash obj land max_int;
    let index = key mod Array.length table.array;
    let bucket = table.array.(index);
    let size = Weak.length bucket;
    let rec go i =>
      if (i >= size) {
        let node = {obj, key, tag: Tag.gen ()};
        insert table node;
        node;
      } else {
        switch (Weak.get_copy bucket i) {
        | Some node when node.obj == obj =>
          switch (Weak.get bucket i) {
          | Some node => node
          | None => go @@ i + 1
          }
        | _ => go @@ i + 1
        }
      };
    go 0
  };
};
