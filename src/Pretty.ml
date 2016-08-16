let show pp_obj obj =
  let buffer = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer buffer in
  pp_obj fmt obj;
  Format.pp_print_flush fmt ();
  Buffer.contents buffer
