type t = string [@show.printer fun fmt -> Format.fprintf fmt "%s"]
[@@deriving eq, ord, show]
