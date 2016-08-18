open Ocamlbuild_plugin

let () = dispatch begin [@warning "-4"] function
    | After_rules -> ocaml_lib "src/lib/yggdrasil";
    | _ -> ()
  end
