open Cmdliner
open Terminal

let main () =
  match Term.eval_choice cmd_default cmds with
  | `Error _ -> exit 1
  | `Ok expr -> Lwt_main.run expr
  | _ -> exit 0

let () =
  if not !Sys.interactive then
    main ()
