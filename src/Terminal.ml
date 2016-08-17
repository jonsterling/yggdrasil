let act_parse file_name =
  let module T = Token in
  let%lwt ix = Lwt_io.open_file ~mode:Lwt_io.Input file_name in
  let tokens = Lexer.tokens ix in
  Lwt_stream.iter begin fun tok ->
    Printf.printf "%s\n" @@ Token.show_token tok
  end tokens

open Cmdliner

let cmd_parse =
  let doc = "parse file" in
  let file_name = Arg.
    ( required
    & pos ~rev:true 0 (some string) None
    & info [] ~doc ~docv:"FILE"
    ) [@warning "-44"] in
  Term.
    ( pure act_parse $ file_name
    , info "parse" ~doc
    )

let cmd_help =
  let doc = "show help" in
  Term.
    ( ret @@ pure @@ `Help ( `Pager, None )
    , info "help" ~doc
    )

let cmd_default =
  Term.
    ( ret @@ pure @@ `Help ( `Pager, None )
    , info "yggdrasil" ~version:"0.0.0"
    )

let cmds = [
  cmd_parse;
  cmd_help;
]
