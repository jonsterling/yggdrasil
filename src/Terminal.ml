let act_parse file_name =
  let module P = Parser.Id in
  let module M = P.MenhirInterpreter in
  let module T = Token in
  let pos = Lexing.dummy_pos in
  let%lwt ix = Lwt_io.open_file ~mode:Lwt_io.Input file_name in
  let tokens = Lexer.tokens ix in
  let parse () : string list M.checkpoint = P.Incremental.main pos in
  let rec handler chk =
    match chk with
    | M.AboutToReduce _ ->
      handler @@ M.resume chk
    | M.Accepted res ->
      let buf = Buffer.create 0 in
      let ppf = Format.formatter_of_buffer buf in
      let pp_ids ppf =
        let sep ppf () = Format.fprintf ppf "@," in
        Fmt.list ~sep Fmt.string ppf in
      let () = Format.fprintf ppf "@[<v>%a@]" pp_ids res in
      let () = Format.pp_print_flush ppf () in
      Lwt_io.printl @@ Buffer.contents buf
    | M.HandlingError _ ->
      Lwt.fail_with "parser: handling error"
    | M.InputNeeded _ ->
      begin
        match%lwt Lwt_stream.get tokens with
        | None ->
          Lwt.fail_with "parser: token stream ended prematurely"
        | Some lexeme ->
          handler @@ M.offer chk (lexeme, pos, pos)
      end
    | M.Rejected ->
      Lwt.fail_with "parser: rejected"
    | M.Shifting _ ->
      handler @@ M.resume chk in
  handler @@ parse ()

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
