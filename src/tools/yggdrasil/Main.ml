open Cmdliner

let is_infix ~affix s =
  (* Damned, already missing astring, from which this is c&p *)
  let len_a = String.length affix in
  let len_s = String.length s in
  if len_a > len_s then false else
    let max_idx_a = len_a - 1 in
    let max_idx_s = len_s - len_a in
    let rec loop i k =
      if i > max_idx_s then false else
      if k > max_idx_a then true else
      if k > 0 then
        if String.get affix k = String.get s (i + k) then loop i (k + 1) else
          loop (i + 1) 0
      else if String.get affix 0 = String.get s i then loop i 1 else
        loop (i + 1) 0
    in
    loop 0 0

let setup ?style_renderer ?utf_8 buf =
  let ppf = Format.formatter_of_buffer buf in
  let style_renderer = match style_renderer with
    | Some r -> r
    | None ->
      let dumb = try Sys.getenv "TERM" = "dumb" with
        | Not_found -> true in
      if not dumb then `Ansi_tty else `None in
  let utf_8 = match utf_8 with
    | Some b -> b
    | None ->
      let has_utf_8 var = try
          let res = String.uppercase (Sys.getenv var) in
          let () = Printf.printf "%s\n" res in
          is_infix "UTF-8" res
        with
        | Not_found -> false in
      has_utf_8 "LANG" ||
      has_utf_8 "LC_ALL" ||
      has_utf_8 "LC_CTYPE" in
  Printf.printf "%b\n" utf_8;
  Fmt.set_style_renderer ppf style_renderer ;
  Fmt.set_utf_8 ppf utf_8 ;
  ppf

let act_parse file_name =
  let open Format in
  let module P = Parser.Id in
  let module M = P.MenhirInterpreter in
  let module T = Token in
  let pos = Lexing.dummy_pos in
  let%lwt ix = Lwt_io.open_file ~mode:Lwt_io.Input file_name in
  let tokens = Lexer.tokens ix in
  let parse () = P.Incremental.computad pos in
  let rec handler chk =
    match chk with
    | M.AboutToReduce _ ->
      handler @@ M.resume chk
    | M.Accepted computad ->
      let buf = Buffer.create 0 in
      let fmt = setup buf in
      let () = Computad.pp fmt computad in
      let () = pp_print_flush fmt () in
      Lwt_io.printl @@ Buffer.contents buf
    | M.HandlingError _ ->
      let msg = "parser :: handling error" in
      Lwt.fail_with msg
    | M.InputNeeded _ ->
      begin
        match%lwt Lwt_stream.get tokens with
        | None ->
          Lwt.fail_with "parser :: token stream ended prematurely"
        | Some lexeme ->
          handler @@ M.offer chk (lexeme, pos, pos)
      end
    | M.Rejected ->
      Lwt.fail_with "parser :: rejected"
    | M.Shifting _ ->
      handler @@ M.resume chk in
  handler @@ parse ()

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

let main () =
  match Term.eval_choice cmd_default cmds with
  | `Error _ -> exit 1
  | `Ok expr -> Lwt_main.run expr
  | _ -> exit 0

let () =
  if not !Sys.interactive then
    main ()
