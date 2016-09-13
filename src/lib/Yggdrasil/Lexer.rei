open Lexing;
open Token;

module type SOURCE = {
  let on_refill: lexbuf => Lwt.t unit;
};

module type LEXER = {
  let token: lexbuf => Lwt.t token;
};
type lexer = (module LEXER);

let module Make: (R: SOURCE) => LEXER;

module type STATE = {
  let ix: Lwt_io.input_channel;
  let sz: int;
};

let module LwtSource: (S: STATE) => SOURCE;

let create: Lwt_io.input_channel => int => (lexer, lexbuf);
let tokens: Lwt_io.input_channel => Lwt_stream.t token;
