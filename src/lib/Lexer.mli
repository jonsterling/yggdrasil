open Lexing
open Token

module type SOURCE = sig
  val on_refill : lexbuf -> unit Lwt.t
end

module type LEXER = sig
  val token : lexbuf -> token Lwt.t
end

module Make : functor (R : SOURCE) -> LEXER

module type STATE = sig
  val ix : Lwt_io.input_channel
  val sz : int
end

module LwtSource : functor (S : STATE) -> SOURCE

val create : Lwt_io.input_channel -> int -> (module LEXER) * lexbuf
val tokens : Lwt_io.input_channel -> token Lwt_stream.t
