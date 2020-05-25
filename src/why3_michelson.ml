open Why3
open Pmodule
open Typing
(* open Ptree *)
open Michelson
(* open Adt *)
open Why3_michelson_trans

let read_file file c =
  let lb = Lexing.from_channel c in
  Parser.start Lexer.next_token lb

let read_channel env path file c =
  let p = read_file file c in
  let p = program p in
  List.iter (fun d -> Format.eprintf "%a@." Mlw_printer.pp_decl d) p;
  Typing.open_file env path; (* could remove the Typing. *)
  let id = mk_id "Test" in
  Typing.open_module id;     (* could remove the Typing. *)
  let add_decl d = Typing.add_decl Loc.dummy_position d in
  List.iter add_decl p;
  close_module Loc.dummy_position;
  close_file ()

let () =
  Env.register_format mlw_language "michelson" ["tz"] read_channel
    ~desc:"Michelson format"


(*
* register plugin with why3
* why3 config --install-plugin /home/hollowman/.opam/4.08.1/lib/why3michelson/plugins/plugin_why3michelson.cmxs
*)