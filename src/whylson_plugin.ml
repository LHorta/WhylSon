(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *
   *                                                                                         *
   *   MIT License                                                                           *
   *                                                                                         *
   *   Copyright 2020 Luís Pedro Arrojado Horta                                              *
   *                                                                                         *
   *                                                                                         *
   *   Permission is hereby granted, free of charge, to any person obtaining a copy of       *
   *   this software and associated documentation files (the "Software"), to deal in         *
   *   the Software without restriction, including without limitation the rights to use,     *
   *   copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the       *
   *   Software, and to permit persons to whom the Software is furnished to do so, subject   *
   *   to the following conditions:                                                          *
   *                                                                                         *
   *   The above copyright notice and this permission notice shall be included in all        *
   *   copies or substantial portions of the Software.                                       *
   *                                                                                         *
   *   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,   *
   *   INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A         *
   *   PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT    *
   *   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF  *
   *   CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE  *
   *   OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.                                         *
   *                                                                                         *
   *   End of Lincese                                                                        *
   *                                                                                         *
   *   Research Supported by the Tezos Foundation through project:                           *
   *   FRESCO - FoRmal vErification of Smart COntracts.                                      *
   *                                                                                         *
   *  ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
open Typer
open Why3
open Pmodule
open Typing
open Translator

(* open Ptree *)
(* open Adt *)

type tz_decl = Michelson.Location.t * Ptree.decl

(* let sp_pre_str = Str.regexp_string "requires"
   let sp_post_str = Str.regexp_string "ensures"

   let sp_post_exn_str = Str.regexp_string "raises"

   let sp_variant_str = Str.regexp_string "variant"

   let sp_invariant_str = Str.regexp_string "invariant" *)

let get_spec_comments l =
  List.filter
    (fun (c, _loc) -> c.[0] = '@')
    (List.map (fun (s, loc) -> (String.trim s, loc)) l)

(* let get_spec_token s : spec =
   if Str.string_match sp_pre_str s 0 then Sp_pre,s
   else if .string_match sp_post_str s 0 then Sp_post,s
   else if .string_match sp_post_exn_str s 0 then Sp_post_exn,s
   else if .string_match sp_variant_str s 0 then Sp_variant,s
   else if .string_match sp_invariant_str s 0 then Sp_post,s *)

(* let get_spec_tokens l = List.map (fun (c,loc) -> get_spec_tokens c, loc) l *)

let read_file file =
  match Edo.Parse.parse_program file with
  | Ok ast -> Edo.Parse.program_parse ast
  | Error s -> failwith (Base.Error.to_string_hum s)

let read_channel env path file _c =
  let p, spc = read_file file in
  (* let () = Printf.printf "-----------------\n%s\n-----------------------\n" spec_comment in *)
  let p = to_typed_program p in
  let p = translate_typed_program p spc in
  List.iter (fun (_l, d) -> Format.eprintf "%a@." Mlw_printer.pp_decl d) p;
  Typing.open_file env path;
  (* could remove the Typing. *)
  let id = mk_id "Test" in
  Typing.open_module id;
  (* could remove the Typing. *)
  let add_decl (l, d) = Typing.add_decl l d in
  List.iter add_decl p;
  close_module Loc.dummy_position;
  close_file ()

let () =
  Env.register_format mlw_language "michelson" [ "tz" ] read_channel
    ~desc:"Michelson format"

(*
* register plugin with why3
* why3 config --install-plugin /home/hollowman/.opam/4.08.1/lib/why3michelson/plugins/plugin_why3michelson.cmxs
*)
