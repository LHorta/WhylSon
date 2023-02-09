(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *
   *                                                                                         *
   *   MIT License                                                                           *
   *                                                                                         *
   *   Copyright 2021 Luís Pedro Arrojado da Horta                                              *
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

open Michelson

let rec remove_at n = function
  | [] -> []
  | h :: t -> if Z.(n = zero) then t else h :: remove_at Z.(n - one) t

let rec drop_n n = function
  | [] -> []
  | _ :: t as lst -> if Z.(n <= zero) then lst else drop_n Z.(n - one) t

(* if given position is a negative number, the element will be placed at the head of the list *)
let rec insert_at x n = function
  | [] -> [ x ]
  | h :: t as l ->
      if Z.(n <= zero) then x :: l else h :: insert_at x Z.(n - one) t

(* let rec type_extractor (_, t, _) =
   let open Adt in
   let t =
     match t with
     | Type_int -> Type_int
     | Type_key -> Type_key
     | Type_signature -> Type_signature
     | Type_operation -> Type_operation
     | Type_chain_id -> Type_chain_id
     | Type_nat -> Type_nat
     | Type_string -> Type_string
     | Type_bytes -> Type_bytes
     | Type_mutez -> Type_mutez
     | Type_bool -> Type_bool
     | Type_key_hash -> Type_key_hash
     | Type_timestamp -> Type_timestamp
     | Type_address -> Type_address
     | Type_never -> Type_never
     | Type_bls12_381_g1 -> Type_bls12_381_g1
     | Type_bls12_381_g2 -> Type_bls12_381_g2
     | Type_bls12_381_fr -> Type_bls12_381_fr
     | Type_option t' -> Type_option (type_extractor t')
     | Type_list t' -> Type_list (type_extractor t')
     | Type_set t' -> Type_set (type_extractor t')
     | Type_contract t' -> Type_contract (type_extractor t')
     | Type_pair (t1, t2) -> Type_pair (type_extractor t1, type_extractor t2)
     | Type_or (t1, t2) -> Type_or (type_extractor t1, type_extractor t2)
     | Type_lambda (t1, t2) -> Type_lambda (type_extractor t1, type_extractor t2)
     | Type_map (t1, t2) -> Type_map (type_extractor t1, type_extractor t2)
     | Type_big_map (t1, t2) -> Type_big_map (type_extractor t1, type_extractor t2)
     | Type_ticket t' -> Type_ticket (type_extractor t')
     | Type_sapling_transaction n -> Type_sapling_transaction n
     | Type_sapling_state n -> Type_sapling_state n
   in
   ((), t, ()) *)

let stack_checker s1 s2 =
  List.fold_left2 (fun acc x y -> acc && x = y) true s1 s2

let string_of_simple_comparable_type =
  let open Adt in
  function
  | Type_key -> "Type_key"
  | Type_int -> "Type_int"
  | Type_nat -> "Type_nat"
  | Type_string -> "Type_string"
  | Type_bytes -> "Type_bytes"
  | Type_mutez -> "Type_mutez"
  | Type_bool -> "Type_bool"
  | Type_key_hash -> "Type_key_hash"
  | Type_timestamp -> "Type_timestamp"
  | Type_address -> "Type_address"
  | Type_unit -> "Type_unit"

let rec string_of_comparable_type =
  let open Adt in
  function
  | Type_simple_comparable_type t -> string_of_simple_comparable_type t
  | Type_comparable_pair (t_1, t_2) ->
      "Type_pair ("
      ^ string_of_simple_comparable_type t_1
      ^ ", "
      ^ string_of_comparable_type t_2
      ^ ")"

let rec string_of_type =
  let open Adt in
  function
  | Type_comparable ct -> string_of_comparable_type ct
  | Type_option t -> "Type_option (" ^ string_of_type t ^ ")"
  | Type_list t -> "Type_list (" ^ string_of_type t ^ ")"
  | Type_set t -> "Type_set (" ^ string_of_comparable_type t ^ ")"
  | Type_operation -> "Type_operation"
  | Type_contract t -> "Type_Contract (" ^ string_of_type t ^ ")"
  | Type_pair (t1, t2) ->
      "Type_pair (" ^ string_of_type t1 ^ ", " ^ string_of_type t2 ^ ")"
  | Type_or (t1, t2) ->
      "Type_or (" ^ string_of_type t1 ^ ", " ^ string_of_type t2 ^ ")"
  | Type_lambda (t1, t2) ->
      "Type_lambda (" ^ string_of_type t1 ^ ", " ^ string_of_type t2 ^ ")"
  | Type_map (t1, t2) ->
      "Type_map ("
      ^ string_of_comparable_type t1
      ^ ", " ^ string_of_type t2 ^ ")"
  | Type_big_map (t1, t2) ->
      "Type_big_map ("
      ^ string_of_comparable_type t1
      ^ ", " ^ string_of_type t2 ^ ")"
  | Type_chain_id -> "Type_chain_id"
  | Type_signature -> "Type_signature"

let stack_printer s_name s =
  s_name ^ ": ["
  ^ String.concat "; " (List.map (fun x -> string_of_type x) s @ [ "]\n" ])

exception Bad_Typing of string

let split_n n lst =
  if Z.(n < zero) then raise (Bad_Typing "Invalid List size")
  else
    let rec aux n lst acc =
      match lst with
      | [] ->
          if Z.(n > zero) then
            raise (Bad_Typing "List is smaller than argument")
          else (List.rev acc, [])
      | h :: t ->
          if Z.(n = zero) then (List.rev acc, h :: t)
          else aux Z.(n - one) t (h :: acc)
    in
    aux n lst []

let to_typed_program (p : Adt_typ.program) : Adt_typ.program_typed =
  let open Adt_typ in
  let initial_stack =
    {
      stack_size = 1;
      stack_type =
        [ { value = T_pair (p.param, p.storage); loc = p.param.loc } ];
    }
  in
  let rec typer s i =
    let open Adt in
    match i.Location.value with
    | I_seq (i_1, i_2) ->
        let desc_1, s1 = typer s i_1 in
        let desc_2, s_2 = typer s1 i_2 in
        let code_1 = { desc = desc_1; stack_before = s; stack_after = s1 } in
        let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s1 } in
        let x = { i with value = Adt_typ.I_seq (code_1, code_2) } in
        let code =
          { desc = x; stack_after = s_2; stack_before = code_1.stack_before }
        in
        (code.desc, code.stack_after)
        (* Adt_typ.I_seq (code_1, code_2), s_2 *)
    | I_drop ->
        let sa =
          { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
        in
        ({ i with value = Adt_typ.I_drop }, sa)
    | I_drop_n n ->
        let lst = drop_n n s.stack_type in
        let sa = { stack_size = s.stack_size - Z.to_int n; stack_type = lst } in
        ({ i with value = Adt_typ.I_drop_n n }, sa)
    | I_dup ->
        let sa =
          {
            stack_size = s.stack_size + 1;
            stack_type = List.hd s.stack_type :: s.stack_type;
          }
        in
        ({ i with value = Adt_typ.I_dup }, sa)
    | I_swap ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let sa = { stack_size = s.stack_size; stack_type = t2 :: t1 :: lst } in
        ({ i with value = Adt_typ.I_swap }, sa)
    | I_dig n ->
        let t, lst =
          (List.nth s.stack_type (Z.to_int n), remove_at n s.stack_type)
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_dig n }, sa)
    | I_dug n ->
        let lst = insert_at (List.hd s.stack_type) n (List.tl s.stack_type) in
        let sa = { stack_size = s.stack_size; stack_type = lst } in
        ({ i with value = Adt_typ.I_dug n }, sa)
    | I_push (t, d) ->
        let lst = s.stack_type in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_push (t, d) }, sa)
    | I_some ->
        let t', lst = (List.hd s.stack_type, List.tl s.stack_type) in
        let t = { t' with value = T_option t' } in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_some }, sa)
    | I_none t' ->
        let t, lst = (T_option t', s.stack_type) in
        let t' = { Location.loc = t'.loc; Location.value = t } in
        let sa = { stack_size = s.stack_size + 1; stack_type = t' :: lst } in
        ({ i with value = Adt_typ.I_none t' }, sa)
    | I_unit ->
        let lst = s.stack_type in
        let t' =
          T_comparable
            (T_simple_comparable_type
               { Location.loc = i.loc; Location.value = T_unit })
        in
        let t = { i with value = t' } in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_unit }, sa)
    | I_if_none (i_1, i_2) ->
        let s' =
          match (List.hd s.stack_type).value with
          | T_option t' -> t'
          | _ -> raise (Bad_Typing "Invalid types on IF_NONE")
        in
        let s_1' =
          { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
        in
        let s_2' =
          { stack_size = s.stack_size; stack_type = s' :: List.tl s.stack_type }
        in
        let desc_1, s_1 = typer s_1' i_1 in
        let desc_2, s_2 = typer s_2' i_2 in
        let code_1 =
          { desc = desc_1; stack_after = s_1; stack_before = s_1' }
        in
        let code_2 =
          { desc = desc_2; stack_after = s_2; stack_before = s_2' }
        in
        if stack_checker s_1.stack_type s_2.stack_type then
          ({ i with value = Adt_typ.I_if_none (code_1, code_2) }, s_2)
        else raise (Bad_Typing "Type of IF_NONE branches do not match")
    | I_pair ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t = { Location.value = T_pair (t1, t2); loc = t1.loc } in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_pair }, sa)
    | I_car ->
        let t', lst = (List.hd s.stack_type, List.tl s.stack_type) in
        let t = match t'.value with T_pair (a, _) -> a | _ -> assert false in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_car }, sa)
    | I_cdr ->
        let t', lst = (List.hd s.stack_type, List.tl s.stack_type) in
        let t = match t'.value with T_pair (_, b) -> b | _ -> assert false in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_cdr }, sa)
    | I_left t' ->
        (* let t' = Adt.type_of_parser_type t' in *)
        let t', lst = (T_or (List.hd s.stack_type, t'), List.tl s.stack_type) in
        let t = { i with value = t' } in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_left t }, sa)
    | I_right t' ->
        (* checked till here *)
        let t' = Adt.type_of_parser_type t' in
        let t, lst =
          (Type_or (t', List.hd s.stack_type), List.tl s.stack_type)
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_right t' }, sa)
    | I_if_left (i_1, i_2) ->
        let s' =
          match List.hd s.stack_type with
          | Type_or (l, r) -> (l, r)
          | _ -> raise (Bad_Typing "Invalid types on IF_LEFT")
        in
        let s_1' = { s with stack_type = fst s' :: List.tl s.stack_type } in
        let s_2' = { s with stack_type = snd s' :: List.tl s.stack_type } in
        let desc_1, s_1 = typer s_1' i_1 in
        let desc_2, s_2 = typer s_2' i_2 in
        let code_1 =
          { desc = desc_1; stack_after = s_1; stack_before = s_1' }
        in
        let code_2 =
          { desc = desc_2; stack_after = s_2; stack_before = s_2' }
        in
        if stack_checker s_1.stack_type s_2.stack_type then
          ({ i with value = Adt_typ.I_if_left (code_1, code_2) }, s_2)
        else raise (Bad_Typing "Type of IF_LEFT branches do not match")
    | I_nil t' ->
        let t' = Adt.type_of_parser_type t' in
        let t, lst = (Type_list t', s.stack_type) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_nil t' }, sa)
    | I_cons ->
        let lst = List.tl s.stack_type in
        (* no need to change type because it is on position 1 *)
        let sa = { stack_size = s.stack_size - 1; stack_type = lst } in
        ({ i with value = Adt_typ.I_cons }, sa)
    | I_if_cons (i_1, i_2) ->
        let s' =
          match List.hd s.stack_type with
          | Type_list t' -> t'
          | _ -> raise (Bad_Typing "Invalid types on IF_CONS")
        in
        let s_1' =
          { stack_size = s.stack_size + 1; stack_type = s' :: s.stack_type }
        in
        let s_2' =
          { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
        in
        let desc_1, s_1 = typer s_1' i_1 in
        let desc_2, s_2 = typer s_2' i_2 in
        let code_1 =
          { desc = desc_1; stack_after = s_1; stack_before = s_1' }
        in
        let code_2 =
          { desc = desc_2; stack_after = s_2; stack_before = s_2' }
        in
        if stack_checker s_1.stack_type s_2.stack_type then
          ({ i with value = Adt_typ.I_if_cons (code_1, code_2) }, s_2)
        else
          let str1 = stack_printer "s1" s_1.stack_type in
          let str2 = stack_printer "s2" s_2.stack_type in
          let () =
            Printf.printf "%s\n%s\n%s\n" str1 str2
              (string_of_bool (stack_checker s_1.stack_type s_2.stack_type))
          in
          raise (Bad_Typing "Type of IF_CONS branches do not match")
    | I_size ->
        let t, lst =
          ( Type_comparable (Type_simple_comparable_type Type_nat),
            List.tl s.stack_type )
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_size }, sa)
    | I_empty_set t' ->
        let t_comp = Adt.comparable_type_of_parser_type t'.value in
        let t = Type_set t_comp in
        let sa =
          { stack_size = s.stack_size + 1; stack_type = t :: s.stack_type }
        in
        ({ i with value = Adt_typ.I_empty_set (Type_comparable t_comp) }, sa)
    | I_empty_map (tc', t') ->
        let t_comp = Adt.comparable_type_of_parser_type tc'.value in
        let t' = Adt.type_of_parser_type t' in
        let t = Type_map (t_comp, t') in
        let sa =
          { stack_size = s.stack_size + 1; stack_type = t :: s.stack_type }
        in
        ({ i with value = Adt_typ.I_empty_map (Type_comparable t_comp, t') }, sa)
    | I_empty_big_map (tc', t') ->
        let t_comp = Adt.comparable_type_of_parser_type tc'.value in
        let t' = Adt.type_of_parser_type t' in
        let t = Type_big_map (t_comp, t') in
        let sa =
          { stack_size = s.stack_size + 1; stack_type = t :: s.stack_type }
        in
        ( { i with value = Adt_typ.I_empty_big_map (Type_comparable t_comp, t') },
          sa )
    (*| I_map of inst_annotated FIXME: not done yet *)
    | I_iter i ->
        (* TODO: check not sure*)
        let desc, s' =
          typer
            { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
            i
        in
        let sa =
          {
            stack_size = s'.stack_size + 1;
            stack_type = List.hd s.stack_type :: s'.stack_type;
          }
        in
        let code = { desc; stack_after = sa; stack_before = s } in
        ({ i with value = Adt_typ.I_iter code }, sa)
    | I_mem ->
        (* TODO: check not sure*)
        let t, lst =
          ( Type_comparable (Type_simple_comparable_type Type_bool),
            drop_n Z.(of_int 2) s.stack_type )
        in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_mem }, sa)
    | I_get ->
        (* TODO: check not sure*)
        let t =
          match List.hd (List.tl s.stack_type) with
          | Type_map (_c, t') | Type_big_map (_c, t') -> Type_option t'
          | _ -> raise (Bad_Typing "Invalid types on GET")
        in
        let lst = drop_n Z.(of_int 2) s.stack_type in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_get }, sa)
    | I_update ->
        let lst = drop_n Z.(of_int 2) s.stack_type in
        let sa = { stack_size = s.stack_size - 2; stack_type = lst } in
        ({ i with value = Adt_typ.I_update }, sa)
    | I_if (i_1, i_2) ->
        (* TODO: check not sure*)
        let s' =
          { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
        in
        let desc_1, s_1 = typer s' i_1 in
        let desc_2, s_2 = typer s' i_2 in
        let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s' } in
        let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s' } in
        if stack_checker s_1.stack_type s_2.stack_type then
          ({ i with value = Adt_typ.I_if (code_1, code_2) }, s_2)
        else raise (Bad_Typing "Type of IF branches do not match")
    | I_loop i ->
        (* TODO: check not sure FIXME: *)
        let desc, s' =
          typer
            { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
            i
        in
        let code = { desc; stack_after = s'; stack_before = s } in
        ({ i with value = Adt_typ.I_loop code }, s')
    (*| I_loop_left of inst_annotated FIXME: not done *)
    | I_lambda (t1, t2, i) ->
        (* TODO: check why s' is not being used *)
        let t1 = Adt.type_of_parser_type t1 in
        let t2 = Adt.type_of_parser_type t2 in
        let t, lst = (Type_lambda (t1, t2), s.stack_type) in
        let desc, _s' = typer s i in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        let code = { desc; stack_before = s; stack_after = sa } in
        ({ i with value = Adt_typ.I_lambda (t1, t2, code) }, sa)
    | I_exec ->
        (* TODO: check *)
        let t', lst =
          (List.hd (List.tl s.stack_type), drop_n Z.(of_int 2) s.stack_type)
        in
        let t =
          match t' with
          | Type_lambda (_t1, t2) -> t2
          | _ -> raise (Bad_Typing "Invalid types on EXEC")
        in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_exec }, sa)
    | I_dip i ->
        let desc, s' =
          typer
            { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
            i
        in
        let sa =
          {
            stack_size = s'.stack_size + 1;
            stack_type = List.hd s.stack_type :: s'.stack_type;
          }
        in
        let code = { desc; stack_after = sa; stack_before = s } in
        ({ i with value = Adt_typ.I_dip code }, sa)
    | I_dip_n (n, i) ->
        if Z.(n = zero) then
          let desc, sa =
            typer { stack_size = s.stack_size; stack_type = s.stack_type } i
          in
          let code = { desc; stack_after = sa; stack_before = s } in
          ({ i with value = Adt_typ.I_dip_n (n, code) }, sa)
        else if Z.(n = one) then
          let desc, s' =
            typer
              {
                stack_size = s.stack_size - 1;
                stack_type = List.tl s.stack_type;
              }
              i
          in
          let sa =
            {
              stack_size = s'.stack_size + 1;
              stack_type = List.hd s.stack_type :: s'.stack_type;
            }
          in
          let code = { desc; stack_after = sa; stack_before = s } in
          ({ i with value = Adt_typ.I_dip_n (n, code) }, sa)
        else
          let protected_stack, execution_stack = split_n n s.stack_type in
          let desc, s' =
            typer
              {
                stack_size = (s.stack_size - Z.(to_int n));
                stack_type = execution_stack;
              }
              i
          in
          let sa =
            {
              stack_size = (s'.stack_size + Z.(to_int n));
              stack_type = protected_stack @ s'.stack_type;
            }
          in
          let code = { desc; stack_after = sa; stack_before = s } in
          ({ i with value = Adt_typ.I_dip_n (n, code) }, sa)
    (*| I_failwith FIXME: not done yet
      | I_cast of typ_annotated *)
    | I_rename -> ({ i with value = Adt_typ.I_rename }, s)
    | I_concat ->
        let sa =
          { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }
        in
        ({ i with value = Adt_typ.I_concat }, sa)
    | I_slice ->
        let t, lst =
          ( Type_comparable (Type_simple_comparable_type Type_string),
            drop_n Z.(of_int 3) s.stack_type )
        in
        let sa = { stack_size = s.stack_size - 2; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_slice }, sa)
    | I_pack ->
        let t, lst =
          ( Type_comparable (Type_simple_comparable_type Type_bytes),
            List.tl (List.tl s.stack_type) )
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_pack }, sa)
    | I_unpack t' ->
        let t' = Adt.type_of_parser_type t' in
        let t, lst = (Type_option t', List.tl s.stack_type) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_unpack t' }, sa)
    | I_add ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t =
          match (t1, t2) with
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_int) )
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_nat) )
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_int) ) ->
              Type_int
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_nat) ) ->
              Type_nat
          | _ -> raise (Bad_Typing "Invalid types on ADD")
        in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_add }, sa)
    | I_sub ->
        let t, lst = (Type_int, List.tl (List.tl s.stack_type)) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_sub }, sa)
    | I_mul ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t =
          match (t1, t2) with
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_int) )
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_nat) )
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_int) ) ->
              Type_int
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_nat) ) ->
              Type_nat
          | _ -> raise (Bad_Typing "Invalid types on MUL")
        in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_mul }, sa)
    | I_ediv ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t =
          match (t1, t2) with
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_int) )
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_nat) )
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_int) ) ->
              Type_option
                (Type_pair
                   ( Type_comparable (Type_simple_comparable_type Type_int),
                     Type_comparable (Type_simple_comparable_type Type_nat) ))
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_nat) ) ->
              Type_option
                (Type_pair
                   ( Type_comparable (Type_simple_comparable_type Type_nat),
                     Type_comparable (Type_simple_comparable_type Type_nat) ))
          | _ -> raise (Bad_Typing "Invalid types on EDIV")
        in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_ediv }, sa)
    | I_abs ->
        let t, lst =
          ( Type_comparable (Type_simple_comparable_type Type_int),
            List.tl s.stack_type )
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_abs }, sa)
    | I_isnat ->
        let t, lst =
          ( Type_option (Type_comparable (Type_simple_comparable_type Type_nat)),
            List.tl s.stack_type )
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_isnat }, sa)
    | I_int ->
        let t, lst = (Type_int, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_int }, sa)
    | I_neg ->
        let t, lst = (Type_int, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_neg }, sa)
    | I_lsl ->
        let t, lst = (Type_nat, List.tl (List.tl s.stack_type)) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_lsl }, sa)
    | I_lsr ->
        let t, lst = (Type_nat, List.tl (List.tl s.stack_type)) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_lsr }, sa)
    | I_or ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t =
          match (t1, t2) with
          | ( Type_comparable (Type_simple_comparable_type Type_bool),
              Type_comparable (Type_simple_comparable_type Type_bool) ) ->
              Type_bool
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_nat) ) ->
              Type_nat
          | _ -> raise (Bad_Typing "Invalid types on OR")
        in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_or }, sa)
    | I_and ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t =
          match (t1, t2) with
          | ( Type_comparable (Type_simple_comparable_type Type_bool),
              Type_comparable (Type_simple_comparable_type Type_bool) ) ->
              Type_bool
          | ( Type_comparable (Type_simple_comparable_type Type_int),
              Type_comparable (Type_simple_comparable_type Type_nat) )
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_nat) ) ->
              Type_nat
          | _ -> raise (Bad_Typing "Invalid types on AND")
        in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_and }, sa)
    | I_xor ->
        let t1, t2, lst =
          ( List.hd s.stack_type,
            List.hd (List.tl s.stack_type),
            List.tl (List.tl s.stack_type) )
        in
        let t =
          match (t1, t2) with
          | ( Type_comparable (Type_simple_comparable_type Type_bool),
              Type_comparable (Type_simple_comparable_type Type_bool) ) ->
              Type_bool
          | ( Type_comparable (Type_simple_comparable_type Type_nat),
              Type_comparable (Type_simple_comparable_type Type_nat) ) ->
              Type_nat
          | _ -> raise (Bad_Typing "Invalid types on XOR")
        in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_xor }, sa)
    | I_not ->
        let t', lst = (List.hd s.stack_type, List.tl s.stack_type) in
        let t =
          match t' with
          | Type_comparable (Type_simple_comparable_type Type_bool) -> Type_bool
          | Type_comparable (Type_simple_comparable_type Type_nat)
          | Type_comparable (Type_simple_comparable_type Type_int) ->
              Type_int
          | _ -> raise (Bad_Typing "Invalid types on NOT")
        in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_not }, sa)
    | I_compare ->
        let lst = List.tl (List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type Type_int) in
        let sa = { stack_size = s.stack_size - 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_xor }, sa)
    | I_eq ->
        let t, lst = (Type_bool, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_eq }, sa)
    | I_neq ->
        let t, lst = (Type_bool, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_neq }, sa)
    | I_lt ->
        let t, lst = (Type_bool, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_lt }, sa)
    | I_gt ->
        let t, lst = (Type_bool, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_gt }, sa)
    | I_le ->
        let t, lst = (Type_bool, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_le }, sa)
    | I_ge ->
        let t, lst = (Type_bool, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_ge }, sa)
    | I_self ->
        let t, lst =
          (Type_contract (Adt.type_of_parser_type p.param), s.stack_type)
        in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_self }, sa)
    | I_contract t' ->
        let t' = Adt.type_of_parser_type t' in
        let t, lst = (Type_option t', List.tl s.stack_type) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_contract t' }, sa)
    | I_transfer_tokens ->
        let t, lst =
          (Type_operation, List.tl (List.tl (List.tl s.stack_type)))
        in
        let sa = { stack_size = s.stack_size - 2; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_transfer_tokens }, sa)
    | I_set_delegate ->
        let t, lst = (Type_operation, List.tl s.stack_type) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_set_delegate }, sa)
    | I_create_contract _x -> assert false (* of program  FIXME: *)
    | I_implicit_account ->
        let t, lst =
          ( Type_contract
              (Type_comparable (Type_simple_comparable_type Type_unit)),
            List.tl s.stack_type )
        in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_implicit_account }, sa)
    | I_now ->
        let t, lst = (Type_timestamp, s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_now }, sa)
    | I_amount ->
        let t, lst = (Type_mutez, s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_amount }, sa)
    | I_balance ->
        let t, lst = (Type_mutez, s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_balance }, sa)
    | I_check_signature ->
        let t, lst = (Type_bool, List.tl (List.tl (List.tl s.stack_type))) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size - 2; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_check_signature }, sa)
    | I_blake2b ->
        let t, lst = (Type_bytes, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_blake2b }, sa)
    | I_sha256 ->
        let t, lst = (Type_bytes, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_sha256 }, sa)
    | I_sha512 ->
        let t, lst = (Type_bytes, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_sha512 }, sa)
    | I_hash_key ->
        let t, lst = (Type_key_hash, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_hash_key }, sa)
    | I_source ->
        let t, lst = (Type_address, s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_source }, sa)
    | I_sender ->
        let t, lst = (Type_address, s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_sender }, sa)
    | I_address ->
        let t, lst = (Type_address, List.tl s.stack_type) in
        let t = Type_comparable (Type_simple_comparable_type t) in
        let sa = { stack_size = s.stack_size; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_address }, sa)
    | I_chain_id ->
        let t, lst = (Type_chain_id, s.stack_type) in
        let sa = { stack_size = s.stack_size + 1; stack_type = t :: lst } in
        ({ i with value = Adt_typ.I_chain_id }, sa)
    | I_noop -> ({ i with value = Adt_typ.I_noop }, s)
    | I_unpair ->
        let t, lst = (List.hd s.stack_type, List.tl s.stack_type) in
        let t1, t2 =
          match t with Type_pair (t1', t2') -> (t1', t2') | _ -> assert false
        in
        let sa =
          { stack_size = s.stack_size + 1; stack_type = t1 :: t2 :: lst }
        in
        ({ i with value = Adt_typ.I_unpair }, sa)
    | _ -> assert false
  in
  let desc, stack_after = typer initial_stack p.code in
  let code = { desc; stack_after; stack_before = initial_stack } in
  {
    code;
    param = Adt.type_of_parser_type p.param;
    storage = Adt.type_of_parser_type p.storage;
  }
