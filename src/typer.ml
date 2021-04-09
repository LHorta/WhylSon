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

let rec remove_at n = function
  | [] -> []
  | h :: t -> if Z.(n = zero) then t else h :: remove_at Z.(n - one) t

let rec drop_n n = function
  | [] -> []
  | _::t as lst -> if Z.(n <= zero) then lst else drop_n Z.(n - one) t

  (* if given position is a negative number, the element will be placed at the head of the list *)
let rec insert_at x n = function
  | [] -> [x]
  | h :: t as l -> if Z.(n <= zero) then x :: l else h :: insert_at x Z.(n - one) t;;

  let rec type_extractor (_,t,_) =
    let open Michelson.Adt in
    let t = match t with
    | T_int -> T_int  
    | T_key -> T_key
    | T_unit -> T_unit
    | T_signature -> T_signature
    | T_operation -> T_operation
    | T_chain_id -> T_chain_id
    | T_nat -> T_nat
    | T_string -> T_string
    | T_bytes -> T_bytes
    | T_mutez -> T_mutez
    | T_bool -> T_bool
    | T_key_hash -> T_key_hash
    | T_timestamp -> T_timestamp
    | T_address -> T_address
    | T_never -> T_never
    | T_bls12_381_g1 -> T_bls12_381_g1
    | T_bls12_381_g2 -> T_bls12_381_g2
    | T_bls12_381_fr -> T_bls12_381_fr
    | T_option t' -> T_option (type_extractor t')
    | T_list t' -> T_list (type_extractor t')
    | T_set t' -> T_set (type_extractor t')
    | T_contract t'  -> T_contract (type_extractor t')
    | T_pair (t1, t2) -> T_pair (type_extractor t1, type_extractor t2)
    | T_or (t1, t2) -> T_or (type_extractor t1, type_extractor t2)
    | T_lambda (t1, t2) -> T_lambda (type_extractor t1, type_extractor t2)
    | T_map (t1, t2) -> T_map (type_extractor t1, type_extractor t2)
    | T_big_map (t1, t2) -> T_big_map (type_extractor t1, type_extractor t2)
    | T_ticket t' -> T_ticket (type_extractor t')
    | T_sapling_transaction n -> T_sapling_transaction n
    | T_sapling_state n -> T_sapling_state n    
  in (),t,()

let stack_checker s1 s2 =   
  List.fold_left2 (fun acc x y -> acc && type_extractor x = type_extractor y) true s1 s2

let rec string_of_type (_,t,_) = 
  let open Michelson.Adt in
    match t with
    | T_key -> "T_key"
    | T_unit -> "T_unit"
    | T_signature -> "T_signature"
    | T_option t -> "T_option ("^ string_of_type t ^")"
    | T_list t -> "T_list ("^ string_of_type t ^")"
    | T_set t -> "T_set ("^ string_of_type t ^")"
    | T_operation -> "T_operation"
    | T_contract t -> "T_Contract ("^ string_of_type t ^")"
    | T_pair (t1,t2) -> "T_pair ("^ string_of_type t1 ^", "^ string_of_type t2 ^")"
    | T_or (t1,t2) -> "T_or ("^ string_of_type t1 ^", "^ string_of_type t2 ^")"
    | T_lambda (t1,t2) -> "T_lambda ("^ string_of_type t1 ^", "^ string_of_type t2 ^")"
    | T_map (t1,t2) -> "T_map ("^ string_of_type t1 ^", "^ string_of_type t2 ^")"
    | T_big_map (t1,t2) -> "T_big_map ("^ string_of_type t1 ^", "^ string_of_type t2 ^")"
    | T_chain_id -> "T_chain_id"
    | T_int -> "T_int"
    | T_nat -> "T_nat"
    | T_string -> "T_string"
    | T_bytes -> "T_bytes"
    | T_mutez -> "T_mutez"
    | T_bool -> "T_bool"
    | T_key_hash -> "T_key_hash"
    | T_timestamp -> "T_timestamp"
    | T_address -> "T_address"
    | T_never -> "T_never"
    | T_ticket t -> "T_ticket ("^ string_of_type t ^")"
    | T_bls12_381_g1 -> "T_bls12_381_g1"
    | T_bls12_381_g2 -> "T_bls12_381_g2"
    | T_bls12_381_fr -> "T_bls12_381_fr"
    | T_sapling_transaction n -> "T_sapling_transaction ("^ Z.to_string n ^")"
    | T_sapling_state n -> "T_sapling_state ("^ Z.to_string n ^")"



let stack_printer s_name s =    
  s_name^": ["^ String.concat "; " ((List.map (fun x -> (string_of_type x)) s)@["]\n"]) 
    

exception Bad_Typing of string
let split_n n lst = 
  if Z.(n < zero) then raise (Bad_Typing "Invalid List size")  else
  let rec aux n lst acc = 
      match lst with 
      | [] -> if Z.(n > zero) then raise (Bad_Typing "List is smaller than argument") else List.rev acc,[]
      | h::t -> if Z.(n = zero) then List.rev acc,h::t else aux Z.(n - one) t (h::acc) in
  aux n lst []



let to_typed_program (p : Adt_typ.program) : Adt_typ.program_typed =
  let open Adt_typ in
  let lc,_,ant = p.code in   
  let initial_stack = { stack_size=1; stack_type=[lc , Michelson.Adt.T_pair (p.param, p.storage),ant]} in
  let rec typer s ((lc,i,ant) : (Michelson.Location.t, Michelson.Adt.annot list) Michelson.Adt.inst) =
    let open Michelson.Adt in
    match i with          
      | I_seq l ->  
         (match l with
        | [] -> (lc, Adt_typ.I_noop, ant), s
        | [hd] -> typer s hd
        | hd::tl ->
            let desc_1, s1 = typer s hd in
                let code = List.fold_left (fun code_1 i_2 -> 
                    let s_1 = code_1.stack_after in
                    let desc_2, s_2 = typer s_1 i_2 in
                    let code_2 = { desc=desc_2; stack_after=s_2; stack_before=s_1 } in
                    let x = lc,Adt_typ.I_seq (code_1, code_2),ant in
                    {desc=x; stack_after=s_2; stack_before=code_1.stack_before}) {desc = desc_1; stack_before = s; stack_after = s1}
                tl in
                code.desc, code.stack_after)
        (* Adt_typ.I_seq (code_1, code_2), s_2 *)
      | I_drop -> 
          let sa = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in
          (lc, Adt_typ.I_drop, ant), sa
      | I_drop_n n ->
          let lst = drop_n n s.stack_type in
          let sa = { stack_size = s.stack_size - (Z.to_int n); stack_type = lst } in
          (lc, Adt_typ.I_drop_n n, ant), sa
      | I_dup -> 
          let sa = { stack_size = s.stack_size + 1; stack_type = (List.hd s.stack_type)::s.stack_type } in
          (lc, Adt_typ.I_dup, ant), sa
      | I_swap -> 
          let t1,t2,lst = List.hd s.stack_type, List.hd (List.tl s.stack_type), List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size; stack_type = t2::(t1::lst) } in
          (lc, Adt_typ.I_swap, ant), sa
      | I_dig n -> 
          let t,lst = List.nth s.stack_type (Z.to_int n), remove_at n s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_dig n, ant), sa
      | I_dug n ->
          let lst = insert_at (List.hd s.stack_type) n (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size; stack_type = lst } in
          (lc, Adt_typ.I_dug n, ant), sa
      | I_push (t,d) -> 
          let lst = s.stack_type in
          (* let t' = type_extractor t in *)
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_push (t,d), ant), sa
      | I_some ->
          let t',lst = List.hd s.stack_type, List.tl s.stack_type in
          let t = (lc, T_option t', ant) in 
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_some, ant), sa
      | I_none t' ->
          let t,lst = (lc, T_option t', ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_none t', ant), sa
      | I_unit -> 
          let t,lst = (lc, T_unit, ant), s.stack_type in          
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_unit, ant), sa
      | I_if_none ((i_1, i_2)) -> 
          let s' = 
            match List.hd s.stack_type with
              | (_, T_option t', _) -> t'
              | _ -> raise (Bad_Typing "Invalid types on IF_NONE") in
          let s_1' = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in
          let s_2' = { stack_size = s.stack_size; stack_type = s'::(List.tl s.stack_type) } in
          let desc_1, s_1 = typer s_1' (i_1) in
          let desc_2, s_2 = typer s_2' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s_1' } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s_2' } in
          if stack_checker s_1.stack_type s_2.stack_type then
          (lc, Adt_typ.I_if_none (code_1, code_2), ant), s_2 else raise (Bad_Typing "Type of IF_NONE branches do not match")
      | I_pair -> 
          let t1,t2,lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = lc,T_pair (t1,t2),ant in 
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_pair, ant), sa
      | I_car ->
          let t',lst = List.hd s.stack_type, List.tl s.stack_type in
          let t = (match t' with
            | _,T_pair (a, _),_ -> a              
            | _ -> assert false) in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_car, ant), sa
      | I_cdr ->
          let t',lst = List.hd s.stack_type, List.tl s.stack_type in
          let t = (match t' with
            | _, T_pair (_, b),_ -> b
            | _ -> assert false) in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_cdr, ant), sa
      | I_left t' ->       
          let t,lst = (lc, T_or (List.hd s.stack_type, t'), ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_left t', ant), sa
      | I_right t' ->   (* checked till here *)    
          let t,lst = (lc, T_or (t', List.hd s.stack_type), ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_right t', ant), sa
      | I_if_left ((i_1, i_2)) -> 
          let s' = 
            match List.hd s.stack_type with
              | _, (T_or (l,r)),_ -> l,r
              | _ -> raise (Bad_Typing "Invalid types on IF_LEFT") in
          let s_1' = { s with stack_type = (fst s')::(List.tl s.stack_type) } in
          let s_2' = { s with stack_type = (snd s')::(List.tl s.stack_type) } in
          let desc_1, s_1 = typer s_1' (i_1) in
          let desc_2, s_2 = typer s_2' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s_1' } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s_2' } in
          if stack_checker s_1.stack_type s_2.stack_type then
          (lc, Adt_typ.I_if_left (code_1, code_2), ant), s_2 else           
            raise (Bad_Typing "Type of IF_LEFT branches do not match")
      | I_nil t' ->
          let t,lst = (lc,T_list t',ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_nil t', ant), sa
      | I_cons ->
          let lst = List.tl s.stack_type in (* no need to change type because it is on position 1 *)
          let sa = { stack_size = s.stack_size - 1; stack_type = lst } in
          (lc, Adt_typ.I_cons, ant), sa
      | I_if_cons ((i_1, i_2)) ->
          let s' = match List.hd s.stack_type with 
                  | _,(T_list t'),_ -> t'
                  | _ -> raise (Bad_Typing "Invalid types on IF_CONS") in
          let s_1' = { stack_size = s.stack_size + 1; stack_type = s'::s.stack_type } in
          let s_2' = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in
          let desc_1, s_1 = typer s_1' (i_1) in
          let desc_2, s_2 = typer s_2' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s_1';  } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s_2';  } in
          if stack_checker s_1.stack_type s_2.stack_type then            
          (lc, Adt_typ.I_if_cons (code_1, code_2), ant), s_2 else
            let str1 = stack_printer "s1" s_1.stack_type in
            let str2 = stack_printer "s2" s_2.stack_type in           
            let () = Printf.printf "%s\n%s\n%s\n" str1 str2 (string_of_bool (stack_checker s_1.stack_type s_2.stack_type)) in 
            raise (Bad_Typing "Type of IF_CONS branches do not match")
      | I_size -> 
          let t,lst = (lc, T_nat, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_size, ant), sa
      | I_empty_set t' -> 
          let t = lc, T_set t', ant in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::s.stack_type } in
          (lc, Adt_typ.I_empty_set t', ant), sa
      | I_empty_map (tc',t') -> 
          let t = lc, T_map (tc', t'), ant in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::s.stack_type } in
          (lc, Adt_typ.I_empty_map (tc',t'), ant), sa
      | I_empty_big_map (tc',t') -> 
          let t = lc, T_big_map (tc', t'), ant in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::s.stack_type } in
          (lc, Adt_typ.I_empty_big_map (tc',t'), ant), sa
      (*| I_map of inst_annotated FIXME: not done yet *)
      | I_iter (i) -> (* TODO: check not sure*)
          let desc, s' = typer ({ stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type}) (i) in
          let sa = { stack_size = s'.stack_size + 1; stack_type = (List.hd s.stack_type)::s'.stack_type } in 
          let code = { desc = desc; stack_after = sa; stack_before = s; } in
          (lc, Adt_typ.I_iter code, ant), sa
      | I_mem -> (* TODO: check not sure*)
          let t, lst = (lc,T_bool,ant), drop_n Z.(of_int 2) s.stack_type in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_mem, ant), sa
      | I_get -> (* TODO: check not sure*)
          let t = 
            match List.hd (List.tl s.stack_type) with
              | _, (T_map (_c,t') | T_big_map (_c, t')),_ -> (lc, T_option t', ant)
              | _ -> raise (Bad_Typing "Invalid types on GET") in
          let lst = drop_n Z.(of_int 2) s.stack_type in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_get, ant), sa
      | I_update ->
          let lst = drop_n Z.(of_int 2) s.stack_type in
          let sa = { stack_size = s.stack_size - 2; stack_type = lst } in
          (lc, Adt_typ.I_update, ant), sa
      | I_if ((i_1, i_2)) -> (* TODO: check not sure*)
          let s' = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in        
          let desc_1, s_1 = typer s' (i_1) in
          let desc_2, s_2 = typer s' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s'; } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s'; } in
          if stack_checker s_1.stack_type s_2.stack_type then
          (lc, Adt_typ.I_if (code_1, code_2), ant), s_2 else raise (Bad_Typing "Type of IF branches do not match")
      | I_loop (i) -> (* TODO: check not sure FIXME: *)
          let desc, s' = typer ({ stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }) (i) in          
          let code = { desc = desc; stack_after = s'; stack_before = s;  } in
          (lc, Adt_typ.I_loop code, ant), s'
      (*| I_loop_left of inst_annotated FIXME: not done *)
      | I_lambda (t1,t2,(i)) -> (* TODO: check why s' is not being used *)
          let t,lst = (lc, T_lambda (t1, t2), ant), s.stack_type in    
          let desc, _s' =  typer s (i) in 
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          let code = { desc = desc; stack_before = s; stack_after = sa;  } in 
          (lc, Adt_typ.I_lambda (t1,t2,code), ant), sa
      | I_exec -> (* TODO: check *)
          let t',lst = List.hd (List.tl s.stack_type), drop_n Z.(of_int 2) s.stack_type in
          let t = match t' with
                    | _, T_lambda (_t1,t2),_ -> t2
                    | _ -> raise(Bad_Typing "Invalid types on EXEC") in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_exec, ant), sa
      | I_dip (i) ->
          let desc, s' = typer ({ stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type}) (i) in
          let sa = { stack_size = s'.stack_size + 1; stack_type = (List.hd s.stack_type)::s'.stack_type } in 
          let code = { desc = desc; stack_after = sa; stack_before=s;  } in
          (lc, Adt_typ.I_dip code, ant), sa
      | I_dip_n (n,(i)) ->
          if Z.(n = zero) then
            let desc,sa = typer ({stack_size = s.stack_size; stack_type = s.stack_type}) (i) in 
            let code = { desc = desc; stack_after = sa; stack_before = s; } in 
            (lc, Adt_typ.I_dip_n (n, code), ant), sa
          else if Z.(n = one) then
            let desc, s' = typer ({ stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type}) i in
            let sa = { stack_size = s'.stack_size + 1; stack_type = (List.hd s.stack_type)::s'.stack_type } in 
            let code = { desc = desc; stack_after = sa; stack_before=s;  } in
            (lc, Adt_typ.I_dip_n (n,code), ant), sa
          else
            let protected_stack,execution_stack = split_n n s.stack_type in
            let desc, s' = typer ({ stack_size = s.stack_size - Z.(to_int n); stack_type = execution_stack}) i in
            let sa = { stack_size = s'.stack_size + Z.(to_int n); stack_type = protected_stack@s'.stack_type } in 
            let code = { desc = desc; stack_after = sa; stack_before=s;  } in
            (lc, Adt_typ.I_dip_n (n,code), ant), sa
      (*| I_failwith FIXME: not done yet
      | I_cast of typ_annotated *)
      | I_rename -> 
          (lc, Adt_typ.I_rename, ant), s
      | I_concat ->        
          let sa = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in
          (lc, Adt_typ.I_concat, ant), sa
      | I_slice ->
          let t, lst = (lc, T_string, ant), drop_n Z.(of_int 3) s.stack_type  in
          let sa = { stack_size = s.stack_size - 2; stack_type = t::lst } in
          (lc, Adt_typ.I_slice,  ant),sa
      | I_pack ->
          let t,lst = (lc, T_bytes, ant),List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_pack, ant), sa
      | I_unpack t' ->
          let t,lst = (lc, T_option t',ant), List.tl s.stack_type in            
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_unpack t', ant), sa
      | I_add -> 
          let (_lc1, t1, _ant1),(_lc2, t2,_ant2),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
            | T_int, T_int
            | T_int, T_nat
            | T_nat, T_int -> lc, T_int, ant
            | T_nat, T_nat -> lc, T_nat, ant
            | _ -> raise (Bad_Typing "Invalid types on ADD")) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_add, ant), sa
      | I_sub ->
          let t,lst = (lc,T_int, ant),List.tl (List.tl s.stack_type) in            
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_sub, ant), sa
      | I_mul ->
          let (_, t1, _),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
            | T_int, T_int
            | T_int, T_nat
            | T_nat, T_int -> lc, T_int, ant
            | T_nat, T_nat -> lc, T_nat, ant
            | _ -> raise (Bad_Typing "Invalid types on MUL")) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc,Adt_typ.I_mul, ant), sa
      | I_ediv ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
            let t = (match t1,t2 with
              | T_int, T_int
              | T_int, T_nat
              | T_nat, T_int -> 
                    T_option (lc, T_pair  ((lc, T_int, ant),
                                       (lc, T_nat, ant)), ant)
              |  T_nat, T_nat -> 
                    T_option (lc, T_pair  ((lc, T_nat, ant),
                                       (lc, T_nat, ant)), ant)
              | _ -> raise (Bad_Typing "Invalid types on EDIV")) in
            let sa = { stack_size = s.stack_size - 1; stack_type = (lc, t, ant)::lst } in
            (lc, Adt_typ.I_ediv, ant), sa
      | I_abs -> 
          let t,lst = (lc, T_int, ant),List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_abs, ant), sa
      | I_isnat ->
          let t,lst = (lc, T_option (lc, T_nat, ant), ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_isnat, ant), sa
      | I_int ->
          let t,lst = (lc, T_int, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_int, ant), sa
      | I_neg ->
          let t,lst = (lc, T_int, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_neg, ant), sa
      | I_lsl ->
          let t,lst = (lc, T_nat, ant), List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size-1; stack_type = t::lst } in
          (lc, Adt_typ.I_lsl, ant), sa
      | I_lsr ->
          let t,lst = (lc, T_nat, ant), List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size-1; stack_type = t::lst } in
          (lc, Adt_typ.I_lsr, ant), sa
      | I_or ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
              | T_bool, T_bool -> 
                  lc, T_bool, ant
              | T_nat, T_nat -> 
                  lc, T_nat, ant
              | _ -> raise (Bad_Typing "Invalid types on OR")) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_or, ant), sa
      | I_and ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
              | T_bool, T_bool -> 
                  lc, T_bool, ant
              | T_int, T_nat                   
              | T_nat, T_nat -> 
                  lc, T_nat, ant
              | _ -> raise (Bad_Typing "Invalid types on AND")) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_and, ant), sa
      | I_xor ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
              | T_bool, T_bool -> 
                  lc, T_bool, ant
              | T_nat, T_nat -> 
                  lc, T_nat, ant
              | _ -> raise (Bad_Typing "Invalid types on XOR")) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_xor, ant), sa
      | I_not ->
          let (_, t', _),lst = List.hd s.stack_type, List.tl s.stack_type in
          let t = (match t' with
            | T_bool -> lc, T_bool, ant
            | T_nat
            | T_int -> lc, T_int, ant
            | _ -> raise (Bad_Typing "Invalid types on NOT")) in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_not, ant), sa
      | I_compare ->
          let lst = List.tl (List.tl s.stack_type) in
          let t = lc, T_int, ant in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_xor, ant), sa
      | I_eq ->
          let t,lst = (lc, T_bool, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_eq, ant), sa
      | I_neq ->
          let t,lst = (lc, T_bool, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_neq, ant), sa
      | I_lt ->
          let t,lst = (lc, T_bool, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_lt, ant), sa
      | I_gt ->
          let t,lst = (lc, T_bool, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_gt, ant), sa
      | I_le ->
          let t,lst = (lc, T_bool, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_le, ant), sa
      | I_ge ->
          let t,lst = (lc, T_bool, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_ge, ant), sa
      | I_self ->
          let t,lst = (lc, T_contract p.param, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_self, ant), sa
      | I_contract t' ->
          let t,lst = (lc, T_option t', ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_contract t', ant), sa
      | I_transfer_tokens ->
          let t,lst = (lc, T_operation, ant), List.tl (List.tl (List.tl s.stack_type)) in
          let sa = { stack_size = s.stack_size - 2; stack_type = t::lst } in
          (lc, Adt_typ.I_transfer_tokens, ant), sa
      | I_set_delegate ->
          let t,lst = (lc, T_operation, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_set_delegate, ant), sa
      | I_create_contract _x -> assert false (* of program  FIXME: *)
      | I_implicit_account ->
          let t,lst = (lc, T_contract (lc, T_unit, ant), ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_implicit_account, ant), sa
      | I_now ->
          let t,lst = (lc, T_timestamp, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_now, ant), sa
      | I_amount ->
          let t,lst = (lc, T_mutez, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_amount, ant), sa
      | I_balance ->
          let t,lst = (lc, T_mutez, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_balance, ant), sa
      | I_check_signature ->
        let t,lst = (lc, T_bool, ant), List.tl (List.tl (List.tl s.stack_type)) in
        let sa = { stack_size = s.stack_size - 2; stack_type = t::lst } in
        (lc, Adt_typ.I_check_signature, ant), sa
      | I_blake2b ->
          let t,lst = (lc,  T_bytes, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_blake2b, ant), sa
      | I_sha256 ->
          let t,lst = (lc, T_bytes, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_sha256, ant), sa
      | I_sha512 ->
          let t,lst = (lc, T_bytes, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_sha512, ant), sa
      | I_hash_key ->
          let t,lst = (lc, T_key_hash, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_hash_key, ant), sa
      | I_source ->
          let t,lst = (lc, T_address, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_source, ant), sa
      | I_sender ->
          let t,lst = (lc, T_address, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_sender, ant), sa
      | I_address ->
          let t,lst = (lc, T_address, ant), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_address, ant), sa
      | I_chain_id ->
          let t,lst = (lc, T_chain_id, ant), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_chain_id, ant), sa
      | I_noop -> 
          (lc, Adt_typ.I_noop, ant), s
      | I_unpair -> 
          let (_, t, _),lst = List.hd s.stack_type, List.tl s.stack_type in
            let (t1),(t2) = (match (t) with
              | T_pair ((t1'), (t2')) -> ((t1'), (t2'))
              | _ -> assert false) in
            let sa = { stack_size = s.stack_size + 1; stack_type = (t1)::((t2)::lst) } in
            (lc, Adt_typ.I_unpair, ant), sa
      | _ -> assert false
   in
   let desc, stack_after = typer initial_stack (p.code) in
   let code = { desc = desc; stack_after = stack_after; stack_before = initial_stack } in
   { code; param=p.param; storage=p.storage }
