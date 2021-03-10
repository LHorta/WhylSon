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
  | h::t as lst -> if Z.(n <= zero) then lst else drop_n Z.(n - one) t

  (* if given position is a negative number, the element will be placed at the head of the list *)
let rec insert_at x n = function
  | [] -> [x]
  | h :: t as l -> if Z.(n <= zero) then x :: l else h :: insert_at x Z.(n - one) t;;

let stack_checker s1 s2 = 
  List.fold_left2 (fun acc x y -> acc && x=y) true s1 s2

exception Bad_Typing
let split_n n lst = 
  if Z.(n < zero) then raise Bad_Typing else
  let rec aux n lst acc = 
      match lst with 
      | [] -> if Z.(n > zero) then raise Bad_Typing else List.rev acc,[]
      | h::t -> if Z.(n = zero) then List.rev acc,h::t else aux Z.(n - one) t (h::acc) in
  aux n lst []

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

let to_typed_program (p : Adt_typ.program) : Adt_typ.program_typed =
  let open Adt_typ in
  let param = type_extractor p.param in  
  let storage = type_extractor p.storage in
  let initial_stack = { stack_size=1; stack_type=[ (), Michelson.Adt.T_pair (param, storage),()]} in
  let rec typer s ((lc,i,ant) : (Michelson.Location.t, Michelson.Adt.annot list) Michelson.Adt.inst) =
    let open Michelson.Adt in
    match i with          
      | I_seq l ->         
        let code = List.fold_left (fun code_1 i_2 -> 
            let desc_1, s_1 = code_1.desc, code_1.stack_after in
            let desc_2, s_2 = typer s_1 i_2 in
            let code_2 = { desc=desc_2; stack_after=s_2; stack_before=s_1 } in
            let x = lc,Adt_typ.I_seq (code_1, code_2),ant in
            {desc=x; stack_after=s_2; stack_before=code_1.stack_before}) {desc=lc,Adt_typ.I_noop,ant; stack_before=s;stack_after=s}
        l in
        code.desc, code.stack_after
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
          let t' = type_extractor t in
          let sa = { stack_size = s.stack_size + 1; stack_type = t'::lst } in
          (lc, Adt_typ.I_push (t,d), ant), sa
      | I_some ->
          let t',lst = List.hd s.stack_type, List.tl s.stack_type in
          let t = ((), T_option t', ()) in 
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_some, ant), sa
      | I_none t' ->
          let t,lst = ((), T_option (type_extractor t'), ()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_none t', ant), sa
      | I_unit -> 
          let t,lst = ((), T_unit, ()), s.stack_type in          
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_unit, ant), sa
      | I_if_none ((i_1, i_2)) -> 
          let s' = 
            match List.hd s.stack_type with
              | (_, T_option t', _) -> t'
              | _ -> raise Bad_Typing in
          let s_1' = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in
          let s_2' = { stack_size = s.stack_size; stack_type = s'::(List.tl s.stack_type) } in
          let desc_1, s_1 = typer s_1' (i_1) in
          let desc_2, s_2 = typer s_2' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s_1' } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s_2' } in
          if stack_checker s_1.stack_type s_2.stack_type then
          (lc, Adt_typ.I_if_none (code_1, code_2), ant), s_2 else raise Bad_Typing
      | I_pair -> 
          let t1,t2,lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (),T_pair (type_extractor t1, type_extractor t2),() in 
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
          let t,lst = ((), T_or (List.hd s.stack_type, type_extractor t'), ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_left t', ant), sa
      | I_right t' ->   (* checked till here *)    
          let t,lst = ((), T_or (type_extractor t', List.hd s.stack_type), ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_right t', ant), sa
      | I_if_left ((i_1, i_2)) -> 
          let s' = 
            match List.hd s.stack_type with
              | _, (T_or (l,r)),_ -> l,r
              | _ -> raise Bad_Typing in
          let s_1' = { s with stack_type = (fst s')::(List.tl s.stack_type) } in
          let s_2' = { s with stack_type = (snd s')::(List.tl s.stack_type) } in
          let desc_1, s_1 = typer s_1' (i_1) in
          let desc_2, s_2 = typer s_2' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s_1' } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s_2' } in
          if stack_checker s_1.stack_type s_2.stack_type then
          (lc, Adt_typ.I_if_left (code_1, code_2), ant), s_2 else raise Bad_Typing
      | I_nil t' ->
          let t,lst = ((),T_list (type_extractor t'),()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_nil t', ant), sa
      | I_cons ->
          let lst = List.tl s.stack_type in (* no need to change type because it is on position 1 *)
          let sa = { stack_size = s.stack_size - 1; stack_type = lst } in
          (lc, Adt_typ.I_cons, ant), sa
      | I_if_cons ((i_1, i_2)) ->
          let s' = match List.hd s.stack_type with 
                  | _,(T_list t'),_ -> t'
                  | _ -> raise Bad_Typing in
          let s_1' = { stack_size = s.stack_size + 1; stack_type = s'::s.stack_type } in
          let s_2' = { stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type } in
          let desc_1, s_1 = typer s_1' (i_1) in
          let desc_2, s_2 = typer s_2' (i_2) in
          let code_1 = { desc = desc_1; stack_after = s_1; stack_before = s_1';  } in
          let code_2 = { desc = desc_2; stack_after = s_2; stack_before = s_2';  } in
          if stack_checker s_1.stack_type s_2.stack_type then
          (lc, Adt_typ.I_if_cons (code_1, code_2), ant), s_2 else raise Bad_Typing
      | I_size -> 
          let t,lst = ((), T_nat, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_size, ant), sa
      | I_empty_set t' -> 
          let t = (), T_set (type_extractor t'),() in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::s.stack_type } in
          (lc, Adt_typ.I_empty_set t', ant), sa
      | I_empty_map (tc',t') -> 
          let t = (), T_map (type_extractor tc', type_extractor t'),() in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::s.stack_type } in
          (lc, Adt_typ.I_empty_map (tc',t'), ant), sa
      | I_empty_big_map (tc',t') -> 
          let t = (), T_big_map (type_extractor tc', type_extractor t'),() in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::s.stack_type } in
          (lc, Adt_typ.I_empty_big_map (tc',t'), ant), sa
      (*| I_map of inst_annotated FIXME: not done yet *)
      | I_iter (i) -> (* TODO: check not sure*)
          let desc, s' = typer ({ stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type}) (i) in
          let sa = { stack_size = s'.stack_size + 1; stack_type = (List.hd s.stack_type)::s'.stack_type } in 
          let code = { desc = desc; stack_after = sa; stack_before = s; } in
          (lc, Adt_typ.I_iter code, ant), sa
      | I_mem -> (* TODO: check not sure*)
          let t, lst = ((),T_bool,()), drop_n Z.(of_int 2) s.stack_type in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_mem, ant), sa
      | I_get -> (* TODO: check not sure*)
          let t = 
            match List.hd (List.tl s.stack_type) with
              | _, (T_map (c,t') | T_big_map (c, t')),_ -> ((), T_option (type_extractor t'),())
              | _ -> raise Bad_Typing in
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
          (lc, Adt_typ.I_if (code_1, code_2), ant), s_2 else raise Bad_Typing
      | I_loop (i) -> (* TODO: check not sure FIXME: *)
          let desc, s' = typer ({ stack_size = s.stack_size - 1; stack_type = List.tl s.stack_type }) (i) in          
          let code = { desc = desc; stack_after = s'; stack_before = s;  } in
          (lc, Adt_typ.I_loop code, ant), s'
      (*| I_loop_left of inst_annotated FIXME: not done *)
      | I_lambda (t1,t2,(i)) -> (* TODO: check*)
          let t,lst = ((), T_lambda (type_extractor t1,type_extractor t2), ()), s.stack_type in    
          let desc, s' =  typer s (i) in 
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          let code = { desc = desc; stack_before = s; stack_after = sa;  } in 
          (lc, Adt_typ.I_lambda (t1,t2,code), ant), sa
      | I_exec -> (* TODO: check *)
          let t',lst = List.hd (List.tl s.stack_type), drop_n Z.(of_int 2) s.stack_type in
          let t = match t' with
                    | _, T_lambda (t1,t2),_ -> t2
                    | _ -> raise Bad_Typing in
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
          let t, lst = ((), T_string, ()), drop_n Z.(of_int 3) s.stack_type  in
          let sa = { stack_size = s.stack_size - 2; stack_type = t::lst } in
          (lc, Adt_typ.I_slice,  ant),sa
      | I_pack ->
          let t,lst = ((), T_bytes, ()),List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_pack, ant), sa
      | I_unpack t' ->
          let t,lst = ((), T_option (type_extractor t'),()), List.tl s.stack_type in            
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_unpack t', ant), sa
      | I_add -> 
          let (_, t1, _),(_, t2, _),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
            | T_int, T_int
            | T_int, T_nat
            | T_nat, T_int -> (), T_int, ()
            | T_nat, T_nat -> (), T_nat, ()
            | _ -> raise Bad_Typing) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_add, ant), sa
      | I_sub ->
          let t,lst = ((),T_int, ()),List.tl (List.tl s.stack_type) in            
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_sub, ant), sa
      | I_mul ->
          let (_, t1, _),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
            | T_int, T_int
            | T_int, T_nat
            | T_nat, T_int -> (), T_int, ()
            | T_nat, T_nat -> (), T_nat, ()
            | _ -> raise Bad_Typing) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc,Adt_typ.I_mul, ant), sa
      | I_ediv ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
            let t = (match t1,t2 with
              | T_int, T_int
              | T_int, T_nat
              | T_nat, T_int -> 
                    T_option ((), T_pair  (((), T_int, ()),
                                       ((), T_nat, ())), ())
              |  T_nat, T_nat -> 
                    T_option ((), T_pair  (((), T_nat, ()),
                                       ((), T_nat, ())), ())
              | _ -> raise Bad_Typing) in
            let sa = { stack_size = s.stack_size - 1; stack_type = ((), t, ())::lst } in
            (lc, Adt_typ.I_ediv, ant), sa
      | I_abs -> 
          let t,lst = ((), T_int, ()),List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_abs, ant), sa
      | I_isnat ->
          let t,lst = ((), T_option ((), T_nat, ()), ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_isnat, ant), sa
      | I_int ->
          let t,lst = ((), T_int, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_int, ant), sa
      | I_neg ->
          let t,lst = ((), T_int, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_neg, ant), sa
      | I_lsl ->
          let t,lst = ((), T_nat, ()), List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size-1; stack_type = t::lst } in
          (lc, Adt_typ.I_lsl, ant), sa
      | I_lsr ->
          let t,lst = ((), T_nat, ()), List.tl (List.tl s.stack_type) in
          let sa = { stack_size = s.stack_size-1; stack_type = t::lst } in
          (lc, Adt_typ.I_lsr, ant), sa
      | I_or ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
              | T_bool, T_bool -> 
                  (), T_bool, ()
              | T_nat, T_nat -> 
                  (), T_nat, ()
              | _ -> raise Bad_Typing) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_or, ant), sa
      | I_and ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
              | T_bool, T_bool -> 
                  (), T_bool, ()
              | T_int, T_nat                   
              | T_nat, T_nat -> 
                  (), T_nat, ()
              | _ -> raise Bad_Typing) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_and, ant), sa
      | I_xor ->
          let (_, t1,_),(_, t2,_),lst = List.hd s.stack_type, List.hd (List.tl s.stack_type),List.tl (List.tl s.stack_type) in
          let t = (match t1,t2 with
              | T_bool, T_bool -> 
                  (), T_bool, ()
              | T_nat, T_nat -> 
                  (), T_nat, ()
              | _ -> raise Bad_Typing) in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_xor, ant), sa
      | I_not ->
          let (_, t', _),lst = List.hd s.stack_type, List.tl s.stack_type in
          let t = (match t' with
            | T_bool -> (), T_bool, ()
            | T_nat
            | T_int -> (), T_int, ()
            | _ -> raise Bad_Typing) in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_not, ant), sa
      | I_compare ->
          let lst = List.tl (List.tl s.stack_type) in
          let t = (), T_int, () in
          let sa = { stack_size = s.stack_size - 1; stack_type = t::lst } in
          (lc, Adt_typ.I_xor, ant), sa
      | I_eq ->
          let t,lst = ((), T_bool, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_eq, ant), sa
      | I_neq ->
          let t,lst = ((), T_bool, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_neq, ant), sa
      | I_lt ->
          let t,lst = ((), T_bool, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_lt, ant), sa
      | I_gt ->
          let t,lst = ((), T_bool, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_gt, ant), sa
      | I_le ->
          let t,lst = ((), T_bool, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_le, ant), sa
      | I_ge ->
          let t,lst = ((), T_bool, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_ge, ant), sa
      | I_self ->
          let t,lst = ((), T_contract (type_extractor p.param), ()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_self, ant), sa
      | I_contract t' ->
          let t,lst = ((), T_option (type_extractor t'), ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_contract t', ant), sa
      | I_transfer_tokens ->
          let t,lst = ((), T_operation, ()), List.tl (List.tl (List.tl s.stack_type)) in
          let sa = { stack_size = s.stack_size - 2; stack_type = t::lst } in
          (lc, Adt_typ.I_transfer_tokens, ant), sa
      | I_set_delegate ->
          let t,lst = ((), T_operation, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_set_delegate, ant), sa
      | I_create_contract x -> assert false (* of program  FIXME: *)
      | I_implicit_account ->
          let t,lst = ((), T_contract ((), T_unit, ()), ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_implicit_account, ant), sa
      | I_now ->
          let t,lst = ((), T_timestamp,()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_now, ant), sa
      | I_amount ->
          let t,lst = ((), T_mutez, ()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_amount, ant), sa
      | I_balance ->
          let t,lst = ((), T_mutez, ()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_balance, ant), sa
      | I_check_signature ->
        let t,lst = ((), T_bool, ()), List.tl (List.tl (List.tl s.stack_type)) in
        let sa = { stack_size = s.stack_size - 2; stack_type = t::lst } in
        (lc, Adt_typ.I_check_signature, ant), sa
      | I_blake2b ->
          let t,lst = ((),  T_bytes, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_blake2b, ant), sa
      | I_sha256 ->
          let t,lst = ((), T_bytes, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_sha256, ant), sa
      | I_sha512 ->
          let t,lst = ((), T_bytes, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_sha512, ant), sa
      | I_hash_key ->
          let t,lst = ((), T_key_hash, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_hash_key, ant), sa
      | I_source ->
          let t,lst = ((), T_address, ()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_source, ant), sa
      | I_sender ->
          let t,lst = ((), T_address, ()), s.stack_type in
          let sa = { stack_size = s.stack_size + 1; stack_type = t::lst } in
          (lc, Adt_typ.I_sender, ant), sa
      | I_address ->
          let t,lst = ((), T_address, ()), List.tl s.stack_type in
          let sa = { stack_size = s.stack_size; stack_type = t::lst } in
          (lc, Adt_typ.I_address, ant), sa
      | I_chain_id ->
          let t,lst = ((), T_chain_id, ()), s.stack_type in
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
