open Why3
open Michelson
open Adt
open Ptree
open Number

let mk_id id_str =
  { id_str; id_ats = []; id_loc = Loc.dummy_position }

let mk_expr ?(expr_loc = Loc.dummy_position) expr_desc =
  { expr_desc; expr_loc }

let mk_pat pat_desc =
  { pat_desc; pat_loc = Loc.dummy_position }

let id_stack = mk_id "__stack__"

let id_fuel = mk_id "__fuel__"

let q_fuel = Qident id_fuel

let q_stack = Qident id_stack

let e_stack = mk_expr (Eident q_stack)

let e_fuel = mk_expr (Eident q_fuel)

let id_stack_t = mk_id "stack_t"

let stack_ty = PTtyapp (Qident id_stack_t, [])

let id_int = mk_id "int"

let int_ty = PTtyapp (Qident id_int, [])

let stack_binder = Loc.dummy_position, Some id_stack, false, Some stack_ty

let fuel_binder = Loc.dummy_position, Some id_fuel, false, Some int_ty

let empty_spec = {
  sp_pre     = [];
  sp_post    = [];
  sp_xpost   = [];
  sp_reads   = [];
  sp_writes  = [];
  sp_alias   = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false;
}

(* TODO: check with mario *)
let mk_term t = { term_desc = t; term_loc = Loc.dummy_position }

let mk_const i =
  Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = BigInt.of_int i })

let mk_tconst i = mk_term (Tconst (mk_const i))

let mk_tapp f l = mk_term (Tidapp(f,l))

let eq_symb = (Qident (mk_id "infix ="))

let gt_symb = (Qident (mk_id ("infix >")))

let t_stack = mk_term (Tident q_stack)

let t_fuel = mk_term (Tident q_fuel)

let t_result = mk_term (Tident (Qident(mk_id "result")))

let len_stack  = mk_tapp (Qident (mk_id "length")) [t_stack]
let len_stack  = mk_tapp (Qident (mk_id "length")) [t_stack]
let len_result = mk_tapp (Qident (mk_id "length")) [t_result]

let top_input_stack = mk_tapp (Qident (mk_id "mixfix []")) [t_stack;mk_tconst 0]
(* let top_input_stack = mk_tapp (Qident (mk_id "peek")) [t_stack]  *)


let pre_len  = mk_tapp eq_symb [len_stack;mk_tconst 1]
let pre_fuel = mk_tapp gt_symb [t_fuel;mk_tconst 0]
let post_len = mk_tapp eq_symb [len_result;mk_tconst 1]

let mk_pre_typ t1 t2 = 
  let top_input_stack = mk_tapp (Qident (mk_id "mixfix []")) [t_stack;mk_tconst 0] in
  let d_field_s0 = mk_tapp (Qident (mk_id "d")) [top_input_stack] in
  let typ_stack = mk_tapp (Qident (mk_id "typ_infer")) [d_field_s0] in
  let p = mk_term (Tidapp (Qident (mk_id "Pair_t"), [t1;t2])) in
  mk_tapp eq_symb [typ_stack;p]  

let mk_post_typ t =  
  let top_result_stack = mk_tapp (Qident (mk_id "mixfix []")) [t_result;mk_tconst 0] in
  let d_field_s0 = mk_tapp (Qident (mk_id "d")) [top_result_stack] in
  let typ_stack = mk_tapp (Qident (mk_id "typ_infer")) [d_field_s0] in
  let opt_t = mk_term (Tidapp (Qident (mk_id "Operation_t"), [])) in
  let lst_t = mk_term (Tidapp (Qident (mk_id "List_t"), [opt_t])) in
  let p = mk_term (Tidapp (Qident (mk_id "Pair_t"), [lst_t;t])) in
  Loc.dummy_position,[mk_pat (Pvar (mk_id "result")),mk_tapp eq_symb [typ_stack;p]]    

let stack_fuel_args = [e_stack; e_fuel]

let use_axiomatic = let axiomatic_sem = mk_id "AxiomaticSem" in
  let q_axiomatic = Qdot (Qident (mk_id "axiomatic"), axiomatic_sem) in
  Duseimport (Loc.dummy_position, false, [q_axiomatic, None])

let use_data_types = let data_types = mk_id "DataTypes" in
  let q_data_types = Qdot (Qident (mk_id "dataTypes"), data_types) in
  Duseimport (Loc.dummy_position, false, [q_data_types, None])

let use_seq = let seq_id = mk_id "Seq" in
  let q_seq = Qdot (Qident (mk_id "seq"), seq_id) in
  Duseimport (Loc.dummy_position, false, [q_seq, None])

let use_int = let int_id = mk_id "Int" in
  let q_int = Qdot (Qident (mk_id "int"), int_id) in
  Duseimport (Loc.dummy_position, false, [q_int, None])

let use_nat = let nat_id = mk_id "Natural" in
  let q_nat = Qdot (Qident (mk_id "natural"), nat_id) in
  Duseimport (Loc.dummy_position, false, [q_nat, None])

let simple_comparable_type = function
  | T_int ->
      mk_expr (Eidapp (Qident (mk_id "Int_t"), []))
  | T_nat ->
      mk_expr (Eidapp (Qident (mk_id "Nat_t"), []))
  | T_string ->
      mk_expr (Eidapp (Qident (mk_id "String_t"), []))
  | T_bytes ->
      mk_expr (Eidapp (Qident (mk_id "Bytes_t"), []))
  | T_mutez ->
      mk_expr (Eidapp (Qident (mk_id "Mutez_t"), []))
  | T_bool ->
      mk_expr (Eidapp (Qident (mk_id "Bool_t"), []))
  | T_key_hash ->
      mk_expr (Eidapp (Qident (mk_id "Key_hash_t"), []))
  | T_timestamp ->
      mk_expr (Eidapp (Qident (mk_id "Timestamp_t"), []))
  | T_address->
      mk_expr (Eidapp (Qident (mk_id "Address_t"), []))

(* TODO: deal with annotations *)
let simple_comparable_type_annotated (t,_anot) = 
 simple_comparable_type t

let rec comparable_type = function
  | T_simple_comparable_type t -> 
      simple_comparable_type t
  | T_comparable_pair (sAnot, cAnot) -> 
      let car_expr_t = simple_comparable_type_annotated sAnot in
      let cdr_expr_t = comparable_type_annotated cAnot in
      mk_expr (Eidapp (Qident (mk_id "Pair_t"), [car_expr_t;cdr_expr_t]))

(* TODO: deal with annotations *)
and comparable_type_annotated (t,_anot) = 
  comparable_type t

and typ = function
  | T_comparable t ->
      let t = comparable_type t in 
			mk_expr (Eidapp (Qident (mk_id "Comparable_t"), [t]))
  | T_key ->
      mk_expr (Eidapp (Qident (mk_id "Key_t"), []))
  | T_unit ->
      mk_expr (Eidapp (Qident (mk_id "Unit_t"), []))
  | T_signature ->
      mk_expr (Eidapp (Qident (mk_id "Signature_t"), []))
  | T_option t ->
      let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "Option_t"), [inner_type]))
  | T_list t ->
      let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "List_t"), [inner_type]))
  | T_set ct ->
      let inner_type = comparable_type_annotated ct in
      mk_expr (Eidapp (Qident (mk_id "Option_t"), [inner_type]))
  | T_operation ->
      mk_expr (Eidapp (Qident (mk_id "Operation_t"), []))
  | T_contract t ->
      let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "Contract_t"), [inner_type]))
  | T_pair (t1,t2) ->
      let car_type = typ_annotated t1 in
      let cdr_type = typ_annotated t2 in
      mk_expr (Eidapp (Qident (mk_id "Pair_t"), [car_type;cdr_type]))
  | T_or (t1,t2) ->
      let left_type = typ_annotated t1 in
      let right_type = typ_annotated t2 in
      mk_expr (Eidapp (Qident (mk_id "Or_t"), [left_type;right_type]))
  | T_lambda (t1,t2) ->
      let parameter_type = typ_annotated t1 in
      let storage_type = typ_annotated t2 in
      mk_expr (Eidapp (Qident (mk_id "Lambda_t"), [parameter_type;storage_type]))
  | T_map (ct1,t2) ->
      let key_type = comparable_type_annotated ct1 in
      let value_type = typ_annotated t2 in
      mk_expr (Eidapp (Qident (mk_id "Map_t"), [key_type;value_type]))
  | T_big_map (ct1,t2) ->
      let key_type = comparable_type_annotated ct1 in
      let value_type = typ_annotated t2 in
      mk_expr (Eidapp (Qident (mk_id "Big_map_t"), [key_type;value_type]))
  | T_chain_id ->
      mk_expr (Eidapp (Qident (mk_id "Chain_id_t"), []))

(* TODO: deal with annotations *)
and typ_annotated (t,_anot) =
  typ t

and inst = function
  | I_seq ((i1,_anot1), (i2,_anot2)) ->
      mk_expr (Elet (id_stack, false, Expr.RKnone, inst i1, inst i2))
  | I_drop ->
      mk_expr (Eidapp (Qident (mk_id "drop"), stack_fuel_args))
  | I_drop_n n -> let n = Z.to_string n in
      let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
      let n = mk_expr (Econst (Constant.ConstInt n)) in
      mk_expr (Eidapp (Qident (mk_id "drop_n"), stack_fuel_args @ [n]))
  | I_dup ->
      mk_expr (Eidapp (Qident (mk_id "dup"), stack_fuel_args)) 
  | I_swap ->
      mk_expr (Eidapp (Qident (mk_id "swap"), stack_fuel_args))
  | I_dig n -> let n = Z.to_string n in
      let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
      let n = mk_expr (Econst (Constant.ConstInt n)) in
      mk_expr (Eidapp (Qident (mk_id "dig_n"), stack_fuel_args @ [n]))
  | I_dug n -> let n = Z.to_string n in 
      let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
      let n = mk_expr (Econst (Constant.ConstInt n)) in
      mk_expr (Eidapp (Qident (mk_id "dig_n"), stack_fuel_args @ [n]))
  | I_push (_t,dt) ->
      (* let push_type = typ_annotated t in  *)
      let pushed_data = data dt in      
      mk_expr (Eidapp (Qident (mk_id "push"), stack_fuel_args @ [(*push_type;*)pushed_data]))
  | I_some ->  
      mk_expr (Eidapp (Qident (mk_id "some_op"), stack_fuel_args))
	| I_none t -> 
			let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "none_op"), stack_fuel_args @ [inner_type]))
	| I_unit ->
			mk_expr (Eidapp (Qident (mk_id "unit_op"), stack_fuel_args))
	| I_if_none (i1, i2) -> 
      let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in
			let pat_none  = mk_pat (Papp  (Qident (mk_id "None_data"), [mk_pat (Pvar (mk_id "_"))])) in
			let pat_some = mk_pat (Papp  (Qident (mk_id "Some_data"), [mk_pat (Pvar (mk_id "dt"))])) in
			let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
			let branch_true = inst_annotated i1 in
			let branch_false = inst_annotated i2 in
			let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
			let dt = mk_expr (Eident (Qident (mk_id "dt"))) in 
      let wf_dt = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [dt])) in
			let drop_head = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)			
			let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [wf_dt;e_stack])) in (* top :: s *)
			let mid_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat)) in 
      let btrue_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, branch_true)) in 
      let bfalse_let = mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_false)) in 
			let branch = [(pat_none,btrue_let);(pat_some,bfalse_let);pat_absurd] in
			mk_expr (Ematch (d_field,branch,[]))
	| I_if_some (i1,i2) ->
			inst (I_if_none (i2,i1))
	| I_pair ->
			mk_expr (Eidapp (Qident (mk_id "pair"), stack_fuel_args))
	| I_car ->
			mk_expr (Eidapp (Qident (mk_id "car"), stack_fuel_args))
	| I_cdr ->
			mk_expr (Eidapp (Qident (mk_id "cdr"), stack_fuel_args))
	| I_left t ->
			let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "left_op"), stack_fuel_args @ [inner_type]))
  | I_right t -> 
			let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "right_op"), stack_fuel_args @ [inner_type]))
  | I_if_left (i1, i2) -> 
			let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in
			let pat_left  = mk_pat (Papp  (Qident (mk_id "Left"), [mk_pat (Pvar (mk_id "dt"));mk_pat (Pvar (mk_id "_"))])) in
			let pat_right = mk_pat (Papp  (Qident (mk_id "Right"), [mk_pat (Pvar (mk_id "dt"));mk_pat (Pvar (mk_id "_"))])) in
			let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
			let branch_true = inst_annotated i1 in
			let branch_false = inst_annotated i2 in
			let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
			let dt = mk_expr (Eident (Qident (mk_id "dt"))) in 
      let wf_dt = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [dt])) in
			let drop_head = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)			
			let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [wf_dt;e_stack])) in 
			let mid_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat)) in 
      let btrue_let = mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_true)) in 
      let bfalse_let = mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_false)) in 			
			let branch = [(pat_left,btrue_let);(pat_right,bfalse_let);pat_absurd] in			
			mk_expr (Ematch (d_field,branch,[])) 			
  | I_if_right (i1, i2) -> 
			inst (I_if_left (i2,i1))
  | I_nil t -> 
			let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "nil_op"), stack_fuel_args @ [inner_type]))
  | I_cons ->
			mk_expr (Eidapp (Qident (mk_id "cons_op"), stack_fuel_args))
  | I_if_cons (i1, i2) -> 
			let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in
			let pat_nil  = mk_pat (Papp (Qident (mk_id "List"), [mk_pat (Pvar (mk_id "_Nil"));mk_pat (Pvar (mk_id "_"))])) in
			let cons_var = mk_pat (Papp (Qident (mk_id "Cons"), [mk_pat (Pvar (mk_id "hd"));mk_pat (Pvar (mk_id "tl"))])) in
			let pat_cons = mk_pat (Papp (Qident (mk_id "List"),[cons_var; mk_pat (Pvar (mk_id "t"))])) in 
			let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
			let branch_true = inst_annotated i1 in
			let branch_false = inst_annotated i2 in
			let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
			let hd = mk_expr (Eident (Qident (mk_id "hd"))) in
			let tl = mk_expr (Eident (Qident (mk_id "tl"))) in 
			let t = mk_expr (Eident (Qident (mk_id "t"))) in 
			let lst = mk_expr (Eidapp (Qident (mk_id "List"),[tl;t])) in
      let wf_hd = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [hd])) in
			let wf_lst = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [lst])) in
			let drop_head = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)			
			let first_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [wf_lst;e_stack])) in 
			let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [wf_hd;first_cat])) in 
			let mid_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat)) in 
      let btrue_let = mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_true)) in 
      let bfalse_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, branch_false)) in 						
			let branch = [(pat_cons,btrue_let);(pat_nil,bfalse_let);pat_absurd] in			
			mk_expr (Ematch (d_field,branch,[])) 			
  | I_size -> (*FIXME: Implement in WhyML *)
			mk_expr (Eidapp (Qident (mk_id "size_op"), stack_fuel_args))
  | I_empty_set ct -> (*FIXME: Implement in WhyML *)
			let inner_ctype = comparable_type_annotated ct in
      mk_expr (Eidapp (Qident (mk_id "empty_set_op"), stack_fuel_args @ [inner_ctype]))
  | I_empty_map (ct,t) -> (*FIXME: Implement in WhyML *) 
			let key_ctype = comparable_type_annotated ct in
			let value_type = typ_annotated t in
			mk_expr (Eidapp (Qident (mk_id "empty_map_op"), stack_fuel_args @ [key_ctype; value_type]))
  | I_empty_big_map (ct,t) -> (*FIXME: Implement in WhyML *) 
			let key_ctype = comparable_type_annotated ct in
			let value_type = typ_annotated t in
			mk_expr (Eidapp (Qident (mk_id "empty_big_map_op"), stack_fuel_args @ [key_ctype; value_type]))
  | I_map i -> assert false (* TODO: implement *) (*FIXME: Implement in WhyML *)
  | I_iter i -> (* FIXME: *)
      let body = inst_annotated i in      
      let fun_id = mk_id "iter_fun" in
      let kind = Expr.RKnone in
      (* start here 
      let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in
			let pat_nil  = mk_pat (Papp (Qident (mk_id "List"), [mk_pat (Pvar (mk_id "_Nil"));mk_pat (Pvar (mk_id "_"))])) in
			let cons_var = mk_pat (Papp (Qident (mk_id "Cons"), [mk_pat (Pvar (mk_id "hd"));mk_pat (Pvar (mk_id "tl"))])) in
			let pat_cons = mk_pat (Papp (Qident (mk_id "List"),[cons_var; mk_pat (Pvar (mk_id "t"))])) in 
			let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
			let branch_true = inst_annotated i1 in			
			let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
			let hd = mk_expr (Eident (Qident (mk_id "hd"))) in
			let tl = mk_expr (Eident (Qident (mk_id "tl"))) in 
			let t = mk_expr (Eident (Qident (mk_id "t"))) in 
			let lst = mk_expr (Eidapp (Qident (mk_id "List"),[tl;t])) in
      let wf_hd = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [hd])) in
			let wf_lst = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [lst])) in
			let drop_head = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)			
			let first_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [wf_lst;e_stack])) in 
			let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [wf_hd;first_cat])) in 
			let mid_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat)) in 
      let btrue_let = mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_true)) in       
			let branch = [(pat_cons,btrue_let);(pat_nil,drop_head);pat_absurd] in			
			let mtch = mk_expr (Ematch (d_field,branch,[])) in
       end here *)
      let i_let =  mk_expr (Elet (id_stack, false, kind, body, e_stack)) in    
      let pat = mk_pat (Pvar id_stack_t) in 
      let mask = Ity.MaskVisible in
      let pty = Some stack_ty in
      let binders = [stack_binder;fuel_binder] in
      let fun_def = [fun_id,false,kind,binders,pty,pat,mask,empty_spec,i_let] in 
      let deleteME = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      mk_expr (Erec (fun_def,deleteME))
      (* let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in
			let pat_nil  = mk_pat (Papp (Qident (mk_id "List"), [mk_pat (Pvar (mk_id "_Nil"));mk_pat (Pvar (mk_id "_"))])) in
			let cons_var = mk_pat (Papp (Qident (mk_id "Cons"), [mk_pat (Pvar (mk_id "hd"));mk_pat (Pvar (mk_id "tl"))])) in
			let pat_cons = mk_pat (Papp (Qident (mk_id "List"),[cons_var; mk_pat (Pvar (mk_id "t"))])) in 
			let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
      let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
      let drop_head = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)
      let bfalse_let = mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, e_stack)) in 
      let branch = [(pat_cons,btrue_let);(pat_nil,bfalse_let);pat_absurd] in			
			mk_expr (Ematch (d_field,branch,[])) 			 *)
  | I_mem -> (*FIXME: Implement in WhyML *)
			mk_expr (Eidapp (Qident (mk_id "mem_op"), stack_fuel_args))
  | I_get -> (*FIXME: Implement in WhyML *)
			mk_expr (Eidapp (Qident (mk_id "get_op"), stack_fuel_args))
  | I_update -> (*FIXME: Implement in WhyML *)
			mk_expr (Eidapp (Qident (mk_id "update_op"), stack_fuel_args))
  | I_if (i1, i2) -> (* TODO: ask about non exhaustive pm *)		
			let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in	      
      let pat_bool = mk_pat (Papp  (Qident (mk_id "Bool"), [mk_pat (Pvar (mk_id "b"))])) in
      let comp_b = mk_pat (Papp (Qident (mk_id "Comparable"),[pat_bool])) in			
			let branch_true = inst_annotated i1 in
			let branch_false = inst_annotated i2 in
			let bool_eval = mk_expr (Eident (Qident (mk_id "b"))) in 
			let if_eval = mk_expr (Eif (bool_eval, branch_true, branch_false)) in
			let branch = [(comp_b,if_eval)] in
			mk_expr (Ematch (d_field,branch,[]))			
  | I_loop i -> 
      let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
      let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in	      
      let pat_bool = mk_pat (Papp  (Qident (mk_id "Bool"), [mk_pat (Pvar (mk_id "b"))])) in
      let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
      let comp_b = mk_pat (Papp (Qident (mk_id "Comparable"),[pat_bool])) in
      let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
      let drop_head = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in
			let body = inst_annotated i in			
			let bool_eval = mk_expr (Eident (Qident (mk_id "b"))) in 
      let kind = Expr.RKnone in               
      let fun_id = mk_id "loop_fun" in
      let branch_true = mk_expr (Elet (id_stack, false, kind, body, e_stack)) in 
      let rec_call = mk_expr (Eidapp (Qident (fun_id), [branch_true;e_fuel])) in  
      let if_eval = mk_expr (Eif (bool_eval, rec_call, e_stack)) in
      let drop_let = mk_expr (Elet(id_stack,false,kind,drop_head,if_eval)) in
			let branch = [(comp_b,drop_let);pat_absurd] in
			let mtch = mk_expr (Ematch (d_field,branch,[]))	in
      let pat = mk_pat (Pvar id_stack_t) in 
      let mask = Ity.MaskVisible in
      let pty = Some stack_ty in
      let binders = [stack_binder;fuel_binder] in
      let fun_def = [fun_id,false,kind,binders,pty,pat,mask,empty_spec,mtch] in       
      mk_expr (Erec (fun_def,e_stack))           
  | I_loop_left i -> assert false (* TODO: implement *) (*FIXME: Implement in WhyML *)
  | I_lambda (t1,t2,i) -> assert false (* TODO: implement *) (*FIXME: Implement in WhyML *)  
  | I_dip i ->
			let top_id = mk_id "top" in 
			let top_value = mk_expr (Eident (Qident top_id)) in 
			let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in (* top = s[0] *)
			let n_lit = int_literal ILitDec ~neg:false "1" in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
			let headless = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)			
			let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [top_value;e_stack])) in (* top :: s *)
			let last_let = mk_expr (Elet (id_stack, false, Expr.RKnone, inst_annotated i, final_cat)) in 
			let middle_let =  mk_expr (Elet (id_stack, false, Expr.RKnone, headless, last_let)) in
			mk_expr (Elet (top_id, false, Expr.RKnone, top, middle_let))
  | I_dip_n (n,i) -> 
      let top_id = mk_id "top" in 
			let top_value = mk_expr (Eident (Qident top_id)) in 
			let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in (* top = s[0] *)
			let n = Z.to_string n in			
			let n_lit = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
      let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
			let headless = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)			
			let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [top_value;e_stack])) in (* top :: s *)
			let last_let = mk_expr (Elet (id_stack, false, Expr.RKnone, inst_annotated i, final_cat)) in 
			let middle_let =  mk_expr (Elet (id_stack, false, Expr.RKnone, headless, last_let)) in
			mk_expr (Elet (top_id, false, Expr.RKnone, top, middle_let))
  | I_failwith -> 
      mk_expr (Eraise ((Qident (mk_id "Failing")),None))			
  | I_cast t -> (*TODO: Implement in WhyML *)
      let value_type = typ_annotated t in
			mk_expr (Eidapp (Qident (mk_id "cast_op"), stack_fuel_args @ [value_type]))
  | I_concat -> (*TODO: Implement in WhyML *)
			mk_expr (Eidapp (Qident (mk_id "concat_op"), stack_fuel_args))
  | I_slice -> (*TODO: Implement in WhyML *)
			mk_expr (Eidapp (Qident (mk_id "slice_op"), stack_fuel_args))
  | I_pack -> 
			mk_expr (Eidapp (Qident (mk_id "pack"), stack_fuel_args))
  | I_unpack t -> 
			let inner_type = typ_annotated t in
			mk_expr (Eidapp (Qident (mk_id "unpack_op"), stack_fuel_args @ [inner_type]))
  | I_add ->
			mk_expr (Eidapp (Qident (mk_id "add"), stack_fuel_args))
  | I_sub ->
			mk_expr (Eidapp (Qident (mk_id "sub"), stack_fuel_args))
  | I_mul ->
			mk_expr (Eidapp (Qident (mk_id "mul"), stack_fuel_args))
  | I_ediv ->
			mk_expr (Eidapp (Qident (mk_id "ediv"), stack_fuel_args))
  | I_abs ->
			mk_expr (Eidapp (Qident (mk_id "abs_op"), stack_fuel_args))
  | I_isnat -> 
			mk_expr (Eidapp (Qident (mk_id "isnat"), stack_fuel_args))
  | I_int -> 
			mk_expr (Eidapp (Qident (mk_id "int_op"), stack_fuel_args))
  | I_neg -> 
			mk_expr (Eidapp (Qident (mk_id "neg"), stack_fuel_args))
  | I_lsl ->
			mk_expr (Eidapp (Qident (mk_id "lsl_op"), stack_fuel_args))
  | I_lsr ->
			mk_expr (Eidapp (Qident (mk_id "lsr_op"), stack_fuel_args))
  | I_or ->
			mk_expr (Eidapp (Qident (mk_id "or"), stack_fuel_args))
  | I_and ->
			mk_expr (Eidapp (Qident (mk_id "and"), stack_fuel_args))
  | I_xor ->
			mk_expr (Eidapp (Qident (mk_id "xor"), stack_fuel_args))
  | I_not ->
			mk_expr (Eidapp (Qident (mk_id "not_op"), stack_fuel_args))
  | I_compare ->
			mk_expr (Eidapp (Qident (mk_id "compare_op"), stack_fuel_args))
  | I_eq ->
			mk_expr (Eidapp (Qident (mk_id "eq"), stack_fuel_args))
  | I_neq -> 
			mk_expr (Eidapp (Qident (mk_id "neq"), stack_fuel_args))
  | I_lt -> 
			mk_expr (Eidapp (Qident (mk_id "lt"), stack_fuel_args))
  | I_gt -> 
			mk_expr (Eidapp (Qident (mk_id "gt"), stack_fuel_args))
  | I_le -> 
			mk_expr (Eidapp (Qident (mk_id "le"), stack_fuel_args))
  | I_ge -> 
			mk_expr (Eidapp (Qident (mk_id "ge"), stack_fuel_args))
  | I_self -> 
			mk_expr (Eidapp (Qident (mk_id "self_op"), stack_fuel_args))
  | I_contract t -> 
			let inner_type = typ_annotated t in
      mk_expr (Eidapp (Qident (mk_id "contract_op"), stack_fuel_args @ [inner_type]))
  | I_transfer_tokens -> 
			mk_expr (Eidapp (Qident (mk_id "transfer_tokens"), stack_fuel_args))
  | I_set_delegate -> 
			mk_expr (Eidapp (Qident (mk_id "set_delegate_op"), stack_fuel_args))
  | I_create_contract p -> assert false (* TODO: implement *) (*FIXME: Implement in WhyML *)
  | I_implicit_account -> 
			mk_expr (Eidapp (Qident (mk_id "implicit_account_op"), stack_fuel_args))
  | I_now -> 
			mk_expr (Eidapp (Qident (mk_id "now_op"), stack_fuel_args))
  | I_amount ->
			mk_expr (Eidapp (Qident (mk_id "amount_op"), stack_fuel_args))
  | I_balance -> 
			mk_expr (Eidapp (Qident (mk_id "balance_op"), stack_fuel_args))
  | I_check_signature -> 
			mk_expr (Eidapp (Qident (mk_id "check_signature_op"), stack_fuel_args))
  | I_blake2b -> 
			mk_expr (Eidapp (Qident (mk_id "blake2b_op"), stack_fuel_args))
  | I_sha256 -> 
			mk_expr (Eidapp (Qident (mk_id "sha256_op"), stack_fuel_args))
  | I_sha512 -> 
			mk_expr (Eidapp (Qident (mk_id "sha512_op"), stack_fuel_args))
  | I_hash_key -> 
			mk_expr (Eidapp (Qident (mk_id "hash_key_op"), stack_fuel_args))
  | I_source -> 
			mk_expr (Eidapp (Qident (mk_id "source_op"), stack_fuel_args))
  | I_sender -> 
			mk_expr (Eidapp (Qident (mk_id "sender_op"), stack_fuel_args))
  | I_address -> 
			mk_expr (Eidapp (Qident (mk_id "address_op"), stack_fuel_args))
  | I_chain_id -> 
			mk_expr (Eidapp (Qident (mk_id "chain_id_op"), stack_fuel_args))
  | I_noop ->
			mk_expr (Eidapp (Qident (mk_id "noop"), stack_fuel_args))
  | I_unpair ->
			mk_expr (Eidapp (Qident (mk_id "unpair"), stack_fuel_args))
  (* renaming operation on annotations *)    
  | I_rename -> (*TODO: Implement in WhyML *)  
			mk_expr (Eidapp (Qident (mk_id "rename_op"), stack_fuel_args))
  | I_exec -> assert false (*TODO: Implement in WhyML *)
			(* mk_expr (Eidapp (Qident (mk_id "exec_op"), stack_fuel_args)) *)
  | I_create_account (* considered deprecated *)
  | I_steps_to_quota -> assert false (* considered deprecated *)

(* TODO: deal with annotations *)
and inst_annotated (i,_anot) =
	inst i

and data  d = 
	let rec aux = function	
  | D_int n ->
      let n = Z.to_string n in
      let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
      let i = mk_expr (Econst (Constant.ConstInt n)) in
      let int_i = mk_expr (Eidapp (Qident (mk_id "Int"), [i])) in
      mk_expr (Eidapp (Qident (mk_id "Comparable"), [int_i]))
  | D_nat n -> 
      let n = Z.to_string n in
      let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
      let i = mk_expr (Econst (Constant.ConstInt n)) in
      let i_record =  mk_expr (Eidapp (Qident (mk_id "to_nat"), [i])) in
      let nat_i = mk_expr (Eidapp (Qident (mk_id "Nat"), [i_record])) in
			mk_expr (Eidapp (Qident (mk_id "Comparable"), [nat_i]))      
	| D_string s ->
			let str_const = mk_expr (Econst (Constant.ConstStr s)) in
			let str_s = mk_expr (Eidapp (Qident (mk_id "String"),[str_const])) in
			mk_expr (Eidapp (Qident (mk_id "Comparable"), [str_s]))
	| D_timestamp s ->
			let str = mk_expr (Econst (Constant.ConstStr s)) in
			let ts = mk_expr (Eidapp (Qident (mk_id "Timestamp"), [str])) in
			mk_expr (Eidapp (Qident (mk_id "Comparable"), [ts])) 			
	| D_bool b -> 
			let v_true = mk_expr Etrue in 
			let v_false = mk_expr Efalse in
			let arg = if b then v_true else v_false in 
			let b = mk_expr (Eidapp (Qident (mk_id "Bool"), [arg])) in 
			mk_expr (Eidapp (Qident (mk_id "Comparable"), [b]))			
	| D_pair (d1,d2) -> 
			let dt1 = aux d1 in
			let dt2 = aux d2 in
			mk_expr (Eidapp (Qident (mk_id "Pair"), [dt1;dt2]))
	| D_left d -> 
			let dt = aux d in 
			mk_expr (Eidapp (Qident (mk_id "Left"), [dt]))
	| D_right d ->
			let dt = aux d in 
			mk_expr (Eidapp (Qident (mk_id "Right"), [dt]))
	| D_some d -> 
			let dt = aux d in 
			mk_expr (Eidapp (Qident (mk_id "Some_data"), [dt]))
	| D_none t -> 
			let inner_type = typ_annotated t in 
			mk_expr (Eidapp (Qident (mk_id "None_data"), [inner_type]))		
	| D_unit ->
			mk_expr (Eidapp (Qident (mk_id "Unit"), []))			
  | _ -> assert false (* TODO: implement *)
	in let dt = aux d in
	mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [dt]))

(*and node : type a. a node -> expr = fun n ->
  match n.data with
  | Inst i -> inst i
  | Data d -> data d
  | Type x -> assert false (* TODO *)
  | Comparable_type _ -> assert false TODO *)

 (* I_push ({data = Type t}, d) -> begin match t with
      | T_comparable {data = Comparable_type t} -> begin match t with
          | T_int -> let data = node d in
              let id_int = mk_id "Int" in
              let int_app = mk_expr (Eidapp (Qident id_int, [data])) in
              let id_cmp = mk_id "Comparable" in
              let cmp_app = mk_expr (Eidapp (Qident id_cmp, [int_app])) in
              let args = stack_fuel_args @ [cmp_app] in
              mk_expr (Eidapp (Qident (mk_id "push"), args))
          | T_nat -> let data = node d in
              let id_nat = mk_id "Nat" in
              let nat_app = mk_expr (Eidapp (Qident id_nat, [data])) in
              let id_cmp = mk_id "Comparable" in
              let cmp_app = mk_expr (Eidapp (Qident id_cmp, [nat_app])) in
              let args = stack_fuel_args @ [cmp_app] in
              mk_expr (Eidapp (Qident (mk_id "push"), args))
          | _ -> assert false (* TODO *) end
      | _ -> assert false (* TODO *) end  *)


(* *************************************************************** *)
(* ************************     Terms      *********************** *)
(* *************************************************************** *)

let simple_comparable_term = function
  | T_int ->
      mk_term (Tidapp (Qident (mk_id "Int_t"), []))
  | T_nat ->
      mk_term (Tidapp (Qident (mk_id "Nat_t"), []))
  | T_string ->
      mk_term (Tidapp (Qident (mk_id "String_t"), []))
  | T_bytes ->
      mk_term (Tidapp (Qident (mk_id "Bytes_t"), []))
  | T_mutez ->
      mk_term (Tidapp (Qident (mk_id "Mutez_t"), []))
  | T_bool ->
      mk_term (Tidapp (Qident (mk_id "Bool_t"), []))
  | T_key_hash ->
      mk_term (Tidapp (Qident (mk_id "Key_hash_t"), []))
  | T_timestamp ->
      mk_term (Tidapp (Qident (mk_id "Timestamp_t"), []))
  | T_address->
      mk_term (Tidapp (Qident (mk_id "Address_t"), []))

(* TODO: deal with annotations *)
let simple_comparable_term_annotated (t,_anot) = 
 simple_comparable_term t

let rec comparable_term = function
  | T_simple_comparable_type t -> 
      simple_comparable_term t
  | T_comparable_pair (sAnot, cAnot) -> 
      let car_expr_t = simple_comparable_term_annotated sAnot in
      let cdr_expr_t = comparable_term_annotated cAnot in
      mk_term (Tidapp (Qident (mk_id "Pair_t"), [car_expr_t;cdr_expr_t]))

(* TODO: deal with annotations *)
and comparable_term_annotated (t,_anot) = 
  comparable_term t

and typ_term = function
  | T_comparable t ->
      let t = comparable_term t in 
			mk_term (Tidapp (Qident (mk_id "Comparable_t"), [t]))
  | T_key ->
      mk_term (Tidapp (Qident (mk_id "Key_t"), []))
  | T_unit ->
      mk_term (Tidapp (Qident (mk_id "Unit_t"), []))
  | T_signature ->
      mk_term (Tidapp (Qident (mk_id "Signature_t"), []))
  | T_option t ->
      let inner_type = term_annotated t in
      mk_term (Tidapp (Qident (mk_id "Option_t"), [inner_type]))
  | T_list t ->
      let inner_type = term_annotated t in
      mk_term (Tidapp (Qident (mk_id "List_t"), [inner_type]))
  | T_set ct ->
      let inner_type = comparable_term_annotated ct in
      mk_term (Tidapp (Qident (mk_id "Option_t"), [inner_type]))
  | T_operation ->
      mk_term (Tidapp (Qident (mk_id "Operation_t"), []))
  | T_contract t ->
      let inner_type = term_annotated t in
      mk_term (Tidapp (Qident (mk_id "Contract_t"), [inner_type]))
  | T_pair (t1,t2) ->
      let car_type = term_annotated t1 in
      let cdr_type = term_annotated t2 in
      mk_term (Tidapp (Qident (mk_id "Pair_t"), [car_type;cdr_type]))
  | T_or (t1,t2) ->
      let left_type = term_annotated t1 in
      let right_type = term_annotated t2 in
      mk_term (Tidapp (Qident (mk_id "Or_t"), [left_type;right_type]))
  | T_lambda (t1,t2) ->
      let parameter_type = term_annotated t1 in
      let storage_type = term_annotated t2 in
      mk_term (Tidapp (Qident (mk_id "Lambda_t"), [parameter_type;storage_type]))
  | T_map (ct1,t2) ->
      let key_type = comparable_term_annotated ct1 in
      let value_type = term_annotated t2 in
      mk_term (Tidapp (Qident (mk_id "Map_t"), [key_type;value_type]))
  | T_big_map (ct1,t2) ->
      let key_type = comparable_term_annotated ct1 in
      let value_type = term_annotated t2 in
      mk_term (Tidapp (Qident (mk_id "Big_map_t"), [key_type;value_type]))
  | T_chain_id ->
      mk_term (Tidapp (Qident (mk_id "Chain_id_t"), []))

(* TODO: deal with annotations *)
and term_annotated (t,_anot) =
  typ_term t




let program {param;storage;code} =
  let code = inst code in
  let param = term_annotated param in
  let storage = term_annotated storage in
  let default_spec = {
  sp_pre     = [pre_len;pre_fuel;mk_pre_typ param storage];
  sp_post    = [Loc.dummy_position,[mk_pat (Pvar (mk_id "result")),post_len];mk_post_typ storage];
  sp_xpost   = [];
  sp_reads   = [];
  sp_writes  = [];
  sp_alias   = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false;
  } in
  let kind = Expr.RKnone in
  let i_let = mk_expr (Elet (id_stack, false, kind, code, e_stack)) in
  let pat = mk_pat (Pvar id_stack_t) in
  let mask = Ity.MaskVisible in
  let pty = Some stack_ty in
  let binders = [stack_binder; fuel_binder] in
  let f_exp = Efun (binders, pty, pat, mask, default_spec, i_let) in
  let f_exp = mk_expr f_exp in
  let decl = Dlet (mk_id "test", false, kind, f_exp) in
  [use_axiomatic; use_data_types; use_seq; use_int; use_nat; decl]

