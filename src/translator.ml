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

open Why3
open Michelson
open Adt
open Ptree
open Number

let mk_id id_str = { id_str; id_ats = []; id_loc = Loc.dummy_position }
let mk_expr ?(expr_loc = Loc.dummy_position) expr_desc = { expr_desc; expr_loc }
let mk_pat pat_desc = { pat_desc; pat_loc = Loc.dummy_position }
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
let stack_binder = (Loc.dummy_position, Some id_stack, false, Some stack_ty)
let fuel_binder = (Loc.dummy_position, Some id_fuel, false, Some int_ty)

let empty_spec =
  {
    sp_pre = [];
    sp_post = [];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false;
  }

(* added term_loc  as optional parameter *)
let mk_term ?(term_loc = Loc.dummy_position) term_desc = { term_desc; term_loc }
let mk_const i = Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = i })
let mk_tconst i = mk_term (Tconst (mk_const (BigInt.of_int i)))
let mk_tapp f l = mk_term (Tidapp (f, l))
let eq_symb = Qident (mk_id "infix =")
let gt_symb = Qident (mk_id "infix >")
let comma_symb = Qident (mk_id "infix ,")
let t_stack = mk_term (Tident q_stack)
let t_fuel = mk_term (Tident q_fuel)
let t_result = mk_term (Tident (Qident (mk_id "result")))
let len_stack = mk_tapp (Qident (mk_id "length")) [ t_stack ]
let len_result = mk_tapp (Qident (mk_id "length")) [ t_result ]

let top_input_stack =
  mk_tapp (Qident (mk_id "mixfix []")) [ t_stack; mk_tconst 0 ]
(* let top_input_stack = mk_tapp (Qident (mk_id "peek")) [t_stack]  *)

let pre_len = mk_tapp eq_symb [ len_stack; mk_tconst 1 ]
let pre_fuel = mk_tapp gt_symb [ t_fuel; mk_tconst 0 ]
let post_len = mk_tapp eq_symb [ len_result; mk_tconst 1 ]

let mk_pre_typ t1 t2 =
  let top_input_stack =
    mk_tapp (Qident (mk_id "mixfix []")) [ t_stack; mk_tconst 0 ]
  in
  let typ_stack = mk_tapp (Qident (mk_id "type_of")) [ top_input_stack ] in
  let p = mk_term (Tidapp (Qident (mk_id "T_pair"), [ t1; t2 ])) in
  mk_tapp eq_symb [ typ_stack; p ]

let mk_post_typ t =
  let top_result_stack =
    mk_tapp (Qident (mk_id "mixfix []")) [ t_result; mk_tconst 0 ]
  in
  let typ_stack = mk_tapp (Qident (mk_id "type_of")) [ top_result_stack ] in
  let opt_t = mk_term (Tidapp (Qident (mk_id "T_operation"), [])) in
  let lst_t = mk_term (Tidapp (Qident (mk_id "T_list"), [ opt_t ])) in
  let p = mk_term (Tidapp (Qident (mk_id "T_pair"), [ lst_t; t ])) in
  ( Loc.dummy_position,
    [ (mk_pat (Pvar (mk_id "result")), mk_tapp eq_symb [ typ_stack; p ]) ] )

let stack_fuel_args = [ e_stack; e_fuel ]

let use_axiomatic =
  let axiomatic_sem = mk_id "AxiomaticSem" in
  let q_axiomatic = Qdot (Qident (mk_id "axiomatic"), axiomatic_sem) in
  ( Loc.dummy_position,
    Duseimport (Loc.dummy_position, false, [ (q_axiomatic, None) ]) )

let use_data_types =
  let data_types = mk_id "DataTypes" in
  let q_data_types = Qdot (Qident (mk_id "dataTypes"), data_types) in
  ( Loc.dummy_position,
    Duseimport (Loc.dummy_position, false, [ (q_data_types, None) ]) )

let use_seq =
  let seq_id = mk_id "Seq" in
  let q_seq = Qdot (Qident (mk_id "seq"), seq_id) in
  (Loc.dummy_position, Duseimport (Loc.dummy_position, false, [ (q_seq, None) ]))

let use_int =
  let int_id = mk_id "Int" in
  let q_int = Qdot (Qident (mk_id "int"), int_id) in
  (Loc.dummy_position, Duseimport (Loc.dummy_position, false, [ (q_int, None) ]))

(* let use_nat = let nat_id = mk_id "Natural" in
   let q_nat = Qdot (Qident (mk_id "natural"), nat_id) in
   Duseimport (Loc.dummy_position, false, [q_nat, None]) *)

let mk_position =
  let open Michelson.Location in
  function
  | Loc tz_pos ->
      Loc.user_position tz_pos.start_pos.pos_fname tz_pos.start_pos.pos_lnum
        (tz_pos.start_pos.pos_cnum - 1)
        (tz_pos.end_pos.pos_cnum - 1)
  | Unknown -> Loc.dummy_position

(* *************************************************************** *)
(* ************************  List Operations  ******************** *)
(* *************************************************************** *)

let list_iter body list =
  let pat_var = mk_expr (Eident (Qident list)) in
  let lhs_pat_nil =
    mk_pat
      (Papp
         ( Qident (mk_id "D_list"),
           [ mk_pat (Pvar (mk_id "_Nil")); mk_pat Pwild ] ))
  in
  (* List Nil _ *)
  let cons_var =
    mk_pat
      (Papp
         ( Qident (mk_id "Cons"),
           [ mk_pat (Pvar (mk_id "hd")); mk_pat (Pvar (mk_id "tl")) ] ))
  in
  (* Cons hd tl *)
  let lhs_pat_cons =
    mk_pat
      (Papp (Qident (mk_id "D_list"), [ cons_var; mk_pat (Pvar (mk_id "t")) ]))
  in
  (* List (Cons hd tl) t *)
  let pat_absurd = (mk_pat Pwild, mk_expr Eabsurd) in
  let rhs_pat_nil = e_stack in
  let hd = mk_expr (Eident (Qident (mk_id "hd"))) in
  let tl = mk_expr (Eident (Qident (mk_id "tl"))) in
  let t = mk_expr (Eident (Qident (mk_id "t"))) in
  let fun_id = mk_id "list_iter_fun" in
  let rec_call = mk_expr (Eidapp (Qident fun_id, [ e_stack; t ])) in
  let _lst = mk_expr (Eidapp (Qident (mk_id "D_list"), [ tl; t ])) in
  (* let wf_hd = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [hd])) in *)
  (* let wf_lst = mk_expr (Eidapp (Qident (mk_id "mk_wf_data"), [lst])) in *)
  let stack_cat =
    mk_expr (Eidapp (Qident (mk_id "infix ::"), [ hd; e_stack ]))
  in
  let new_stack = mk_expr (Eidapp (eq_symb, [ e_stack; body ])) in
  let s_equal_body_let =
    mk_expr (Elet (id_stack, false, Expr.RKnone, new_stack, rec_call))
  in
  (* let s' = body in *)
  let rhs_pat_cons =
    mk_expr (Elet (id_stack, false, Expr.RKnone, stack_cat, s_equal_body_let))
  in
  (* let stack = h::stack in *)
  let branch =
    [ (lhs_pat_nil, rhs_pat_nil); (lhs_pat_cons, rhs_pat_cons); pat_absurd ]
  in
  let mtch = mk_expr (Ematch (pat_var, branch, [])) in
  let kind = Expr.RKnone in
  let pat = mk_pat (Pvar list) in
  let mask = Ity.MaskVisible in
  let pty = Some stack_ty in
  let list_binder = (Loc.dummy_position, Some list, false, None) in
  let binders = [ stack_binder; list_binder ] in
  let fun_def =
    [ (fun_id, false, kind, binders, pty, pat, mask, empty_spec, mtch) ]
  in
  let main_call = mk_expr (Eidapp (Qident fun_id, [ e_stack; pat_var ])) in
  mk_expr (Erec (fun_def, main_call))

(* *************************************************************** *)
(* ************************     Terms      *********************** *)
(* *************************************************************** *)

let rec term_comparable_type =
  let term_loc = Loc.dummy_position in
  function
  | Type_simple_comparable_type Type_int ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_int"), []))
  | Type_simple_comparable_type Type_nat ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_nat"), []))
  | Type_simple_comparable_type Type_string ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_string"), []))
  | Type_simple_comparable_type Type_bytes ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_bytes"), []))
  | Type_simple_comparable_type Type_mutez ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_mutez"), []))
  | Type_simple_comparable_type Type_bool ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_bool"), []))
  | Type_simple_comparable_type Type_key_hash ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_key_hash"), []))
  | Type_simple_comparable_type Type_timestamp ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_timestamp"), []))
  | Type_simple_comparable_type Type_address ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_address"), []))
  | Type_simple_comparable_type Type_key ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_key"), []))
  | Type_simple_comparable_type Type_unit ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_unit"), []))
  | Type_comparable_pair (t1, t2) ->
      let car_type = term_comparable_type (Type_simple_comparable_type t1) in
      let cdr_type = term_comparable_type t2 in
      mk_term ~term_loc
        (Tidapp (Qident (mk_id "T_pair"), [ car_type; cdr_type ]))

let rec term =
  let term_loc = Loc.dummy_position in
  function
  | Type_comparable t' -> term_comparable_type t'
  | Type_signature ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_signature"), []))
  | Type_option t ->
      let inner_type = term t in
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_option"), [ inner_type ]))
  | Type_list t ->
      let inner_type = term t in
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_list"), [ inner_type ]))
  | Type_set ct ->
      let inner_type = term_comparable_type ct in
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_set"), [ inner_type ]))
  | Type_operation ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_operation"), []))
  | Type_contract t ->
      let inner_type = term t in
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_contract"), [ inner_type ]))
  | Type_pair (t1, t2) ->
      let car_type = term t1 in
      let cdr_type = term t2 in
      mk_term ~term_loc
        (Tidapp (Qident (mk_id "T_pair"), [ car_type; cdr_type ]))
  | Type_or (t1, t2) ->
      let left_type = term t1 in
      let right_type = term t2 in
      mk_term ~term_loc
        (Tidapp (Qident (mk_id "T_or"), [ left_type; right_type ]))
  | Type_lambda (t1, t2) ->
      let parameter_type = term t1 in
      let storage_type = term t2 in
      mk_term ~term_loc
        (Tidapp (Qident (mk_id "T_lambda"), [ parameter_type; storage_type ]))
  | Type_map (ct1, t2) ->
      let key_type = term_comparable_type ct1 in
      let value_type = term t2 in
      mk_term ~term_loc
        (Tidapp (Qident (mk_id "T_map"), [ key_type; value_type ]))
  | Type_big_map (ct1, t2) ->
      let key_type = term_comparable_type ct1 in
      let value_type = term t2 in
      mk_term ~term_loc
        (Tidapp (Qident (mk_id "T_big_map"), [ key_type; value_type ]))
  | Type_chain_id ->
      mk_term ~term_loc (Tidapp (Qident (mk_id "T_chain_id"), []))

(* TODO: deal with annotations *)

(* make intermediate types *)
let mk_intermediate_typ t i =
  let result_stack_at_i =
    mk_tapp (Qident (mk_id "mixfix []")) [ t_result; mk_tconst i ]
  in
  let typ_stack = mk_tapp (Qident (mk_id "type_of")) [ result_stack_at_i ] in
  let tp = term t in
  mk_tapp eq_symb [ typ_stack; tp ]

(* *************************************************************** *)
(* ************************     Exprs      *********************** *)
(* *************************************************************** *)

let rec typ_comparable_type t expr_loc =
  match t with
  | T_simple_comparable_type { value = T_int; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_int"), []))
  | T_simple_comparable_type { value = T_nat; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_nat"), []))
  | T_simple_comparable_type { value = T_string; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_string"), []))
  | T_simple_comparable_type { value = T_bytes; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_bytes"), []))
  | T_simple_comparable_type { value = T_mutez; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_mutez"), []))
  | T_simple_comparable_type { value = T_bool; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_bool"), []))
  | T_simple_comparable_type { value = T_key_hash; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_key_hash"), []))
  | T_simple_comparable_type { value = T_timestamp; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_timestamp"), []))
  | T_simple_comparable_type { value = T_address; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_address"), []))
  | T_simple_comparable_type { value = T_key; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_key"), []))
  | T_simple_comparable_type { value = T_unit; _ } ->
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_unit"), []))
  | T_comparable_pair (t1, t2) ->
      let car_type =
        typ_comparable_type (T_simple_comparable_type t1)
          (mk_position t1.Location.loc)
      in
      let cdr_type =
        typ_comparable_type t2.value (mk_position t2.Location.loc)
      in
      mk_expr ~expr_loc
        (Eidapp (Qident (mk_id "T_pair"), [ car_type; cdr_type ]))

let rec typ t =
  let expr_loc = mk_position t.Location.loc in
  match t.value with
  | T_comparable t' -> typ_comparable_type t' expr_loc
  | T_signature -> mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_signature"), []))
  | T_option t ->
      let inner_type = typ t in
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_option"), [ inner_type ]))
  | T_list t ->
      let inner_type = typ t in
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_list"), [ inner_type ]))
  | T_set ct ->
      let inner_type =
        typ_comparable_type ct.value (mk_position ct.Location.loc)
      in
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_set"), [ inner_type ]))
  | T_operation -> mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_operation"), []))
  | T_contract t ->
      let inner_type = typ t in
      mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_contract"), [ inner_type ]))
  | T_or (t1, t2) ->
      let left_type = typ t1 in
      let right_type = typ t2 in
      mk_expr ~expr_loc
        (Eidapp (Qident (mk_id "T_or"), [ left_type; right_type ]))
  | T_lambda (t1, t2) ->
      let parameter_type = typ t1 in
      let storage_type = typ t2 in
      mk_expr ~expr_loc
        (Eidapp (Qident (mk_id "T_lambda"), [ parameter_type; storage_type ]))
  | T_map (ct1, t2) ->
      let key_type =
        typ_comparable_type ct1.value (mk_position ct1.Location.loc)
      in
      let value_type = typ t2 in
      mk_expr ~expr_loc
        (Eidapp (Qident (mk_id "T_map"), [ key_type; value_type ]))
  | T_big_map (ct1, t2) ->
      let key_type =
        typ_comparable_type ct1.value (mk_position ct1.Location.loc)
      in
      let value_type = typ t2 in
      mk_expr ~expr_loc
        (Eidapp (Qident (mk_id "T_big_map"), [ key_type; value_type ]))
  | T_chain_id -> mk_expr ~expr_loc (Eidapp (Qident (mk_id "T_chain_id"), []))
  | T_pair (t1, t2) ->
      let car_type = typ t1 in
      let cdr_type = typ t2 in
      mk_expr ~expr_loc
        (Eidapp (Qident (mk_id "T_pair"), [ car_type; cdr_type ]))

and to_expr_typed =
  let c = ref 0 in
  fun (exp : expr) ({ stack_after; _ } : Adt_typ.inst) ->
    (* myabe also add stack before for preconditions *)
    let len_of_stack =
      mk_tapp eq_symb [ len_result; mk_tconst stack_after.stack_size ]
    in
    let post =
      List.fold_left
        (fun (acc, i) t ->
          (mk_term (Tbinop (acc, Dterm.DTand, mk_intermediate_typ t i)), i + 1))
        (len_of_stack, 0) stack_after.stack_type
    in
    let spec =
      {
        sp_pre = [];
        sp_post =
          [
            (Loc.dummy_position, [ (mk_pat (Pvar (mk_id "result")), fst post) ]);
          ];
        sp_xpost = [];
        sp_reads = [];
        sp_writes = [];
        sp_alias = [];
        sp_variant = [];
        sp_checkrw = false;
        sp_diverge = false;
        sp_partial = false;
      }
    in
    let e_fun = Efun ([], None, mk_pat Pwild, Ity.MaskVisible, spec, exp) in
    let efun_expr = mk_expr e_fun in
    let temp_count =
      incr c;
      "expl:Intermidate PostCondition " ^ string_of_int !c
    in
    let attr = ATstr (Ident.create_attribute temp_count) in
    let atr_fun = mk_expr (Eattr (ATstr Vc.wb_attr, efun_expr)) in
    mk_expr (Eattr (attr, atr_fun))

and inst Adt_typ.({ desc; stack_before; stack_after } as r) =
  let loc, desc = (desc.loc, desc.value) in
  let new_loc = mk_position loc in
  let x =
    match desc with
    | I_seq (i1, i2) ->
        mk_expr ~expr_loc:new_loc
          (Elet (id_stack, false, Expr.RKnone, inst i1, inst i2))
    | I_drop ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "drop"), stack_fuel_args))
    | I_drop_n n ->
        let n = Z.to_string n in
        let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
        let n = mk_expr (Econst (Constant.ConstInt n)) in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "drop_n"), stack_fuel_args @ [ n ]))
    | I_dup ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "dup"), stack_fuel_args))
    | I_swap ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "swap"), stack_fuel_args))
    | I_dig n ->
        let n = Z.to_string n in
        let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
        let n = mk_expr (Econst (Constant.ConstInt n)) in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "dig_n"), stack_fuel_args @ [ n ]))
    | I_dug n ->
        let n = Z.to_string n in
        let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
        let n = mk_expr (Econst (Constant.ConstInt n)) in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "dug_n"), stack_fuel_args @ [ n ]))
    | I_push (t, dt) ->
        let push_type = typ t in
        let pushed_data = data t dt in
        mk_expr ~expr_loc:new_loc
          (Eidapp
             ( Qident (mk_id "push"),
               stack_fuel_args @ [ push_type; pushed_data ] ))
    | I_some ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "some_op"), stack_fuel_args))
    | I_none t ->
        let inner_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "none_op"), stack_fuel_args @ [ inner_type ]))
    | I_unit ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "unit_op"), stack_fuel_args))
    | I_if_none (i1, i2) ->
        let top = mk_expr (Eidapp (Qident (mk_id "peek"), [ e_stack ])) in
        let pat_none =
          mk_pat (Papp (Qident (mk_id "D_none"), [ mk_pat (Pvar (mk_id "_")) ]))
        in
        let pat_some =
          mk_pat
            (Papp
               ( Qident (mk_id "D_some"),
                 [ mk_pat (Pvar (mk_id "dt")); mk_pat (Pvar (mk_id "_")) ] ))
        in
        (* let pat_none =  mk_pat (Papp (Qident (mk_id "SD"), [p_none])) in
           let pat_some =  mk_pat (Papp (Qident (mk_id "SD"), [p_some])) in *)
        let pat_absurd = (mk_pat Pwild, mk_expr Eabsurd) in
        let branch_true = inst i1 in
        let branch_false = inst i2 in
        let n_lit = int_literal ILitDec ~neg:false "1" in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let dt = mk_expr (Eident (Qident (mk_id "dt"))) in
        let drop_head =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        (* s = s[1..] *)
        let final_cat =
          mk_expr (Eidapp (Qident (mk_id "infix ::"), [ dt; e_stack ]))
        in
        (* top :: s *)
        let mid_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat))
        in
        let btrue_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, branch_true))
        in
        let bfalse_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_false))
        in
        let branch =
          [ (pat_none, btrue_let); (pat_some, bfalse_let); pat_absurd ]
        in
        mk_expr ~expr_loc:new_loc (Ematch (top, branch, []))
    | I_if_some (i1, i2) ->
        inst { r with desc = { value = I_if_none (i2, i1); loc } }
    | I_pair ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "pair"), stack_fuel_args))
    | I_car ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "car"), stack_fuel_args))
    | I_cdr ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "cdr"), stack_fuel_args))
    | I_left t ->
        let inner_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "left_op"), stack_fuel_args @ [ inner_type ]))
    | I_right t ->
        let inner_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "right_op"), stack_fuel_args @ [ inner_type ]))
    | I_if_left (i1, i2) ->
        let top = mk_expr (Eidapp (Qident (mk_id "peek"), [ e_stack ])) in
        let pat_left =
          mk_pat
            (Papp
               ( Qident (mk_id "D_left"),
                 [ mk_pat (Pvar (mk_id "dt")); mk_pat (Pvar (mk_id "_")) ] ))
        in
        let pat_right =
          mk_pat
            (Papp
               ( Qident (mk_id "D_right"),
                 [ mk_pat (Pvar (mk_id "dt")); mk_pat (Pvar (mk_id "_")) ] ))
        in
        (* let pat_left =  mk_pat (Papp (Qident (mk_id "SD"), [p_left])) in
           let pat_right =  mk_pat (Papp (Qident (mk_id "SD"), [p_right])) in *)
        let pat_absurd = (mk_pat Pwild, mk_expr Eabsurd) in
        let branch_true = inst i1 in
        let branch_false = inst i2 in
        let n_lit = int_literal ILitDec ~neg:false "1" in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let dt = mk_expr (Eident (Qident (mk_id "dt"))) in
        (* let dt =  mk_expr (Eidapp (Qident (mk_id "SD"), [pre_dt])) in *)
        let drop_head =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        (* s = s[1..] *)
        let final_cat =
          mk_expr (Eidapp (Qident (mk_id "infix ::"), [ dt; e_stack ]))
        in
        let mid_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat))
        in
        let btrue_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_true))
        in
        let bfalse_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_false))
        in
        let branch =
          [ (pat_left, btrue_let); (pat_right, bfalse_let); pat_absurd ]
        in
        mk_expr ~expr_loc:new_loc (Ematch (top, branch, []))
    | I_if_right (i1, i2) ->
        inst { r with desc = { loc; value = I_if_left (i2, i1) } }
    | I_nil t ->
        let inner_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "nil_op"), stack_fuel_args @ [ inner_type ]))
    | I_cons ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "cons_op"), stack_fuel_args))
    | I_if_cons (i1, i2) ->
        let top = mk_expr (Eidapp (Qident (mk_id "peek"), [ e_stack ])) in
        let pat_nil =
          mk_pat
            (Papp
               ( Qident (mk_id "D_list"),
                 [ mk_pat (Pvar (mk_id "_Nil")); mk_pat (Pvar (mk_id "_")) ] ))
        in
        let cons_var =
          mk_pat
            (Papp
               ( Qident (mk_id "Cons"),
                 [ mk_pat (Pvar (mk_id "hd")); mk_pat (Pvar (mk_id "tl")) ] ))
        in
        let pat_cons =
          mk_pat
            (Papp
               (Qident (mk_id "D_list"), [ cons_var; mk_pat (Pvar (mk_id "t")) ]))
        in
        (* let pat_nil =  mk_pat (Papp (Qident (mk_id "SD"), [p_nil])) in
           let pat_cons =  mk_pat (Papp (Qident (mk_id "SD"), [p_cons])) in *)
        let pat_absurd = (mk_pat Pwild, mk_expr Eabsurd) in
        let branch_true = inst i1 in
        let branch_false = inst i2 in
        let n_lit = int_literal ILitDec ~neg:false "1" in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let hd = mk_expr (Eident (Qident (mk_id "hd"))) in
        (* let hd =  mk_expr (Eidapp (Qident (mk_id "SD"), [pre_hd])) in *)
        let tl = mk_expr (Eident (Qident (mk_id "tl"))) in
        let t = mk_expr (Eident (Qident (mk_id "t"))) in
        let lst = mk_expr (Eidapp (Qident (mk_id "D_list"), [ tl; t ])) in
        (* let lst =  mk_expr (Eidapp (Qident (mk_id "SD"), [pre_lst])) in *)
        let drop_head =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        (* s = s[1..] *)
        let first_cat =
          mk_expr (Eidapp (Qident (mk_id "infix ::"), [ lst; e_stack ]))
        in
        let final_cat =
          mk_expr (Eidapp (Qident (mk_id "infix ::"), [ hd; first_cat ]))
        in
        let mid_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, final_cat))
        in
        let btrue_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, mid_let, branch_true))
        in
        let bfalse_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, branch_false))
        in
        let branch =
          [ (pat_cons, btrue_let); (pat_nil, bfalse_let); pat_absurd ]
        in
        mk_expr ~expr_loc:new_loc (Ematch (top, branch, []))
    | I_size ->
        (*FIXME: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "size_op"), stack_fuel_args))
    | I_empty_set ct ->
        (*FIXME: Implement in WhyML *)
        let inner_ctype = typ ct in
        mk_expr ~expr_loc:new_loc
          (Eidapp
             (Qident (mk_id "empty_set_op"), stack_fuel_args @ [ inner_ctype ]))
    | I_empty_map (ct, t) ->
        (*FIXME: Implement in WhyML *)
        let key_ctype = typ ct in
        let value_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp
             ( Qident (mk_id "empty_map_op"),
               stack_fuel_args @ [ key_ctype; value_type ] ))
    | I_empty_big_map (ct, t) ->
        (*FIXME: Implement in WhyML *)
        let key_ctype = typ ct in
        let value_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp
             ( Qident (mk_id "empty_big_map_op"),
               stack_fuel_args @ [ key_ctype; value_type ] ))
    | I_map _i ->
        assert false
        (* TODO: implement *)
        (*FIXME: Implement in WhyML *)
    | I_iter _i ->
        (* FIXME: only working for lists *)
        assert false
        (* let body = inst_annotated i in
           let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
           let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in
           let pat_list  = mk_pat (Papp  (Qident (mk_id "List"), [mk_pat (Pvar (mk_id "lst"));mk_pat (Pvar (mk_id "_"))])) in
           let pat_absurd = mk_pat Pwild,mk_expr Eabsurd in
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
           mk_expr (Ematch (d_field,branch,[])) *)
        (* let pat_right = mk_pat (Papp  (Qident (mk_id "Right"), [mk_pat (Pvar (mk_id "dt"));mk_pat (Pvar (mk_id "_"))])) in *)
        (*----------------------------------------------------------------------------*)
        (*let body = inst_annotated i in
          let fun_id = mk_id "iter_fun" in
          let kind = Expr.RKnone in
          let i_let =  mk_expr (Elet (id_stack, false, kind, body, e_stack)) in
          let pat = mk_pat (Pvar id_stack_t) in
          let mask = Ity.MaskVisible in
          let pty = Some stack_ty in
          let binders = [stack_binder;fuel_binder] in
          let fun_def = [fun_id,false,kind,binders,pty,pat,mask,empty_spec,i_let] in
          let deleteME = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in
          mk_expr (Erec (fun_def,deleteME))*)
        (*----------------------------------------------------------------------------*)

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
           mk_expr (Ematch (d_field,branch,[])) *)
    | I_mem ->
        (*FIXME: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "mem_op"), stack_fuel_args))
    | I_get ->
        (*FIXME: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "get_op"), stack_fuel_args))
    | I_update ->
        (*FIXME: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "update_op"), stack_fuel_args))
    | I_if (i1, i2) ->
        (* TODO: ask about non exhaustive pm *)
        let top = mk_expr (Eidapp (Qident (mk_id "peek"), [ e_stack ])) in
        let pat_bool =
          mk_pat (Papp (Qident (mk_id "D_bool"), [ mk_pat (Pvar (mk_id "b")) ]))
        in
        (* let pat_bool = mk_pat (Papp (Qident (mk_id "SD"), [pre_pat_bool])) in  *)
        let pat_absurd = (mk_pat Pwild, mk_expr Eabsurd) in
        let branch_true = inst i1 in
        let branch_false = inst i2 in
        let bool_eval = mk_expr (Eident (Qident (mk_id "b"))) in
        let n_lit = int_literal ILitDec ~neg:false "1" in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let drop_head =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        let btrue_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, branch_true))
        in
        let bfalse_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, drop_head, branch_false))
        in
        let if_eval = mk_expr (Eif (bool_eval, btrue_let, bfalse_let)) in
        let branch = [ (pat_bool, if_eval); pat_absurd ] in
        mk_expr ~expr_loc:new_loc (Ematch (top, branch, []))
    | I_loop i ->
        let top = mk_expr (Eidapp (Qident (mk_id "peek"), [ e_stack ])) in
        (* let d_field = mk_expr (Eidapp (Qident (mk_id "d"), [top])) in	       *)
        let pat_bool =
          mk_pat (Papp (Qident (mk_id "D_bool"), [ mk_pat (Pvar (mk_id "b")) ]))
        in
        let pat_absurd = (mk_pat Pwild, mk_expr Eabsurd) in
        let n_lit = int_literal ILitDec ~neg:false "1" in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let drop_head =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        let body = inst i in
        let bool_eval = mk_expr (Eident (Qident (mk_id "b"))) in
        let kind = Expr.RKnone in
        let fun_id = mk_id "loop_fun" in
        let branch_true =
          mk_expr (Elet (id_stack, false, kind, body, e_stack))
        in
        let rec_call =
          mk_expr (Eidapp (Qident fun_id, [ branch_true; e_fuel ]))
        in
        let if_eval = mk_expr (Eif (bool_eval, rec_call, e_stack)) in
        let drop_let =
          mk_expr (Elet (id_stack, false, kind, drop_head, if_eval))
        in
        let branch = [ (pat_bool, drop_let); pat_absurd ] in
        let mtch = mk_expr (Ematch (top, branch, [])) in
        let pat = mk_pat (Pvar id_stack_t) in
        let mask = Ity.MaskVisible in
        let pty = Some stack_ty in
        let binders = [ stack_binder; fuel_binder ] in
        let fun_def =
          [ (fun_id, false, kind, binders, pty, pat, mask, empty_spec, mtch) ]
        in
        mk_expr ~expr_loc:new_loc (Erec (fun_def, e_stack))
    | I_loop_left _i ->
        assert false
        (* TODO: implement *)
        (*FIXME: Implement in WhyML *)
    | I_lambda (_t1, _t2, _i) ->
        assert false
        (* TODO: implement *)
        (*FIXME: Implement in WhyML *)
    | I_dip i ->
        let top_id = mk_id "top" in
        let top_value = mk_expr (Eident (Qident top_id)) in
        let zero_lit = int_literal ILitDec ~neg:false "0" in
        let zero = mk_expr (Econst (Constant.ConstInt zero_lit)) in
        let top =
          mk_expr (Eidapp (Qident (mk_id "mixfix []"), [ e_stack; zero ]))
        in
        let n_lit = int_literal ILitDec ~neg:false "1" in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let headless =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        (* s = s[1..] *)
        let final_cat =
          mk_expr (Eidapp (Qident (mk_id "infix ::"), [ top_value; e_stack ]))
        in
        (* top :: s *)
        let last_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, inst i, final_cat))
        in
        let middle_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, headless, last_let))
        in
        mk_expr ~expr_loc:new_loc
          (Elet (top_id, false, Expr.RKnone, top, middle_let))
    (*
       let top,__stack__ = pop _stack__ in
         let __stack__ = inst i __stack__ in
       let __stack__ = top::__stack__ in
       __stack__
    *)
    (* FIXME: let top_id = mk_id "top" in
       let top_value = mk_expr (Eident (Qident top_id)) in
          let top_and_stack = mk_expr (Eidapp (comma_symb, [top_value;e_stack])) in
          let pop = mk_expr (Eidapp (Qident (mk_id "pop"), [e_stack])) in (* top = s[0] *)
          let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [top_value;e_stack])) in
       let last_let = mk_expr (Elet (id_stack, false, Expr.RKnone, inst i, final_cat)) in
        (* let middle_let =  mk_expr (Elet (id_stack, false, Expr.RKnone, pop, last_let)) in	 *)
       mk_expr ~expr_loc:new_loc  (Elet (top_id, false, Expr.RKnone, top_and_stack, middle_let)) *)
    (*------------------------------------------------------------------------------------------------*)
    (*let top_id = mk_id "top" in
      let top_value = mk_expr (Eident (Qident top_id)) in
      let top = mk_expr (Eidapp (Qident (mk_id "peek"), [e_stack])) in (* top = s[0] *)
      let n_lit = int_literal ILitDec ~neg:false "1" in
         let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
      let headless = mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [e_stack;n])) in (* s = s[1..] *)
      let final_cat = mk_expr (Eidapp (Qident (mk_id "infix ::"), [top;e_stack])) in (* top :: s *)
      let last_let = mk_expr (Elet (id_stack, false, Expr.RKnone, inst i, final_cat)) in
      let middle_let =  mk_expr (Elet (id_stack, false, Expr.RKnone, headless, last_let)) in
      mk_expr ~expr_loc:new_loc  (Elet (top_id, false, Expr.RKnone, top, middle_let)) *)
    | I_dip_n (n, i) ->
        let top_id = mk_id "top" in
        let top_value = mk_expr (Eident (Qident top_id)) in
        let top = mk_expr (Eidapp (Qident (mk_id "peek"), [ e_stack ])) in
        (* top = s[0] *)
        let n = Z.to_string n in
        let n_lit =
          int_literal ILitDec ~neg:false (Lexlib.remove_underscores n)
        in
        let n = mk_expr (Econst (Constant.ConstInt n_lit)) in
        let headless =
          mk_expr (Eidapp (Qident (mk_id "mixfix [_..]"), [ e_stack; n ]))
        in
        (* s = s[1..] *)
        let final_cat =
          mk_expr (Eidapp (Qident (mk_id "infix ::"), [ top_value; e_stack ]))
        in
        (* top :: s *)
        let last_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, inst i, final_cat))
        in
        let middle_let =
          mk_expr (Elet (id_stack, false, Expr.RKnone, headless, last_let))
        in
        mk_expr ~expr_loc:new_loc
          (Elet (top_id, false, Expr.RKnone, top, middle_let))
    | I_failwith ->
        mk_expr ~expr_loc:new_loc (Eraise (Qident (mk_id "Failing"), None))
    | I_cast t ->
        (*TODO: Implement in WhyML *)
        let value_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "cast_op"), stack_fuel_args @ [ value_type ]))
    | I_concat ->
        (*TODO: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "concat_op"), stack_fuel_args))
    | I_slice ->
        (*TODO: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "slice_op"), stack_fuel_args))
    | I_pack ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "pack"), stack_fuel_args))
    | I_unpack t ->
        let inner_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "unpack_op"), stack_fuel_args @ [ inner_type ]))
    | I_add ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "add"), stack_fuel_args))
    | I_sub ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "sub"), stack_fuel_args))
    | I_mul ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "mul"), stack_fuel_args))
    | I_ediv ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "ediv"), stack_fuel_args))
    | I_abs ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "abs_op"), stack_fuel_args))
    | I_isnat ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "isnat"), stack_fuel_args))
    | I_int ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "int_op"), stack_fuel_args))
    | I_neg ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "neg"), stack_fuel_args))
    | I_lsl ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "lsl_op"), stack_fuel_args))
    | I_lsr ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "lsr_op"), stack_fuel_args))
    | I_or ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "or"), stack_fuel_args))
    | I_and ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "and"), stack_fuel_args))
    | I_xor ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "xor"), stack_fuel_args))
    | I_not ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "not_op"), stack_fuel_args))
    | I_compare ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "compare_op"), stack_fuel_args))
    | I_eq ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "eq"), stack_fuel_args))
    | I_neq ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "neq"), stack_fuel_args))
    | I_lt ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "lt"), stack_fuel_args))
    | I_gt ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "gt"), stack_fuel_args))
    | I_le ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "le"), stack_fuel_args))
    | I_ge ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "ge"), stack_fuel_args))
    | I_self ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "self_op"), stack_fuel_args))
    | I_contract t ->
        let inner_type = typ t in
        mk_expr ~expr_loc:new_loc
          (Eidapp
             (Qident (mk_id "contract_op"), stack_fuel_args @ [ inner_type ]))
    | I_transfer_tokens ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "transfer_tokens"), stack_fuel_args))
    | I_set_delegate ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "set_delegate_op"), stack_fuel_args))
    | I_create_contract _p ->
        assert false
        (* TODO: implement *)
        (*FIXME: Implement in WhyML *)
    | I_implicit_account ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "implicit_account_op"), stack_fuel_args))
    | I_now ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "now_op"), stack_fuel_args))
    | I_amount ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "amount_op"), stack_fuel_args))
    | I_balance ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "balance_op"), stack_fuel_args))
    | I_check_signature ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "check_signature_op"), stack_fuel_args))
    | I_blake2b ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "blake2b_op"), stack_fuel_args))
    | I_sha256 ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "sha256_op"), stack_fuel_args))
    | I_sha512 ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "sha512_op"), stack_fuel_args))
    | I_hash_key ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "hash_key_op"), stack_fuel_args))
    | I_source ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "source_op"), stack_fuel_args))
    | I_sender ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "sender_op"), stack_fuel_args))
    | I_address ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "address_op"), stack_fuel_args))
    | I_chain_id ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "chain_id_op"), stack_fuel_args))
    | I_noop ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "noop"), stack_fuel_args))
    | I_unpair ->
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "unpair"), stack_fuel_args))
    (* renaming operation on annotations *)
    | I_rename ->
        (*TODO: Implement in WhyML *)
        mk_expr ~expr_loc:new_loc
          (Eidapp (Qident (mk_id "rename_op"), stack_fuel_args))
    | I_exec -> assert false (*TODO: Implement in WhyML *)
    (* mk_expr (Eidapp (Qident (mk_id "exec_op"), stack_fuel_args)) *)
    | I_create_account (* considered deprecated *) | I_steps_to_quota ->
        assert false
    (* considered deprecated *)
    (* Loc.errorm "This is not supported@." *)
  in
  let desc = { Location.loc; value = desc } in
  to_expr_typed x { desc; stack_before; stack_after }

(*FIXME: refactor for new type system *)
and data t d =
  let rec aux loc d =
    let expr_loc = mk_position loc in
    match d with
    | P_int n ->
        (* let t = typ (mk_position lt) t in *)
        let n = Z.to_string n in
        let n = int_literal ILitDec ~neg:false (Lexlib.remove_underscores n) in
        let i = mk_expr (Econst (Constant.ConstInt n)) in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_int"), [ i ]))
    | P_string s ->
        (* let t = typ (mk_position lt) t in FIXME: *)
        let str_const = mk_expr (Econst (Constant.ConstStr s)) in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_string"), [ str_const ]))
    | P_bool b ->
        let t = typ t in
        let v_true = mk_expr Etrue in
        let v_false = mk_expr Efalse in
        let arg = if b then v_true else v_false in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_bool"), [ arg; t ]))
    | P_pair (d1, d2) ->
        let t = typ t in
        let dt1 = aux loc d1 in
        let dt2 = aux loc d2 in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_pair"), [ dt1; dt2; t ]))
    | P_left d ->
        let t = typ t in
        let dt = aux loc d in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_left"), [ dt; t ]))
    | P_right d ->
        let t = typ t in
        let dt = aux loc d in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_right"), [ dt; t ]))
    | P_some d ->
        let t = typ t in
        let dt = aux loc d in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_some"), [ dt; t ]))
    | P_none ->
        let t = typ t in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_none"), [ t ]))
    | P_unit ->
        let t = typ t in
        mk_expr ~expr_loc (Eidapp (Qident (mk_id "D_unit"), [ t ]))
    | P_bytes _ | P_map _ | P_list _ -> assert false
    (* TODO: implement *)
  in
  aux t.loc d

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
     | _ -> assert false (* TODO *) end *)

(* let program {param;storage;code} =
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
   [use_axiomatic; use_data_types; use_seq; use_int; use_nat; decl] *)

let spec_filter l =
  List.partition
    (fun (spec_t, _spec) -> match spec_t with Sp_pre -> true | _ -> false)
    l

let spec_parser l =
  let sp_pre_unparsed, sp_post_unparsed = spec_filter l in
  let sp_pre =
    List.map
      (fun (_, sp) -> Why3.Lexer.parse_term (Lexing.from_string sp))
      sp_pre_unparsed
  in
  let sp_post_no_pat =
    List.map
      (fun (_, sp) -> Why3.Lexer.parse_term (Lexing.from_string sp))
      sp_post_unparsed
  in
  let sp_post =
    List.map
      (fun x -> (Loc.dummy_position, [ (mk_pat (Pvar (mk_id "result")), x) ]))
      sp_post_no_pat
  in
  (sp_pre, sp_post)

let translate_typed_program ({ param; storage; code } : Adt_typ.program_typed)
    spec =
  let loc = mk_position code.desc.loc in
  let code = inst code in
  let param = term @@ type_of_parser_type param in  

  let storage = term @@ type_of_parser_type storage in

  let spec =
    match spec with
    | [] ->
        {
          sp_pre = [ pre_len; pre_fuel; mk_pre_typ param storage ];
          sp_post =
            [
              ( Loc.dummy_position,
                [ (mk_pat (Pvar (mk_id "result")), post_len) ] );
              mk_post_typ storage;
            ];
          sp_xpost = [];
          sp_reads = [];
          sp_writes = [];
          sp_alias = [];
          sp_variant = [];
          sp_checkrw = false;
          sp_diverge = false;
          sp_partial = false;
        }
    | l ->
        let sp_pre, sp_post = spec_parser l in
        {
          sp_pre = sp_pre @ [ pre_len; pre_fuel; mk_pre_typ param storage ];
          sp_post =
            sp_post
            @ [
                ( Loc.dummy_position,
                  [ (mk_pat (Pvar (mk_id "result")), post_len) ] );
                mk_post_typ storage;
              ];
          sp_xpost = [];
          sp_reads = [];
          sp_writes = [];
          sp_alias = [];
          sp_variant = [];
          sp_checkrw = false;
          sp_diverge = false;
          sp_partial = false;
        }
  in
  let kind = Expr.RKnone in
  let i_let = mk_expr (Elet (id_stack, false, kind, code, e_stack)) in
  let pat = mk_pat (Pvar id_stack_t) in
  let mask = Ity.MaskVisible in
  let pty = Some stack_ty in
  let binders = [ stack_binder; fuel_binder ] in
  let f_exp = Efun (binders, pty, pat, mask, spec, i_let) in
  let f_exp = mk_expr f_exp in
  let decl = (loc, Dlet (mk_id "test", false, kind, f_exp)) in
  [ use_axiomatic; use_data_types; use_seq; use_int; decl ]
