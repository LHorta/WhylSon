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

open Michelson

type typ = Adt.parser_typ Adt.with_loc
type data = Adt.parser_data
type program = Adt.program

type inst_t =
  | I_seq of inst * inst
  | I_drop
  | I_drop_n of Z.t
  | I_dup
  | I_swap
  | I_dig of Z.t
  | I_dug of Z.t
  | I_push of typ * data
  | I_some
  | I_none of typ
  | I_unit
  | I_if_none of inst * inst
  | I_if_some of inst * inst
  | I_pair
  | I_car
  | I_cdr
  | I_left of typ
  | I_right of typ
  | I_if_left of inst * inst
  | I_if_right of inst * inst
  | I_nil of typ
  | I_cons
  | I_if_cons of inst * inst
  | I_size
  | I_empty_set of typ
  | I_empty_map of typ * typ
  | I_empty_big_map of typ * typ
  | I_map of inst
  | I_iter of inst
  | I_mem
  | I_get
  | I_update
  | I_if of inst * inst
  | I_loop of inst
  | I_loop_left of inst
  | I_lambda of typ * typ * inst
  | I_exec
  | I_dip of inst
  | I_dip_n of Z.t * inst
  | I_failwith
  | I_cast of typ
  | I_rename
  | I_concat
  | I_slice
  | I_pack
  | I_unpack of typ
  | I_add
  | I_sub
  | I_mul
  | I_ediv
  | I_abs
  | I_isnat
  | I_int
  | I_neg
  | I_lsl
  | I_lsr
  | I_or
  | I_and
  | I_xor
  | I_not
  | I_compare
  | I_eq
  | I_neq
  | I_lt
  | I_gt
  | I_le
  | I_ge
  | I_self
  | I_contract of typ
  | I_transfer_tokens
  | I_set_delegate
  | I_create_account
  | I_create_contract of program
  | I_implicit_account
  | I_now
  | I_amount
  | I_balance
  | I_check_signature
  | I_blake2b
  | I_sha256
  | I_sha512
  | I_hash_key
  | I_steps_to_quota
  | I_source
  | I_sender
  | I_address
  | I_chain_id
  | I_noop
  | I_unpair

and type_stack_info = { stack_size : int; stack_type : Adt.typ list }

and inst = {
  desc : inst_t Location.with_loc;
  stack_before : type_stack_info;
  stack_after : type_stack_info;
}

and program_typed = { param : typ; storage : typ; code : inst }

type spec_t = Sp_variant | Sp_invariant | Sp_pre | Sp_post | Sp_post_exn
type spec = spec_t * string
