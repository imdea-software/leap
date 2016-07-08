
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)



val sort_to_tll_sort : Expression.sort -> TLLExpression.sort
val var_to_tll_var : Expression.V.t -> TLLExpression.V.t
val tid_to_tll_tid : Expression.tid -> TLLExpression.tid
val term_to_tll_term : Expression.term -> TLLExpression.term
val set_to_tll_set : Expression.set -> TLLExpression.set
val elem_to_tll_elem : Expression.elem -> TLLExpression.elem
val addr_to_tll_addr : Expression.addr -> TLLExpression.addr
val cell_to_tll_cell : Expression.cell -> TLLExpression.cell
val setth_to_tll_setth : Expression.setth -> TLLExpression.setth
val setelem_to_tll_setelem : Expression.setelem -> TLLExpression.setelem
val path_to_tll_path : Expression.path -> TLLExpression.path
val mem_to_tll_mem : Expression.mem -> TLLExpression.mem
val int_to_tll_int : Expression.integer -> TLLExpression.integer
val formula_to_tll_formula : Expression.formula -> TLLExpression.formula

val sort_to_expr_sort : TLLExpression.sort -> Expression.sort
val var_to_expr_var : TLLExpression.V.t -> Expression.V.t
val tid_to_expr_tid : TLLExpression.tid -> Expression.tid
val term_to_expr_term : TLLExpression.term -> Expression.term
val set_to_expr_set : TLLExpression.set -> Expression.set
val elem_to_expr_elem : TLLExpression.elem -> Expression.elem
val addr_to_expr_addr : TLLExpression.addr -> Expression.addr
val cell_to_expr_cell : TLLExpression.cell -> Expression.cell
val setth_to_expr_setth : TLLExpression.setth -> Expression.setth
val setelem_to_expr_setelem : TLLExpression.setelem -> Expression.setelem
val path_to_expr_path : TLLExpression.path -> Expression.path
val mem_to_expr_mem : TLLExpression.mem -> Expression.mem
val int_to_expr_int : TLLExpression.integer -> Expression.integer
val formula_to_expr_formula : TLLExpression.formula -> Expression.formula
