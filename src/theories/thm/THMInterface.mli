
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




val sort_to_thm_sort : Expression.sort -> THMExpression.sort
val var_to_thm_var : Expression.V.t -> THMExpression.V.t
val tid_to_thm_tid : Expression.tid -> THMExpression.tid
val term_to_thm_term : Expression.term -> THMExpression.term
val set_to_thm_set : Expression.set -> THMExpression.set
val elem_to_thm_elem : Expression.elem -> THMExpression.elem
val addr_to_thm_addr : Expression.addr -> THMExpression.addr
val cell_to_thm_cell : Expression.cell -> THMExpression.cell
val setth_to_thm_setth : Expression.setth -> THMExpression.setth
val setelem_to_thm_setelem : Expression.setelem -> THMExpression.setelem
val path_to_thm_path : Expression.path -> THMExpression.path
val mem_to_thm_mem : Expression.mem -> THMExpression.mem
val int_to_thm_int : Expression.integer -> THMExpression.integer
val literal_to_thm_literal : Expression.literal -> THMExpression.literal
val conj_formula_to_thm_conj_formula : Expression.conjunctive_formula ->
                                       THMExpression.conjunctive_formula
val formula_to_thm_formula : Expression.formula -> THMExpression.formula


val sort_to_expr_sort : THMExpression.sort -> Expression.sort
val var_to_expr_var : THMExpression.V.t -> Expression.V.t
val tid_to_expr_tid : THMExpression.tid -> Expression.tid
val term_to_expr_term : THMExpression.term -> Expression.term
val set_to_expr_set : THMExpression.set -> Expression.set
val elem_to_expr_elem : THMExpression.elem -> Expression.elem
val addr_to_expr_addr : THMExpression.addr -> Expression.addr
val cell_to_expr_cell : THMExpression.cell -> Expression.cell
val setth_to_expr_setth : THMExpression.setth -> Expression.setth
val setelem_to_expr_setelem : THMExpression.setelem -> Expression.setelem
val path_to_expr_path : THMExpression.path -> Expression.path
val mem_to_expr_mem : THMExpression.mem -> Expression.mem
val int_to_expr_int : THMExpression.integer -> Expression.integer
val literal_to_expr_literal : THMExpression.literal -> Expression.literal
val conj_formula_to_expr_conj_formula : THMExpression.conjunctive_formula ->
                                        Expression.conjunctive_formula
val formula_to_expr_formula : THMExpression.formula -> Expression.formula

