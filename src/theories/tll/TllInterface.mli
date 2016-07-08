
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



val sort_to_tll_sort : Expression.sort -> TllExpression.sort
val var_to_tll_var : Expression.V.t -> TllExpression.V.t
val tid_to_tll_tid : Expression.tid -> TllExpression.tid
val term_to_tll_term : Expression.term -> TllExpression.term
val set_to_tll_set : Expression.set -> TllExpression.set
val elem_to_tll_elem : Expression.elem -> TllExpression.elem
val addr_to_tll_addr : Expression.addr -> TllExpression.addr
val cell_to_tll_cell : Expression.cell -> TllExpression.cell
val setth_to_tll_setth : Expression.setth -> TllExpression.setth
val setelem_to_tll_setelem : Expression.setelem -> TllExpression.setelem
val path_to_tll_path : Expression.path -> TllExpression.path
val mem_to_tll_mem : Expression.mem -> TllExpression.mem
val int_to_tll_int : Expression.integer -> TllExpression.integer
val formula_to_tll_formula : Expression.formula -> TllExpression.formula

val sort_to_expr_sort : TllExpression.sort -> Expression.sort
val var_to_expr_var : TllExpression.V.t -> Expression.V.t
val tid_to_expr_tid : TllExpression.tid -> Expression.tid
val term_to_expr_term : TllExpression.term -> Expression.term
val set_to_expr_set : TllExpression.set -> Expression.set
val elem_to_expr_elem : TllExpression.elem -> Expression.elem
val addr_to_expr_addr : TllExpression.addr -> Expression.addr
val cell_to_expr_cell : TllExpression.cell -> Expression.cell
val setth_to_expr_setth : TllExpression.setth -> Expression.setth
val setelem_to_expr_setelem : TllExpression.setelem -> Expression.setelem
val path_to_expr_path : TllExpression.path -> Expression.path
val mem_to_expr_mem : TllExpression.mem -> Expression.mem
val int_to_expr_int : TllExpression.integer -> Expression.integer
val formula_to_expr_formula : TllExpression.formula -> Expression.formula
