
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



type sort = Int | Set | Tid

type var_info_t

module V : Variable.S
  with type sort = sort
  with type info = var_info_t


type tid =
  | VarTh of V.t
  | NoTid
and integer =
    Val           of int
  | Var           of V.t
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | Mod           of integer * integer
  | ArrayRd       of Expression.arrays * tid
  | SetMin        of set
  | SetMax        of set
and set =
    VarSet        of V.t
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
  | Lower         of set * integer
and term =
  | IntV          of integer
  | SetV          of set
and fun_term =
  | FunVar        of V.t
  | FunUpd        of fun_term * tid * term
and eq =          term * term
and diseq =       term * term
and atom =
    Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | In            of integer * set
  | Subset        of set * set
  | Eq            of eq
  | InEq          of diseq
  | TidEq         of tid * tid
  | TidInEq       of tid * tid
  | FunEq         of fun_term * fun_term
  | FunInEq       of fun_term * fun_term
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula


exception NotConjunctiveExpr of formula

module ThreadSet : Set.S with type elt = tid

val build_var : ?fresh:bool ->
                ?treat_as_pc:bool ->
                V.id ->
                sort ->
                bool ->
                V.shared_or_local ->
                V.procedure_name ->
                V.t

val treat_as_pc    : V.t -> bool

val is_int_formula : Expression.formula   -> bool

val integer_to_str  : integer  -> string
val formula_to_str  : formula -> string
val literal_to_str  : literal -> string
val atom_to_str     : atom -> string

val all_varid             : formula -> V.id list
val all_global_varid      : formula -> V.id list
val all_local_varid       : formula -> V.id list
val all_varid_set         : formula -> V.VarIdSet.t
val all_global_varid_set  : formula -> V.VarIdSet.t
val all_local_varid_set   : formula -> V.VarIdSet.t

val all_vars              : formula -> V.t list
val all_global_vars       : formula -> V.t list
val all_local_vars        : formula -> V.t list
val all_vars_set          : formula -> V.VarSet.t
val all_global_vars_set   : formula -> V.VarSet.t
val all_local_vars_set    : formula -> V.VarSet.t

val all_global_vars_without_param : formula -> V.t list
val all_local_vars_without_param  : formula -> V.t list

val voc : formula -> tid list


(* LINEARITY *)
val has_variable      : integer -> bool

val formula_is_linear : formula -> bool
val term_is_linear    : integer -> bool

val voc_to_var : tid -> V.t

