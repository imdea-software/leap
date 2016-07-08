
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




type cond_effect_t = Expression.formula * (* Condition list               *)
                     Expression.formula * (* Term - Expression assignment *)
                     Expression.pc_t    * (* Current program counter      *)
                     Expression.pc_t      (* Next program counter         *)


type malloc_info =
  {
    tids       : Expression.tid list;
    gAddrs     : Expression.V.t list;
    gSets      : Expression.V.t list;
    lAddrs     : Expression.V.t list;
    lSets      : Expression.V.t list;
  }


type prog_type = Num | Heap

val fresh_addr : Expression.V.t


val construct_stm_term_eq : malloc_info ->
                            Statement.term ->
                            Expression.V.shared_or_local ->
                            Statement.expr_t ->
                            (Expression.term list * Expression.formula)



val construct_stm_term_eq_as_array : malloc_info ->
                                     Statement.term ->
                                     Expression.V.shared_or_local ->
                                     Statement.expr_t ->
                                     (Expression.term list * Expression.formula)


val gen_st_cond_effect : prog_type ->
                         Statement.statement_t ->
                         bool ->
                         cond_effect_t list


val gen_st_cond_effect_as_array : prog_type ->
                                  Statement.statement_t ->
                                  bool ->
                                  Expression.V.shared_or_local ->
                                  cond_effect_t list
