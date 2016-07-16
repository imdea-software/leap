
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



exception NotAPairsExpression of string


val variable_to_pairs_variable : Expression.V.t -> PairsExpression.V.t
val integer_to_pairs_integer   : Expression.integer  -> PairsExpression.integer
val formula_to_pairs_formula   : Expression.formula  -> PairsExpression.formula

val variable_to_expr_variable : PairsExpression.V.t -> Expression.V.t
val integer_to_expr_integer   : PairsExpression.integer  -> Expression.integer
val formula_to_expr_formula   : PairsExpression.formula  -> Expression.formula
