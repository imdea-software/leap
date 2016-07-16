
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



exception NotAnIntExpression of string


val variable_to_int_variable : Expression.V.t -> NumExpression.V.t
val integer_to_int_integer   : Expression.integer  -> NumExpression.integer
val formula_to_int_formula   : Expression.formula  -> NumExpression.formula

val variable_to_expr_variable : NumExpression.V.t -> Expression.V.t
val integer_to_expr_integer   : NumExpression.integer  -> Expression.integer
val formula_to_expr_formula   : NumExpression.formula  -> Expression.formula
