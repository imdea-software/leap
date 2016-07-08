
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


open Printf
open LeapLib


module Eparser = ExprParser
module Elexer  = ExprLexer
module Expr    = Expression
module Symtbl  = ExprSymTable
module SolOpt  = SolverOptions

(****************)
(* main         *)
(****************)

let _ =
  try
    ThmArgs.parse_args ();

    let phi = Parser.open_and_parse !ThmArgs.phiFile
        (Eparser.single_formula Elexer.norm) in

    ThmSolver.compute_model(true);
    let thm_phi = ThmInterface.formula_to_thm_formula phi in

    (* Solver options *)
    let opt = SolOpt.new_opt () in
    SolOpt.set_cutoff_strategy opt !ThmArgs.coType;
    SolOpt.set_use_quantifiers opt !ThmArgs.use_q;
    SolOpt.set_use_arrangement_generator opt !ThmArgs.arrangement_gen;

    let sat = ThmSolver.check_sat opt thm_phi in
    if Sat.is_sat sat then begin
        ThmSolver.print_model();
        print_endline "SAT"
      end
    else
      print_endline "UNSAT";
    ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
