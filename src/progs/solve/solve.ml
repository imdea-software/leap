
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
    SolveArgs.parse_args ();
    let ch = SolveArgs.open_input () in
    let phi = Parser.parse ch (Eparser.single_formula Elexer.norm) in
    SolveArgs.close_input ();

    (* Choose decision procedure *)
    Printf.printf "Parsed formula is:\n%s\n\n" (Expr.formula_to_str phi);

    (* Solver options *)
    let opt = SolOpt.new_opt () in
    SolOpt.set_cutoff_strategy opt !SolveArgs.coType;
    SolOpt.set_use_quantifiers opt !SolveArgs.use_quantifiers;
    SolOpt.set_use_arrangement_generator opt !SolveArgs.arrangement_gen;

    let sol =
      match !SolveArgs.dpType with
      | DP.NoDP -> (print_endline "NO DP PROVIDED"; Valid.Invalid)
      | DP.Loc -> Valid.Invalid
      | DP.Num -> let module Num = (val (NumSolver.choose BackendSolvers.Yices.identifier)) in
                  Num.compute_model true;
                  let sol = Num.check_valid (NumInterface.formula_to_int_formula phi) in
                  if not (Valid.is_valid sol) then Num.print_model();
                  sol
      | DP.Pairs -> let module Pairs = (val (PairsSolver.choose BackendSolvers.Yices.identifier)) in
                    Pairs.compute_model true;
                    let sol = Pairs.check_valid (PairsInterface.formula_to_pairs_formula phi) in
                    if not (Valid.is_valid sol) then Pairs.print_model();
                    sol
      | DP.Tll -> let module Tll = (val (TllSolver.choose BackendSolvers.Z3.identifier)) in
                  Tll.compute_model true;
                  let tll_phi = TLLInterface.formula_to_tll_formula phi in
                  let sol = Tll.check_valid opt tll_phi in
                  if not (Valid.is_valid sol) then Tll.print_model();
                  sol
      | DP.Tslk k -> let module Tslk = (val (TslkSolver.choose BackendSolvers.Z3.identifier k)) in
                     let module TSLKIntf = TSLKInterface.Make(Tslk.TslkExp) in
                     Tslk.compute_model true;
                     let tslk_phi = TSLKIntf.formula_to_tslk_formula phi in
                     let sol = Tslk.check_valid opt tslk_phi in
                     if not (Valid.is_valid sol) then Tslk.print_model();
                     sol
      | DP.Tsl -> let tsl_phi = TSLInterface.formula_to_tsl_formula phi in
                  TslSolver.compute_model true;
                  let sol = TslSolver.check_valid opt tsl_phi in
                  if not (Valid.is_valid sol) then TslSolver.print_model();
                  sol
      | DP.Thm -> let thm_phi = THMInterface.formula_to_thm_formula phi in
                  ThmSolver.compute_model true;
                  let sol = ThmSolver.check_valid opt thm_phi in
                  if not (Valid.is_valid sol) then TslSolver.print_model();
                  sol
    in
      if Valid.is_valid sol then
        print_endline "VALID"
      else
        print_endline "NOT VALID"
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
