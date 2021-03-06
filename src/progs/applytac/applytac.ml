
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


open LeapLib

module Eparser = ExprParser
module Elexer  = ExprLexer
module F = Formula
module SolOpt = SolverOptions


(****************)
(* main         *)
(****************)

let _ =
  try
    ApplyTacArgs.parse_args ();

    if !ApplyTacArgs.verbose then LeapVerbose.enable_verbose();
    let ch = ApplyTacArgs.open_input () in



    let original_implications =
      if ApplyTacArgs.is_vc_file () then begin
        (* Here goes the code for vc_info *)
        let vc_info = Parser.parse ch (Eparser.vc_info Elexer.norm) in
        print_endline ("ORIGINAL VC INFO:\n\n" ^ Tactics.vc_info_to_str vc_info);

        let split_vc_info_list = Tactics.apply_support_split_tactics
                                  [vc_info] !ApplyTacArgs.supp_split_tac_list in
        Tactics.apply_support_tactic split_vc_info_list !ApplyTacArgs.supp_tac
      end else begin
        let phi = Parser.parse ch (Eparser.single_formula Elexer.norm) in
        print_endline ("FORMULA:\n" ^ (Expression.formula_to_str phi) ^ "\n");
        (* We construct the phi implication *)
  let rec faux f = 
      match f with
        F.Implies (a,b) -> "IMPLIES(" ^  (faux a) ^ "," ^ (faux b) ^ ")"
      | F.And(a,b)      -> "AND(" ^ (faux a) ^ "," ^ (faux b) ^ ")"
      | F.Or(a,b)       ->  "OR(" ^ (faux a) ^ "," ^ (faux b) ^ ")"
      | _ ->  "OTHER" 
  in
  let _ = 
    if false then (* DEBUG *)
      print_endline (faux phi) 
  in
  let (ante, conse) = match phi with
    | F.Implies (a,b) -> (a,b)
    | _ -> (F.True, phi) in
  let phi_implication = { Tactics.ante = ante; Tactics.conseq = conse; }
  in
  [phi_implication]
      end in
    ApplyTacArgs.close_input ();
    let split_implications = Tactics.apply_formula_split_tactics
      original_implications
      !ApplyTacArgs.formula_split_tac_list in
    let final_implications = Tactics.apply_formula_tactics
      split_implications
      !ApplyTacArgs.formula_tac_list in

    (* Convert implications to formulas *)
    let final_formulas = List.map (fun imp ->
                           F.Implies (imp.Tactics.ante, imp.Tactics.conseq)
                         ) final_implications in

    (* Output *)
    if !ApplyTacArgs.outfile <> "" then begin
      let i = ref 1 in
      (* Print files *)
      List.iter (fun phi ->
        let file_name = !ApplyTacArgs.outfile ^ "_" ^ (string_of_int !i) in
        let out = open_out_gen [Open_creat;Open_trunc;Open_wronly] 0o666 file_name in
        output_string out (Expression.formula_to_human_str phi);
        close_out out;
        incr i
      ) final_formulas
    end;

    print_endline "=============================\nRESULTS:";

    print_endline (String.concat "\n----------------------------\n"
      (List.map Expression.formula_to_human_str final_formulas));


    (* Apply decision procedures if activated *)
    if !ApplyTacArgs.tllEnable then
      begin
        let tllSolver : (module TllSolver.S) = TllSolver.choose "Z3" in
        let module Tll = (val tllSolver) in
        Tll.compute_model true;
        print_endline "Calling the TLL solver...";
        List.iter (fun phi ->
          print_endline (Expression.formula_to_str phi);
          let tll_phi = TLLInterface.formula_to_tll_formula phi in
          let opt = SolOpt.new_opt () in
          SolOpt.set_cutoff_strategy opt (!ApplyTacArgs.coType);
          let result = Valid.is_valid (Tll.check_valid opt tll_phi) in
          if result then print_endline "VALID" else print_endline "NOT VALID"
        ) final_formulas
      end;
    ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        Printf.sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()

