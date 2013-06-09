open LeapLib

module Eparser = Exprparser
module Elexer  = Exprlexer


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
        print_endline ("ORIGINAL VC INFO:\n\n" ^ Tactics.vc_info_to_str 
vc_info);

        (* To be removed once we have support tactics *)
(*        let final_vc_info_list = [vc_info] in *)

        let split_vc_info_list =
            List.fold_left (fun ps f_name ->
              List.flatten (List.map (Tactics.pick_support_split_tac f_name) ps)
            ) [vc_info] !ApplyTacArgs.supp_split_tac_list in

        List.map (fun vc ->
          let processed_supp = match !ApplyTacArgs.supp_tac with
                               | None -> Tactics.get_unprocessed_support_from_info vc
                               | Some tac -> (Tactics.pick_support_tac tac) vc in
          Tactics.vc_info_to_implication vc processed_supp
        ) split_vc_info_list
      end else begin
        let (_,phi) = Parser.parse ch (Eparser.single_formula Elexer.norm) in
        print_endline ("FORMULA:\n" ^ (Expression.formula_to_str phi) ^ "\n");
        (* We construct the phi implication *)
        let (ante, conse) = match phi with
                            | Expression.Implies (a,b) -> (a,b)
                            | _ -> (Expression.True, phi) in
        let phi_implication = { Tactics.ante = ante; Tactics.conseq = conse; }
        in
          [phi_implication]
    end in
    ApplyTacArgs.close_input ();



    let split_implications =
        List.fold_left (fun ps f_name ->
          List.flatten (List.map (Tactics.pick_formula_split_tac f_name) ps)
        ) original_implications !ApplyTacArgs.formula_split_tac_list in

    let final_implications =
        List.fold_left (fun ps f_name ->
          List.map (Tactics.pick_formula_tac f_name) ps
        ) split_implications !ApplyTacArgs.formula_tac_list in


    (* Convert implications to formulas *)
    let final_formulas = List.map (fun imp ->
                           Expression.Implies (imp.Tactics.ante, imp.Tactics.conseq)
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
    if !ApplyTacArgs.tslEnable then
      begin
        print_endline "Calling the TSL solver...";
        List.iter (fun phi ->
          print_endline (Expression.formula_to_str phi);
          let tsl_phi = TSLInterface.formula_to_tsl_formula phi in
          let result = TslSolver.is_valid 5 None !ApplyTacArgs.coType tsl_phi in
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

