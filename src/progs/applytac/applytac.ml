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
        print_endline ("ORIGINAL VC INFO:\n\n" ^ Tactics.vc_info_to_str vc_info);

        (* Parse auxiliary support formulas *)
        let supp_list = List.map (fun file ->
                          snd (Parser.open_and_parse file (Eparser.single_formula Elexer.norm))
                        ) !ApplyTacArgs.support_files in

        print_endline "=============================";
        print_endline ("SUPPORT LOADED FROM EXTERNAL FILES:\n" ^
          (String.concat "\n" (List.map Expression.formula_to_str supp_list)));

        (* To be removed once we have support tactics *)
(*        let final_vc_info_list = [vc_info] in *)

        let split_vc_info_list =
            List.fold_left (fun ps f_name ->
              List.flatten (List.map (Tactics.pick_support_split_tac f_name) ps)
            ) [vc_info] !ApplyTacArgs.supp_split_tac_list in

        let final_vc_info_list =
            List.fold_left (fun ps f_name ->
              List.map (Tactics.pick_support_tac f_name) ps
            ) split_vc_info_list !ApplyTacArgs.supp_tac_list in

        List.map (fun vc ->
          Tactics.vc_info_to_implication vc supp_list
        ) final_vc_info_list
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

    ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        Printf.sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()

