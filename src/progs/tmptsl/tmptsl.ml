open LeapLib

module Eparser = ExprParser
module Elexer  = ExprLexer


(****************)
(* main         *)
(****************)

let _ =
  try
    TmptslArgs.parse_args ();

    if !TmptslArgs.verbose then LeapVerbose.enable_verbose();
    let ch = TmptslArgs.open_input () in
    let (_,phi) = Parser.parse ch
                    (Eparser.single_formula Elexer.norm) in
    TmptslArgs.close_input ();

    (* Parse support files *)
    let supp = List.map (fun file ->
                 snd (Parser.open_and_parse file (Eparser.single_formula Elexer.norm))
               ) !TmptslArgs.support_files in


    print_endline ("FORMULA:\n" ^ (Expression.formula_to_str phi) ^ "\n");
    print_endline "SUPPORT FORMULAS:";
    List.iter (fun psi -> (print_endline (Expression.formula_to_str psi))) supp;
    
    (* Create the proof_plan *)
    let plan = Tactics.new_proof_plan
                (Some !TmptslArgs.coType)
                (!TmptslArgs.solve_tactic)
(*                (!TmptslArgs.supp_split_tac_list) *)
                []
                (!TmptslArgs.supp_tac_list)
(*                (!TmptslArgs.formula_split_tac_list) *)
                []
                (!TmptslArgs.formula_tac_list) in

    ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        Printf.sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()

