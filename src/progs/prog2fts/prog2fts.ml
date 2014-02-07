open Printf

open LeapLib
open Global


module Expr = Expression

(* This code should be changed in the future *)
module Pos  = (val PosSolver.choose  "default" : PosSolver.S)
module Tll  = (val TllSolver.choose  "default" : TllSolver.S)
module Tslk = (val TslkSolver.choose "default" 1 : TslkSolver.S)
module Num  = (val NumSolver.choose  "default" : NumSolver.S)
module VCG  = VCGen.Make(Pos)(Tll)(Tslk)(Num)
(* This code should be changed in the future *)


(****************)
(* main         *)
(****************)

let _ =
  try let _ = P2FArgs.parse_args () in
    let ch = P2FArgs.open_input () in
    let (sys,undefTids) = Parser.parse ch (StmParser.system StmLexer.norm) in
(*
    let sys = System.set_threads tmp_sys 1 in
*)
    P2FArgs.close_input ();

    (* Shows the parsed system *)
    Report.report_system sys;

    (* Show label information if required *)
    if (!P2FArgs.show_label_info) then
      Report.report_labels (System.get_labels sys);
    
    if (!P2FArgs.show_fts) then begin
      let simple_mode = System.SOpenArray [Expr.build_var_tid "i"]in
      printf "-------------- FTS ---------------------------------\n";
      printf "*** Global variables ***\n%s\n"
                (String.concat ", " $
                  System.get_var_id_list (System.get_global sys));
      printf "*** Local variables ***\n%s\n"
                (System.proc_table_vars_to_str (System.get_procs sys));
      printf "*** Initial condition ***\n%s\n"
                (Expr.formula_to_str $ VCG.gen_theta simple_mode sys);
      printf "*** Transitions ***\n%s\n"
                (VCG.all_transitions_to_str sys);
      printf "-------------- FTS ---------------------------------\n";
    end
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" 
          (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
