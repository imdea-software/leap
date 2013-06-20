open Printf

open LeapLib
open Global


module Expr = Expression


(****************)
(* main         *)
(****************)

let _ =
  try let _ = PrgInfoArgs.parse_args () in
    let ch = PrgInfoArgs.open_input () in
    let (sys,undefTids) = Parser.parse ch (Stmparser.system Stmlexer.norm) in
(*
    let sys = System.set_threads tmp_sys 1 in
*)
    PrgInfoArgs.close_input ();

    (* Shows the parsed system *)
    Report.report_system sys;

    (* Show label information if required *)
    if (!PrgInfoArgs.show_label_info) then
      Report.report_labels (System.get_labels sys);
    
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" 
          (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
