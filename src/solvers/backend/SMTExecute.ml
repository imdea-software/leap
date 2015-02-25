open LeapLib
open LeapVerbose

type smt_t = Yices | Z3 | CVC4

exception SMT_Syntax_Error of string
exception SMT_Timeout of string * int
exception SMT_Not_Found of string

(* SMT Solver dependent information *)

let get_exec_cmd (smt:smt_t) : string =
  begin
    match smt with
    | Yices -> "yices"
    | Z3 -> "z3"
    | CVC4 -> "cvc4"
  end
(*
  Config.get_exec_path() ^
  begin
    match smt with
    | Yices -> "/tools/yices"
    | Z3    -> "/tools/z3"
    | CVC4  -> "/tools/cvc4"
  end
*)

let check_installed (smts:smt_t list) : unit =
  let check_smt (smt:smt_t) : unit =
    let cmd = get_exec_cmd smt in
    let env = Array.of_list [] in
    let check_method = " -?" in
    let (stdout,stdin,stderr) = Unix.open_process_full (cmd ^ check_method) env in
    print_endline (cmd ^ check_method);
    try
      ignore (Pervasives.input_line stderr);
      raise(SMT_Not_Found cmd)
    with End_of_file -> ignore (Unix.close_process_full (stdout,stdin,stderr));
  in
    List.iter check_smt smts


let get_extension (smt:smt_t) : string =
  match smt with
  | Yices -> ".ys"
  | Z3    -> ".smt2"
  | CVC4  -> ".smt2"


let get_modelparser (smt:smt_t) : Lexing.lexbuf -> GenericModel.t =
  match smt with
  | Yices -> (YicesModelParser.generic_model YicesModelLexer.norm)
  | Z3    -> (Z3ModelParser.generic_model Z3ModelLexer.norm)
  | CVC4  -> (Z3ModelParser.generic_model Z3ModelLexer.norm)


let get_prequery (smt:smt_t) : string =
  match smt with
  | Yices -> "(set-evidence! true)\n"
  | Z3    -> "(set-option :produce-assignments true)\n"
  | CVC4  -> "(set-option :produce-assignments true)\n"


let get_postquery (smt:smt_t) : string =
  match smt with
  | Yices -> ""
  | Z3    -> "\n(get-model)\n"
  | CVC4  -> ""



(* Configuration management *)

type configuration_t = {
  smt                : smt_t;   (** SMT kind *)
  calls              : counter; (** number of calls performed. *)
  exec               : string;  (** path to executable. *)
  extension          : string;  (** temporary file extension *)
  timeout            : int;     (** execution timeout (in secs). *)
  mutable comp_model : bool;    (** compute a model for non valid VCs *)
  model_parser       : Lexing.lexbuf -> GenericModel.t;
                                (** generic model parser *)
  prequery           : string;  (** extra information to precede a query *)
  postquery          : string;  (** extra information to follow a query *)
}


let new_configuration (smt:smt_t) : configuration_t =
  {
    smt           = smt;
    calls         = new counter 0;
    exec          = get_exec_cmd smt;
    extension     = get_extension smt;
    timeout       = 9000 (*1800*) (*3600*) (*1800*);
    comp_model    = false;
    model_parser  = get_modelparser smt;
    prequery      = get_prequery smt;
    postquery     = get_postquery smt;
  }
    
let reset_calls (cfg:configuration_t) : unit =
  cfg.calls # reset

let calls_count (cfg:configuration_t) : int =
  cfg.calls # get

let calls_force_incr (cfg:configuration_t) : unit =
  cfg.calls # incr

let compute_model (cfg:configuration_t) (b:bool) : unit =
  cfg.comp_model <- b

let gen_timeout_str (cfg:configuration_t) : string =
  match cfg.smt with
  | Yices -> " -tc "
  | Z3    -> Printf.sprintf " -T:%i " cfg.timeout
  | CVC4  -> " "

let gen_debugsupp_str (cfg:configuration_t) : string =
  if !Debug._debug_ then
    match cfg.smt with
    | Yices -> " -tc "
    | Z3    -> ""
    | CVC4  -> ""
  else
    ""


(** The model of the last parsed query *)
let model : GenericModel.t ref = ref (GenericModel.new_model())

let get_model () : GenericModel.t =
  !model


(* Running the SMT solver *)
let parse_output (ch:Pervasives.in_channel) : (bool * Sat.t) =
  let answer_str = Pervasives.input_line ch in
  verbl _LONG_INFO "**** SMTExecute answer: %s\n" answer_str;
  let (terminated, outcome) =
    match answer_str with
    | "unsat"   -> (Debug.print_smt "unsat\n"; (true, Sat.Unsat))
    | "sat"     -> (Debug.print_smt "sat\n"; (true, Sat.Sat))
    | "unknown" -> (Debug.print_smt "unknown\n"; (true, Sat.Unknown))
    | "timeout" -> (Debug.print_smt "timeout\n"; (false,Sat.Unknown))
    | _         -> (false, Sat.Unknown)
  in
    (terminated, outcome)


let run (cfg:configuration_t) (query:string) : Sat.t =
  (* 1. write query to temp file *)
(*  LOG "Entering run..." LEVEL TRACE; *)
  
  let tmpfile = Filename.temp_file "leap_" cfg.extension in
  Debug.print_file_name "VC" tmpfile;
  let full_query = if cfg.comp_model then
                     (cfg.prequery ^ query ^ cfg.postquery)
                   else
                     query in
  let output_ch = open_out tmpfile in
  output_string output_ch full_query;
  close_out output_ch;
  (* 2. run SMT and parse output *)
(*
  let cmd = cfg.exec ^ (gen_timeout_str cfg)   ^
                       (gen_debugsupp_str cfg) ^
                       (tmpfile)               ^
                       (" CASE_SPLIT=4 ") in
*)
  let cmd = cfg.exec ^ (gen_timeout_str cfg)   ^
                       (gen_debugsupp_str cfg) ^
                       (tmpfile) in

  let env = Array.of_list [] in
  let (stdout,stdin,stderr) = Unix.open_process_full cmd env in
  verbl _LONG_INFO "**** STMExecute will parse output.\n";
  let (terminated,response) = parse_output stdout in
  verbl _LONG_INFO "**** SMTExecute, response read.\n";
  if (not terminated) then begin
    if Sat.is_unknown response then begin
      Interface.Err.msg "Timeout query" $
        Printf.sprintf "File %s contains a query that timeout after %i seconds." tmpfile cfg.timeout;
      raise(SMT_Timeout(tmpfile,cfg.timeout))
    end else begin
      Interface.Err.msg "Malformed query" $
        Printf.sprintf "File %s contains an invalid query." tmpfile;
      raise(SMT_Syntax_Error tmpfile)
    end
  end;
  if cfg.comp_model then begin
    if Sat.is_sat response then begin
      verbl _LONG_INFO "**** SMTExecute, response with model obtained.\n";
      let buf = Buffer.create 1024 in
      let _ = try
                while true do
                  let line = Pervasives.input_line stdout in
                  let exp = Str.regexp (";;[^\n]*") in
                  let conv = Str.global_replace exp "" line
                  in
                    Buffer.add_string buf conv
                done
              with _ -> () in
(*      if cfg.smt <> Yices then Debug.force_print_file_name "VC" tmpfile; *)
      model := cfg.model_parser (Lexing.from_string (Buffer.contents buf));
    end else begin
      verbl _LONG_INFO "**** SMTExecute, no response with model obtained.\n";
      GenericModel.clear_model !model
    end
  end;
  let _ = Unix.close_process_full (stdout,stdin,stderr) in
  cfg.calls # incr;
  verbl _LONG_INFO "**** SMTExecute, will print results.\n";
  Debug.print_smt_result response;
  if terminated then
    response
  else
    Sat.Unknown
