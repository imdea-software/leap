open LeapLib
open LeapVerbose

type smt_t = Yices | Z3 | CVC4


(* SMT Solver dependent information *)

let get_exec_cmd (smt:smt_t) : string =
  Config.get_exec_path() ^
  begin
    match smt with
    | Yices -> "/tools/yices"
    | Z3    -> "/tools/z3"
    | CVC4  -> "/tools/cvc4"
  end


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
  model_parser       : Lexing.lexbuf -> GenericModel.t
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
    timeout       = 3600;
    comp_model    = false;
    model_parser  = get_modelparser smt;
    prequery      = get_prequery smt;
    postquery     = get_postquery smt;
  }
    
let reset_calls (cfg:configuration_t) : unit =
  cfg.calls # reset

let calls_count (cfg:configuration_t) : int =
  cfg.calls # get

let compute_model (cfg:configuration_t) (b:bool) : unit =
  cfg.comp_model <- b

let gen_timeout_str (cfg:configuration_t) : string =
  match cfg.smt with
  | Yices -> " --timeout=" ^ (string_of_int cfg.timeout)
  | Z3    -> " -t:" ^ (string_of_int cfg.timeout)
  | CVC4  -> ""

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
let parse_output (ch:Pervasives.in_channel) : bool =
  let answer_str = Pervasives.input_line ch in
  verb "**** SMTExecute answer: %s\n" answer_str;
  let (terminated, outcome) =
    match answer_str with
      "unsat" -> let _ = Debug.print_smt "unsat\n"
                 in
                   (true, false)
    | "sat"   -> let _ = Debug.print_smt "sat\n"
                 in
                   (true, true)
    | _       -> (false, false)
  in
    (terminated, outcome)


let run (cfg:configuration_t) (query:string) : bool =
  (* 1. write query to temp file *)
  LOG "Entering run..." LEVEL TRACE;
  let tmpfile = Filename.temp_file "leap_" cfg.extension in
  Debug.print_file_name "VC" tmpfile;
  let full_query = if cfg.comp_model then
                     cfg.prequery ^ query ^ cfg.postquery
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
    verb "**** STMExecute will parse output.\n";
    let response = parse_output stdout in
    verb "**** SMTExecute, response read.\n";
    if cfg.comp_model then
      if response then begin
        verb "**** SMTExecute, response with model obtained.\n";
        let buf = Buffer.create 1024 in
        let _ = try
                  while true do
                    let line = Pervasives.input_line from_z3 in
                    let exp = Str.regexp (";;[^\n]*") in
                    let conv = Str.global_replace exp "" line
                    in
                      Buffer.add_string buf conv
                  done
                with _ -> () in
        model := cfg.model_parser (Lexing.from_string (Buffer.contents buf)) end
      else begin
        verb "**** SMTExecute, no response with model obtained.\n";
        GenericModel.clear_model !model
      end
    else
      ();
    Unix.close_process_full (stdout,stdin,stderr);
    cfg.calls # incr;
    verb "**** SMTExecute, will print results.\n";
    Debug.print_smt_result response;
      terminated && response
