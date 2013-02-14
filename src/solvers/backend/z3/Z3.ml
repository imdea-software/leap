open Genlex
open Debug
open LeapLib
open LeapVerbose
open Z3BackendType

module Z3 : BACKEND_POS_TLL_TSLK =
struct
  type t = string
  
  type configuration = {
    calls              : counter; (** number of calls performed. *)
    mutable exec       : string;  (** path to executable. *)
    mutable timeout    : int;     (** execution timeout (in secs). *)
    mutable comp_model : bool;    (** computes a model for non valid VCs *)
  }
  
  (** Unique identifier *)
  let identifier = "Z3"
  
  (** the configuration register *)
  let config : configuration = {
    calls      = new counter 0;
    exec       = Config.get_exec_path() ^ "/tools/z3 -m";
    timeout    = 3600; (* one hour *)
    comp_model = false;
  }

  let z3_evidence = "\n(get-model)\n"
  
  (** [reset ()] restores to default the configuration register. *)
  let reset () = 
  begin
    config.calls # reset;
    config.exec       <- Config.get_exec_path() ^ "/tools/z3 -m";
    config.timeout    <- 3600;
    config.comp_model <- false;
  end
  
  (** [reset_calls ()] resets the calls counter to [0]. *)
  let reset_calls () = config.calls # reset
  
  (** [calls_count ()] returns the number of calls performed to the SMT. *) 
  let calls_count () = config.calls # get
  
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)
  let compute_model (b:bool) : unit = config.comp_model <- b

  (** The model of the last parsed query *)
  let model : GenericModel.t ref = ref (GenericModel.new_model())
  
  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
  let get_model () : GenericModel.t =
    !model
  
    
  (* RUNING Z3 *)
  
  let parse_z3_output (from_z3:Pervasives.in_channel) : bool =
    let answer_str = Pervasives.input_line from_z3 in
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
      outcome

  (** [sat formula] returns [true] whenever the [formula] is satisfiable, 
      [false] otherwise. *)
  let sat (query:string) : bool =
    (* 1. write query to temp file *)
    let temp      = Filename.temp_file "leap_" ".smt2" in
    let _         = Debug.print_file_name "VC" temp in
    let full_query = if config.comp_model then
                       query ^ z3_evidence
                     else
                       query in
    let output_ch = open_out temp in
    let _ = output_string output_ch full_query ; close_out output_ch in
    (* 2. run z3 and parse output *)
    let run_z3 _ =
      let _ = Debug.print_smt "Invoking z3... " in
      let z3_cmd  = config.exec ^ " -t:" ^ (string_of_int config.timeout)
                      ^ " " ^ temp ^ " CASE_SPLIT=4 " in
      let env = Array.of_list [] in
      let (from_z3,to_z3,stderr) = Unix.open_process_full z3_cmd env in
			verb "**** Z3, will parse Z3 output.\n";
			let response = parse_z3_output from_z3 in
			verb "**** Z3, response read.\n";
      let _ = if config.comp_model then
                if response then
                  let buf = Buffer.create 1024 in
                  let _ = try
                            while true do
                              let line = Pervasives.input_line from_z3 in
                              let exp = Str.regexp (";;[^\n]*") in
                              let conv = Str.global_replace exp "" line
                              in
                                Buffer.add_string buf conv
                            done
                          with _ -> ()
                  in
                    model := (Z3ModelParser.generic_model Z3ModelLexer.norm)
                                (Lexing.from_string (Buffer.contents buf))
                else
                  GenericModel.clear_model !model
              else
                () in
      let _ = Unix.close_process_full (from_z3,to_z3,stderr) in
			let _ = config.calls # incr in
			verb "**** Z3, will print results.\n";
      let _ = Debug.print_smt_result response in
   (* let _ = Unix.unlink temp in *)
        response
    in
      run_z3 ()
  
  (** [unsat formula] returns [not(sat formula)]. *)
  let unsat (query:string) : bool =
    not (sat query)
  
  module Translate = 
  struct
    module Pos = 
    struct
      module Exp = PosExpression

      let set_prog_lines = Z3PosQuery.set_prog_lines
      let expression = Z3PosQuery.pos_expression_to_str
    end
    
    module Tll =
    struct
      module Exp = TllExpression
      module Smp = SmpTll

      let set_prog_lines = Z3TllQuery.set_prog_lines
      let literal_list   = Z3TllQuery.literal_list_to_str
      let formula        = Z3TllQuery.formula_to_str
      let conjformula    = Z3TllQuery.conjformula_to_str
      let sort_map       = Z3TllQuery.get_sort_map
    end

    module Tslk (K : Level.S) =
    struct
      module Smp     = SmpTslk
      module Z3Query = Z3TslkQuery.Make(K)
      module Exp     = Z3Query.Expr

      let set_prog_lines = Z3Query.set_prog_lines
      let literal_list   = Z3Query.literal_list_to_str
      let formula        = Z3Query.formula_to_str
      let conjformula    = Z3Query.conjformula_to_str
      let sort_map       = Z3Query.get_sort_map
    end

  end
end
