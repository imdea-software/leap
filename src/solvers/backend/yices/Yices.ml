open Genlex
open Debug
open LeapLib
open BackendSolverIntf
open YicesNumQuery
open YicesTllQuery

module Yices : BACKEND_SOLVER =
struct
  type t = string
  
  type configuration = {
    calls              : counter;    (** number of calls performed. *)
    mutable exec       : string; (** path to executable. *)
    mutable timeout    : int;    (** execution timeout (in secs). *)
    mutable comp_model : bool; (** compute a model for non valid VCs *)
  }
  
  (** Unique identifier *)
  let identifier = "Yices"
  
  (** the configuration register *)
  let config : configuration = {
    calls      = new counter 0;
    exec       = Config.get_exec_path() ^ "/tools/yices";
    timeout    = 3600; (* one hour *)
    comp_model = false;
  }

  let yices_evidence = "(set-evidence! true)\n"
  
  (** [reset ()] restores to default the configuration register. *)
  let reset () = 
  begin
    (*config.calls # reset;*)
    config.exec       <- Config.get_exec_path() ^ "/tools/yices";
    config.timeout    <- 3600;
    config.comp_model <- false;
  end
  
  (** [reset_calls ()] resets the calls counter to [0]. *)
  let reset_calls () = 
    config.calls # reset
  
  (** [calls_count ()] returns the number of calls performed to the SMT. *) 
  let calls_count () = 
    config.calls # get
  
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)
  let compute_model (b:bool) : unit = config.comp_model <- b

  (** The model of the last parsed query *)
  let model : GenericModel.t ref = ref (GenericModel.new_model())
  
  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
  let get_model () : GenericModel.t =
    !model
  
  
  (* RUNING YICES *)
  
  let parse_yices_output (from_yices:Pervasives.in_channel) : bool =
    let answer_str = Pervasives.input_line from_yices in
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
  let sat (query:t) : bool =
    (* 1. write query to temp file *)
    let temp      = Filename.temp_file "leap_" ".ys" in
    let _         = Debug.print_file_name "VC" temp in
    let output_ch = open_out temp in
    let full_query = if config.comp_model then
                       yices_evidence ^ query
                     else
                       query in
    let _ = output_string output_ch full_query ; close_out output_ch in
    (* l  et _ = Printf.printf "printing in temp file \"%s\"\n" temp in  *)
    (* let _ = Printf.printf "formula: %s\n" query in *)
    (* 2. run yices and parse output *)
    let run_yices _ =
      let _ = Debug.print_smt "Invoking yices... " in
      let yices_type_checking = if !Debug._debug_ then " -tc " else "" in
      let yices_cmd  = config.exec ^ yices_type_checking ^
                        " --timeout=" ^ (string_of_int config.timeout) ^
                        " " ^ temp in
      let env = Array.of_list [] in
      let (from_yices,to_yices,stderr) = Unix.open_process_full yices_cmd env in
      let response = parse_yices_output from_yices in
      let _ = if config.comp_model then
                if response then
                  model := (YicesModelParser.generic_model YicesModelLexer.norm)
                                (Lexing.from_channel from_yices)
                else
                  GenericModel.clear_model !model
              else
                () in
      let _ = Unix.close_process_full (from_yices,to_yices,stderr) in
      let _ = config.calls # incr in
      let _ = Debug.print_smt_result response in
  (*    let _ = Unix.unlink temp in *)
        response
    in
      run_yices ()
  
  (** [unsat formula] returns [not(sat formula)]. *)
  let unsat (query:t) : bool =
    not (sat query)

  
  module Translate = 
  struct
    module Pos = 
    struct
      module Exp = PosExpression
      let set_prog_lines = YicesPosQuery.set_prog_lines
      let expression     = YicesPosQuery.pos_expression_to_str
    end
    
    module Tll =
    struct
      module Exp = TllExpression
      module Smp = SmpTll
      let set_prog_lines = YicesTllQuery.set_prog_lines
      let literal_list   = YicesTllQuery.literal_list_to_str
      let formula        = YicesTllQuery.formula_to_str
      let conjformula    = YicesTllQuery.conjformula_to_str
      let sort_map       = YicesTllQuery.get_sort_map
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

    module Num =
    struct
      module Exp = NumExpression

      let set_prog_lines         = YicesNumQuery.set_prog_lines
      let int_varlist            = YicesNumQuery.int_varlist_to_str
      let formula                = YicesNumQuery.yices_string_of_formula
      let literal                = YicesNumQuery.yices_string_of_literal
      let int_formula            = YicesNumQuery.int_formula_to_str
      let int_formula_with_lines = YicesNumQuery.int_formula_with_lines_to_str
      let std_widening           = YicesNumQuery.standard_widening
      let sort_map               = YicesNumQuery.get_sort_map
    end
  end
end
