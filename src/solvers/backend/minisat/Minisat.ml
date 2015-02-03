
open LeapLib
open MinisatBackendType

module Minisat : BACKEND_POS =
struct
  type t = string

  type configuration = {
    calls              : counter;(** number of calls performed. *)
    mutable exec       : string; (** path to executable. *)
    mutable comp_model : bool;   (** compute model for non valid VCs *)
  }


  (** Unique identifier *)
  let identifier = "Minisat"

  (** the configuration register *)
  let config : configuration = {
    calls      = new counter 0;
(*    exec       = Config.get_exec_path() ^ "/tools/minisat -verb=0 "; *)
    exec       = "minisat -verb=0 ";
    comp_model = false;
  }

  (** [reset ()] restores to default the configuration register. *)
  let reset () = 
  begin
    config.calls # reset;
(*    config.exec       <- Config.get_exec_path() ^ "tools/minisat -verb=0 "; *)
    config.exec       <- "minisat -verb=0 ";
    config.comp_model <- false;
  end

  (** [reset_calls ()] resets the calls counter to [0]. *)
  let reset_calls () = config.calls # reset
  
  (** [calls_count ()] returns the number of calls performed to the SMT. *) 
  let calls_count () = config.calls # get

  (** [calls_force_incr ()] forces to increment by one the number of calls
      performed by the SMT. *)
  let calls_force_incr () : unit = config.calls # incr
  
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)
  let compute_model (b:bool) : unit = config.comp_model <- b

  (** The model of the last parsed query *)
  let model : GenericModel.t ref = ref (GenericModel.new_model())

  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
  let get_model () : GenericModel.t =
    !model
  
    
  (* RUNING MINISAT *)

  let parse_minisat_output (from_minisat:Pervasives.in_channel) : Sat.t =
    let last_line = ref "" in
    let answer_str = try
                       while true do
                         last_line := Pervasives.input_line from_minisat
                       done; ""
                     with End_of_file -> !last_line in
    let (terminated, outcome) =
      match answer_str with
        "UNSATISFIABLE" -> let _ = Debug.print_smt "unsat\n"
                           in
                             (true, Sat.Unsat)
      | "SATISFIABLE"   -> let _ = Debug.print_smt "sat\n"
                           in
                             (true, Sat.Sat)
      | _               -> (false, Sat.Unknown)
    in
      outcome


  (** [sat formula] returns [true] whenever the [formula] is satisfiable, 
      [false] otherwise. *)
  let check_sat (query:string) : Sat.t =
    (* 1. write query to temp file *)
    let temp      = Filename.temp_file "leap_" ".sat" in
    let _         = Debug.print_file_name "SAT Formula" temp in
    let output_ch = open_out temp in

    let _ = output_string output_ch query ; close_out output_ch in
    let run_minisat _ =
      let _ = Debug.print_smt "Invoking minisat... " in
      let minisat_cmd  = config.exec ^ temp in
      let env = Array.of_list [] in
      let (from_minisat,to_minisat,stderr) = Unix.open_process_full
                                               minisat_cmd env in
      let response = parse_minisat_output from_minisat in
      let _ = Debug.print_smt_result response in
      let _ = Unix.close_process_full (from_minisat,to_minisat,stderr)
      in
        response
    in
      run_minisat ()

(*
  (** [unsat formula] returns [not(sat formula)]. *)
  let unsat (query:string) : Sat.t =
    Sat.alternate (sat query)
*)


  module Translate =
  struct
    module Pos =
    struct
      module Exp = PosExpression

      let set_prog_lines = MiniPosQuery.set_prog_lines
      let expression     = MiniPosQuery.pos_expression_to_str
    end
  end
end
