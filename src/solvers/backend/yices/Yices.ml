open BackendSolverIntf
open NumQuery
open TllQuery

module Yices : BACKEND_SOLVER =
struct
  type t = string
  
  (** Unique identifier *)
  let identifier = "Yices"
  

  (** the configuration register *)
  let config = SMTExecute.new_configuration SMTExecute.Yices
  

  (** [reset_calls ()] resets the calls counter to [0]. *)
  let reset_calls () : unit =
    SMTExecute.reset_calls config

  
  (** [calls_count ()] returns the number of calls performed to the SMT. *)
  let calls_count () : int =
    SMTExecute.calls_count config


  (** [calls_force_incr ()] forces to increment by one the number of calls
      performed by the SMT. *)
  let calls_force_incr () : unit =
    SMTExecute.calls_force_incr config

 
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)
  let compute_model (b:bool) : unit =
    SMTExecute.compute_model config b

  
  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
  let get_model () : GenericModel.t =
    SMTExecute.get_model ()
  
  
  (* RUNING YICES *)
  (** [sat formula] returns [true] whenever the [formula] is satisfiable, 
      [false] otherwise. *)
  let sat (query:t) : bool =
    SMTExecute.run config query

  
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
      module Query = functor (Q : TLL_QUERY) ->
      struct
        let set_prog_lines = Q.set_prog_lines
        let literal_list   = Q.literal_list_to_str
        let formula        = Q.formula_to_str
        let conjformula    = Q.conjformula_to_str
        let sort_map       = Q.get_sort_map
      end
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
      module Query = functor (Q : NUM_QUERY) ->
      struct
        let set_prog_lines         = Q.set_prog_lines
        let int_varlist            = Q.int_varlist_to_str
        let formula                = Q.string_of_formula
        let literal                = Q.string_of_literal
        let int_formula            = Q.int_formula_to_str
        let int_formula_with_lines = Q.int_formula_with_lines_to_str
        let std_widening           = Q.standard_widening
        let sort_map               = Q.get_sort_map
      end
    end
  end
end
