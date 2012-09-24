open ExpressionTypes

module type BackendCommon =
(** Minimum signature for a Backend Solver. *)
sig
  type t
  (** Type for internal data structures. *)
  
  val identifier : string
  (** Unique identifier for this solver. *)

  val reset : unit -> unit
  (** [reset ()] restores to default the configuration register. *)
  
  val reset_calls : unit -> unit
  (** [reset_calls ()] resets the calls counter to [0]. *)
  
  val calls_count : unit -> int
  (** [calls_count ()] returns the number of calls performed to the Solver. *)
  
  val sat   : t -> bool
  (** Tests whether the formula is satisfiable or not. *)
  
  val unsat : t -> bool
  (** [unsat formula] returns [not(sat formula)]. *)
  
  val set_prog_lines : int -> unit
  (** [set_prog_lines n] sets the number of lines of the analyzed 
      program to [n]. *)

  val prog_lines : unit -> int
  (** [prog_lines ()] returns the number of lines of the program 
      being analyzed. *)

  val compute_model : bool -> unit
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)

  val get_model : unit -> GenericModel.t
  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
end




module type PosBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support Position Reasoning. *)
sig
  type t
  
  module Pos : 
  (** Translation of Pos expressions. *)
  sig
    module Exp : POSEXP
    
    val expression : Exp.expression -> t
    (** [expression exp] translates the expression [exp] into its 
        corresponding data structure in the Solver program. *)
  end
end




module type TllBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support TLL. *)
sig
  type t
  
  module Tll :
  (** Translation of TLL expressions. *)
  sig  
    module Exp : TLLEXP
    module Smp : sig
      type cutoff_strategy
      type cutoff_options_t
    end
    
    val literal_list : Exp.literal list -> t
    (** [literal_list ls] translates the list [ls] of literals into its 
        internal representation. *)
    
    val formula      : Tactics.solve_tactic_t option ->
                       Smp.cutoff_strategy ->
                       Smp.cutoff_options_t ->
                       Exp.formula -> t
    (** [formula stat strat copt f] translates the formula [f] following the
        strategy [strat] to compute the SMP cutoff and tactic [stat] to
        decide whether or not to include extra information to help the
        future satisfiability analysis of the formula. When computing the SMP
        it considers the options passes in [copt]. *)
        
    val conjformula  : Exp.conjunctive_formula -> t
    (** [conjformula f] tranlates the conjunctive formula [f]. *)

    val sort_map : unit -> GenericModel.sort_map_t
    (** [sort_map ()] returns the sort mapping obtained from the last
        call to a formula translation *)
  end
end



(*
module type TslkBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support TLL. *)
sig
  type t
  
  module Tslk :
  (** Translation of TLL expressions. *)
  sig
    module Exp : TSLKEXP
    module Smp : sig
      type cutoff_strategy
      type cutoff_options_t
    end


    val literal_list : Exp.literal list -> t
    (** [literal_list ls] translates the list [ls] of literals into its
        internal representation. *)
    
    val formula      : Tactics.solve_tactic_t option ->
                       Smp.cutoff_strategy ->
                       Smp.cutoff_options_t ->
                       Exp.formula -> t
    (** [formula stat strat copt f] translates the formula [f] following the
        strategy [strat] to compute the SMP cutoff and tactic [stat] to
        decide whether or not to include extra information to help the
        future satisfiability analysis of the formula. When computing the SMP
        it considers the options passes in [copt]. *)
        
    val conjformula  : Exp.conjunctive_formula -> t
    (** [conjformula f] tranlates the conjunctive formula [f]. *)

    val sort_map : unit -> GenericModel.sort_map_t
    (** [sort_map ()] returns the sort mapping obtained from the last
        call to a formula translation *)

  end
end
*)




module type NumBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support Numeric Reasoning. *)
sig
  type t
  
  module Num :
  (** Translation of numeric expressions. *)
  sig
    module Exp : NUMEXP
    
    val int_varlist  : Exp.variable list -> t
    (** [int_varlist vs] tranlates the list [vs] of integer variables
        into its corresponding internal representation. *)
    
    val formula      : Exp.formula -> t
    (** Tranlation of a numeric formula into its related data structure. *)
    
    val literal      : Exp.literal -> t
    (** Translation of a literal into an internal representation. *)
    
    val int_formula  : Exp.formula -> t
    (** [int_formula f] translates the integer formula [f]. *)
    
    val int_formula_with_lines 
                     : Exp.formula -> int -> t
    (** [int_formula_with_lines f n] translate the integer formula [f] 
        taking into account the number of lines [n]. *)
    
    val std_widening : Exp.variable list -> Exp.formula 
                         -> Exp.literal -> t
    (** [std_widening vars f l] constructs an internal representation of 
        a standard widening. *)
  end
end




module type CUSTOM_BACKEND_SOLVER = 
(** Signature of a full backend solver. *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
        
    include PosBackend  with type t := t
    include TllBackend  with type t := t
    include NumBackend  with type t := t
(*    include TslkBackend with type t := t*)
  end
end

module type BACKEND_SOLVER = CUSTOM_BACKEND_SOLVER
  with module Translate.Pos.Exp  = PosExpression
  and  module Translate.Tll.Exp  = TllExpression
  and  module Translate.Tll.Smp  = SmpTll
  and  module Translate.Num.Exp  = NumExpression
(*  and  module Translate.Tslk.Exp = TSLKExpression
  and  module Translate.Tslk.Smp = SmpTslk
*)




module type CUSTOM_BACKEND_POS =
(** Signature of solver that supports position reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include PosBackend with type t := t  
  end
end

module type BACKEND_POS = CUSTOM_BACKEND_POS
  with module Translate.Pos.Exp = PosExpression




module type CUSTOM_BACKEND_TLL =
(** Signature of solver that supports TLL reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include TllBackend with type t := t  
  end
end

module type BACKEND_TLL = CUSTOM_BACKEND_TLL
  with module Translate.Tll.Exp = TllExpression
  and  module Translate.Tll.Smp = SmpTll



(*
module type CUSTOM_BACKEND_TSLK =
(** Signature of solver that supports TSLK reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include TslkBackend with type t := t
  end
end

module type BACKEND_TSLK = CUSTOM_BACKEND_TSLK
  with module Translate.Tslk.Exp = TSLKExpression
  and  module Translate.Tslk.Smp = SmpTslk
*)


module type CUSTOM_BACKEND_NUM =
(** Signature of solver that supports numeric reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include NumBackend with type t := t  
  end
end

module type BACKEND_NUM = CUSTOM_BACKEND_NUM
  with module Translate.Num.Exp = NumExpression
