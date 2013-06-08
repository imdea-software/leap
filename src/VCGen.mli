
type valid_t = Unverified | NotValid | CheckedLocation | Checked | Unneeded
        
module type S =
sig 
  type rhoMode
  
  type formula_table_t
  
  type vc_info_t = {
                     pc   : Expression.pc_t               ;
                     smp  : Smp.cutoff_strategy_t         ;
                     stac : Tactics.solve_tactic option   ;
                     mutable supps : Tag.f_tag list       ;
                     try_pos : bool                       ;
                   }
  
  type dp_info

  (*
  type solver_info 
    {
      prog_lines : int ;
      dp         : dp_info ;
      cutoff     : cutoff_type ;
      out_file   : string ;
      focus      : Expression.pc_t list;
      hide_pres  : bool ;
      count_abs  : bool ;
    }
  *)
  
  val cutoff : unit -> Smp.cutoff_strategy_t
  val out_file : unit -> string
  val hide_pres : unit -> bool
  val tactics : unit -> Tactics.proof_plan
  
  val decl_tag : Tag.f_tag option -> Expression.formula -> unit
  val read_tag : Tag.f_tag -> Expression.formula option
  val is_def_tag : Tag.f_tag -> bool
  val tags_num : unit -> int
  
  
  (** Decision procedure *)
  val none_dp : unit -> dp_info
  val enable_num_dp  : unit -> unit
  val enable_tll_dp  : unit -> unit
  val enable_tsl_dp  : unit -> unit
  val enable_tslk_dp : int  -> unit
  val enable_dp      : DP.t -> unit (** Available options: "num", "tll".  *)
  val some_dp_enabled : unit -> bool
  val apply_pos_dp  : unit -> bool
  val apply_num_dp  : unit -> bool
  val apply_tll_dp  : unit -> bool
  val apply_tsl_dp  : unit -> bool
  val apply_tslk_dp : unit -> (bool * int)
  
  
  
  (** Solver information functions *)
  (* val new_solver_info : int  *)
  (*   -> cutoff_type           *)
  (*   -> string                *)
  (*   -> Expression.pc_t list  *)
  (*   -> bool                  *)
  (*   -> bool                  *)
  (*   -> solver_info           *)
  val initialize : int       (** Number of lines in the program. *)
    -> Smp.cutoff_strategy_t   (** Cutoff strategy to follow. *)
    -> string                (** Output file. *)
    -> Expression.pc_t list  (** Program lines where the VCGen focuses.*)
    -> bool                  (** Hide unmodified variables. *)
    -> bool                  (** Enable counting abstraction. *)
    -> unit

  val set_detFolder : string -> unit

  val set_detProbName : string -> unit

  val set_detFileName : string -> unit
  
  val set_cases : (Expression.pc_t * IGraph.premise_t, 
       Expression.formula list * Tactics.proof_plan) Hashtbl.t 
    -> unit
  
  val set_tactics : Tactics.proof_plan -> unit
 
  (** Transition relation generation *)
  val gen_rho : rhoMode
    -> bool 
    -> bool 
    -> System.system_t 
    -> Expression.tid list 
    -> Expression.pc_t 
    -> Expression.formula list
  
  val gen_all_transitions : System.system_t 
    -> (Expression.pc_t * Expression.formula list) list
  
  val all_transitions_to_str : System.system_t -> string
  
  (* Theta *)
  
  val gen_global_init_cond : System.system_t 
    -> Expression.formula list
  
  val gen_local_init_cond : System.system_t 
    -> string 
    -> Expression.formula list
  
  val gen_init_cond : System.system_t 
    -> string 
    -> Expression.tid list 
    -> bool 
    -> Expression.formula
    
  val gen_theta : System.sysMode 
    -> System.system_t 
    -> Expression.formula
  
  
  (** B-INV for a closed system *)
  val binv : System.system_t 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list
  
  
  val pinv : System.system_t 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list
  
  
  (** P-INV+ for an open system *)
  val pinv_plus : System.system_t 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list
  
  
  (** SP-INV for an open system *)
  val spinv : System.system_t 
    -> Expression.formula list 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list


  (** Sequential B-INV *)
  val seq_binv : System.system_t
    -> Expression.formula
    -> (Expression.formula * vc_info_t) list


  val seq_spinv : System.system_t
    -> Expression.formula list
    -> Expression.formula
    -> (Expression.formula * vc_info_t) list


  val check_with_pinv : System.system_t 
    -> Expression.formula
    (*-> solver_info*)
    -> bool
  
  val check_with_pinv_plus : System.system_t 
    -> Expression.formula 
    (*-> solver_info*)
    -> bool
  
  val check_with_spinv : System.system_t
    -> Expression.formula list
    -> Expression.formula
    (*-> solver_info*)
    ->bool


  val check_with_seq_binv : System.system_t
    -> Expression.formula
    -> bool


  val check_with_seq_spinv : System.system_t
    -> Expression.formula list
    -> Expression.formula
    (*-> solver_info*)
    ->bool


  val check_with_graph : System.system_t 
    -> IGraph.iGraph_t 
    -> bool
  
  (** Formula table update functions *)
  val support_formula_table : Expression.formula list 
    -> formula_table_t 
    -> formula_table_t
  
  
  (** Decision procedure functions *)
  val filter_system : System.system_t 
    -> System.system_t
  
  val clean_formula : Expression.formula 
    -> Expression.formula
  
  
  val apply_dp_on_table : formula_table_t 
    (* -> solver_info  *)
    -> string 
    -> bool
  
  val apply_dp_on_list : (Expression.formula * vc_info_t) list 
    (* -> solver_info  *)
    -> string 
    -> bool
  
  val formula_list_to_table : (Expression.formula * vc_info_t) list 
    -> formula_table_t
end

module Make : 
  functor (PS : PosSolver.S) -> 
    functor (TS : TllSolver.S) ->
      functor (TKS : TslkSolver.S) ->
        functor (NS : NumSolver.S) -> S
