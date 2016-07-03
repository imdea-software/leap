
type file_kind_t = Inv | Axiom
type proof_info_t
type proof_obligation_t
type solved_proof_obligation_t


module GenOptions :
  sig

    val sys : System.t
    val focus : Expression.pc_t list
    val ignore : Expression.pc_t list
    val abs : System.abstraction
    val hide_pres : bool
    val output_file : string
    val inv_folder : string
    val axiom_file : string
    val axiom_folder : string
    val dp : DP.t
    val pSolver : string
    val tSolver : string
    val compute_model : bool
    val group_vars : bool
    val forget_primed_mem : bool
    val default_cutoff : Smp.cutoff_strategy_t
    val use_quantifiers : bool
    val output_vcs : bool
    val stop_on_invalid : bool
    val arrangement_gen : bool
  end

module type S =
  sig

    exception No_invariant_folder
    exception No_axiom_folder

    val new_proof_info : Smp.cutoff_strategy_t option -> proof_info_t
    val new_proof_obligation : Tactics.vc_info ->
                               Expression.formula list ->
                               proof_info_t ->
                               proof_obligation_t
    val obligations : proof_obligation_t -> Expression.formula list

    val lines_to_consider : int list
    val requires_theta : bool

    val report_vcs : Tactics.vc_info list -> unit

    val decl_tag : file_kind_t -> Tag.f_tag option -> Expression.formula ->
                   System.var_table_t -> unit
    val is_def_tag : Tag.f_tag -> bool
    val read_tag : file_kind_t -> Tag.f_tag -> Expression.formula
    val read_tags_and_group_by_file : file_kind_t -> Tag.f_tag list -> Expression.formula list
    val read_tag_info : file_kind_t -> Tag.f_tag -> Tag.f_info

    val system : System.t

    val theta : Expression.ThreadSet.t -> (Expression.formula * Expression.ThreadSet.t)
    val rho : System.seq_or_conc_t ->
              Expression.ThreadSet.t ->
              int ->
              Expression.ThreadSet.elt ->
              Expression.formula list

    val solve_proof_obligations : proof_obligation_t list ->
                                  solved_proof_obligation_t list

  end

module Make (Opt:module type of GenOptions) : S
