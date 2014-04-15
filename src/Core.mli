


module GenOptions :
  sig

    val sys : System.t
    val focus : Expression.pc_t list
    val ignore : Expression.pc_t list
    val abs : System.abstraction
    val hide_pres : bool
    val output_file : string
    val inv_folder : string
    val dp : DP.t
    val pSolver : string
    val tSolver : string
    val compute_model : bool
    val group_vars : bool
    val forget_primed_mem : bool
    val default_cutoff : Smp.cutoff_strategy_t
    val use_quantifiers : bool
    val output_vcs : bool

  end


module type S =
  sig

    exception No_invariant_folder

    type proof_obligation_t

    type solved_proof_obligation_t

    (* Getters *)
    val sys : System.t
    val abs : System.abstraction
    val hide_pres : bool
    val output_vcs : bool
    val prog_type : Bridge.prog_type
    val lines_to_consider : int list
    val requires_theta : bool

    val filter_me_tid : Expression.ThreadSet.t -> Expression.ThreadSet.t

    val report_vcs : Tactics.vc_info list -> unit

    val decl_tag : Tag.f_tag option -> Expression.formula -> unit
    val is_def_tag : Tag.f_tag -> bool
    val read_tags_and_group_by_file : Tag.f_tag list -> Expression.formula list

    val gen_theta : Expression.formula -> (Expression.formula * Expression.ThreadSet.t)


  end

module Make (Opt:module type of GenOptions) : S
