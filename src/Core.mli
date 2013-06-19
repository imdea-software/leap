


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
    val use_smt : bool
    val compute_model : bool
    val group_vars : bool
    val forget_primed_mem : bool
    val default_cutoff : Smp.cutoff_strategy_t

  end


module type S =
  sig

    exception No_invariant_folder

    type proof_obligation_t

    type solving_status_t =
      Unverified      |   (* The formula has not been analyzed              *)
      Invalid         |   (* The formula is invalid                         *)
      Valid of DP.t       (* The formula is valid                           *)

    type solved_proof_obligation_t

    val decl_tag : Tag.f_tag option -> Expression.formula -> unit


    val gen_from_graph : IGraph.t -> proof_obligation_t list

    val solve_from_graph : IGraph.t -> solved_proof_obligation_t list


  end

module Make (Opt:module type of GenOptions) : S
