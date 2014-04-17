

module type S =
  sig

    exception No_invariant_folder

    val gen_from_graph : IGraph.t -> Core.proof_obligation_t list

    val solve_from_graph : IGraph.t -> Core.solved_proof_obligation_t list

  end

module Make (C:Core.S) : S
