type pvd_vc_t

module type S =
  sig
    val gen_vcs : PVD.t -> pvd_vc_t
    val gen_from_pvd : PVD.t -> PVD.support_t option -> Core.proof_obligation_t list
    val solve_from_pvd : PVD.t ->
                         PVD.support_t option ->
                         Core.solved_proof_obligation_t list
  end

module Make (C:Core.S) : S
