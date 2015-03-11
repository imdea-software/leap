type pvd_vc_t

type gen_t

val new_options : PVD.conditions_t list ->
                  PVD.node_id_t list ->
                  gen_t

module type S =
  sig
    val gen_vcs : ?opt:gen_t option ->
                  PVD.t ->
                  pvd_vc_t
    val gen_from_pvd : ?opt:gen_t option ->
                       PVD.t ->
                       PVD.support_t option ->
                       Core.proof_obligation_t list
    val solve_from_pvd : ?opt:gen_t option ->
                         PVD.t ->
                         PVD.support_t option ->
                         Core.solved_proof_obligation_t list
  end

module Make (C:Core.S) : S
