type pvd_vc_t

module type S =
	sig
		val gen_vcs : PVD.t -> pvd_vc_t
  end

module Make (C:Core.S) : S
