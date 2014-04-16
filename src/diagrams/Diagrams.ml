open LeapLib

module E = Expression
module F = Formula


type pvd_vc_t = {
	initiation : Tactics.vc_info;
}


module type S =
  sig
		val gen_vcs : PVD.t -> pvd_vc_t
	end


module Make (C:Core.S) : S =
  struct

		let gen_initiation (pvd:PVD.t) : Tactics.vc_info =
			let init_mu = F.disj_list (PVD.NodeIdSet.fold (fun n xs ->
																	(PVD.node_mu pvd n) :: xs
																) (PVD.initial pvd) []) in
			let (theta, voc) = C.theta (E.voc init_mu) in
			Tactics.create_vc_info [] F.True theta init_mu voc E.NoTid 0


		let gen_vcs (pvd:PVD.t) : vc_t =
			{
				initiation = gen_initiation pvd;
      }
	end
