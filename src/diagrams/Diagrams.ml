open LeapLib

module E = Expression
module F = Formula


type pvd_vc_t = {
  initiation : Tactics.vc_info;
}


module type S =
  sig
    val gen_vcs : PVD.t -> pvd_vc_t
    val gen_from_pvd : PVD.t ->
                       PVD.support_t option ->
                       Core.proof_obligation_t list
    val solve_from_pvd : PVD.t ->
                         PVD.support_t option ->
                         Core.solved_proof_obligation_t list
  end


module Make (C:Core.S) : S =
  struct

    let gen_initiation (pvd:PVD.t) : Tactics.vc_info =
      let init_mu = F.disj_list (PVD.NodeIdSet.fold (fun n xs ->
                                  (PVD.node_mu pvd n) :: xs
                                ) (PVD.initial pvd) []) in
      let (theta, voc) = C.theta (E.voc init_mu) in
      Tactics.create_vc_info [] F.True theta init_mu voc E.NoTid 0


    let gen_vcs (pvd:PVD.t) : pvd_vc_t =
    let tmp =
      {
        initiation = gen_initiation pvd;
      }
    in
      print_endline (Tactics.vc_info_to_str tmp.initiation); tmp


    let check_well_defined_supp (supp:PVD.support_t) : unit =
      let tags = PVD.supp_tags supp in
      let undef_tags = List.filter (fun t -> not (C.is_def_tag t)) tags in
      if undef_tags <> [] then begin
        let undef_t = Tag.tag_id (List.hd undef_tags) in
        Interface.Err.msg "Undefined tag" $
          Printf.sprintf "Tag %s was used in PVD support \
            but it could not be read from the invariant folder." undef_t;
        raise(Tag.Undefined_tag undef_t)
      end


    let gen_from_pvd (pvd:PVD.t) (supp:PVD.support_t option)
        : Core.proof_obligation_t list =
      let _ = match supp with
              | None -> ()
              | Some s -> check_well_defined_supp s in
      let pvd_vcs = gen_vcs pvd in
      []


    let solve_from_pvd (pvd:PVD.t)
                       (supp:PVD.support_t option)
          : Core.solved_proof_obligation_t list =
      C.solve_proof_obligations (gen_from_pvd pvd supp)

  end
