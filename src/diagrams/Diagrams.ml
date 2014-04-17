open LeapLib

module E = Expression
module F = Formula


type pvd_vc_t = {
  initiation : Tactics.vc_info;
  consecution : Tactics.vc_info list;
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
        consecution = [];
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

    let generate_obligations (orig_vc:Tactics.vc_info)
                             (supp_opt:PVD.support_t option)
        : Core.proof_obligation_t =
      let line = Tactics.get_line_from_info orig_vc in
      let (vc, plan) =
        match supp_opt with
        | None -> (orig_vc, Tactics.empty_proof_plan)
        | Some supp ->
            begin
              let supp_tags = PVD.supp_fact supp line in
              let supp_formulas = C.read_tags_and_group_by_file supp_tags in
                (Tactics.vc_info_add_support orig_vc supp_formulas,
                 PVD.supp_plan supp line)
            end in
      let obligations = Tactics.apply_tactics_from_proof_plan [vc] plan in
      let proof_info = C.new_proof_info (Tactics.get_cutoff plan) in
      let proof_obligation = C.new_proof_obligation vc obligations proof_info in
        proof_obligation


    let gen_from_pvd (pvd:PVD.t) (supp:PVD.support_t option)
        : Core.proof_obligation_t list =
      let _ = match supp with
              | None -> ()
              | Some s -> check_well_defined_supp s in
      let pvd_vcs = gen_vcs pvd in
      let vc_list = pvd_vcs.initiation :: pvd_vcs.consecution in
      let vc_count = ref 1 in
      let show_progress = not (LeapVerbose.is_verbose_enabled()) in
      Progress.init (List.length vc_list);
      List.fold_left (fun os vc ->
        let new_obligation = generate_obligations vc supp in
        if show_progress then (Progress.current !vc_count; incr vc_count);
        new_obligation :: os
      ) [] vc_list


    let solve_from_pvd (pvd:PVD.t)
                       (supp:PVD.support_t option)
          : Core.solved_proof_obligation_t list =
      C.solve_proof_obligations (gen_from_pvd pvd supp)

  end
