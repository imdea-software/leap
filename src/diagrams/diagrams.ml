open LeapLib

module E = Expression
module F = Formula


type pvd_vc_t = {
  initiation : Tactics.vc_info;
  consecution : Tactics.vc_info list;
  acceptance : Tactics.vc_info list;
  fairness : Tactics.vc_info list;
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
      Tactics.create_vc_info [] Tactics.no_tid_constraint theta init_mu voc E.NoTid 0


    let gen_consecution (pvd:PVD.t) : Tactics.vc_info list =
      let free_voc = PVD.free_voc pvd in
      let nodes = PVD.nodes pvd in
      PVD.NodeIdSet.fold (fun n vcs ->


        (* n1, n4 *)
        if n = "n1" then begin


        let n_voc = match PVD.node_box pvd n with
                    | None -> free_voc
                    | Some b -> E.ThreadSet.add (PVD.box_param pvd b) free_voc in
        let mu_n = PVD.node_mu pvd n in
        let boxed_next = PVD.cond_next pvd PVD.Pres n in
        let other_next = PVD.cond_next pvd PVD.Any n in
        let boxed_next_disj = F.disj_list (PVD.NodeIdSet.fold (fun n' xs ->
                                            (PVD.node_mu pvd n') :: xs
                                          ) boxed_next []) in
        let other_next_disj = F.disj_list (PVD.NodeIdSet.fold (fun n' xs ->
                                            (PVD.node_mu pvd n') :: xs
                                          ) other_next []) in
        let full_voc = List.fold_left (fun vSet phi ->
                         E.ThreadSet.union vSet (E.voc phi)
                       ) n_voc [mu_n; boxed_next_disj; other_next_disj] in
        let fresh_t = E.gen_fresh_tid full_voc in

        let (full_mu_n, goal) =
          match PVD.node_box pvd n with
          | None ->
              begin
                assert (PVD.NodeIdSet.is_empty boxed_next);
                (mu_n, other_next_disj)
              end
          | Some b ->
              begin
                let t = PVD.box_param pvd b in
                let t_cond = F.atom_to_formula (E.Eq(E.TidT (E.prime_tid t),
                                                     E.TidT t)) in
                let t_subst = E.new_tid_subst [(t,fresh_t)] in
                let fresh_other_next_disj = E.subst_tid t_subst other_next_disj in
                (F.And (mu_n, t_cond), F.Or (boxed_next_disj, fresh_other_next_disj))
              end in
        let full_voc = E.ThreadSet.add fresh_t full_voc in
        let n_vcs = ref [] in
        for line = 1 to (System.lines C.system) do
          (* Self-consecution *)
          let self_vcs =
            E.ThreadSet.fold (fun t ys ->
              let self_rho = C.rho System.Concurrent full_voc line t in
              (List.map (fun rho ->
                let aa =
                Tactics.create_vc_info [] Tactics.no_tid_constraint (F.And (full_mu_n, rho))
                  goal full_voc t line in
                print_endline
                                      ("VCINFO GENERATED:\n" ^
                                      (Tactics.vc_info_to_str aa)); aa) self_rho) @ ys
            ) n_voc [] in
          (* Others-consecution *)
          let fresh_k = E.gen_fresh_tid full_voc in
          let other_rho = C.rho System.Concurrent full_voc line fresh_k in
          let tid_ineqs = E.ThreadSet.fold (fun t xs ->
                            (fresh_k,t) :: xs
                          ) full_voc [] in
          let tid_constraints = Tactics.new_tid_constraint [] tid_ineqs in
          let others_vcs = List.map (fun rho ->
                             Tactics.create_vc_info [] tid_constraints (F.And (full_mu_n, rho))
                               goal full_voc fresh_k line
                           ) other_rho in
          n_vcs := self_vcs @ others_vcs @ !n_vcs
        done;
        !n_vcs @ vcs
        end else vcs
      ) nodes []


    let gen_acceptance (pvd:PVD.t) : Tactics.vc_info list =
      let free_voc = PVD.free_voc pvd in
      let acceptance_list = PVD.acceptance_list pvd in
      let edges = PVD.edge_list pvd in
      List.fold_left (fun acc_vcs accept ->
        (List.fold_left (fun edge_vcs (n,m,e_info_set) ->
(*          if n = "n5" && m = "n5" then begin *)

          let n_voc = match PVD.node_box pvd n with
                      | None -> free_voc
                      | Some b -> E.ThreadSet.add (PVD.box_param pvd b) free_voc in
          let mu_n = PVD.node_mu pvd n in
          let unprimed_mu_m = match PVD.node_box pvd m with
            | Some b -> begin
                          let p = PVD.box_param pvd b in
                          let subst = E.new_tid_subst [(p, E.prime_tid p)] in
                            E.subst_tid subst (PVD.node_mu pvd m)
                        end
            | None -> PVD.node_mu pvd m in


          (PVD.EdgeInfoSet.fold (fun (kind,trans) xs ->
            let beta = PVD.beta pvd (n,m,kind) in
            
            let voc = E.ThreadSet.union (E.voc_term (fst accept.PVD.delta))
                                        (E.voc_from_list [mu_n;unprimed_mu_m;beta]) in
            match trans with
            | PVD.NoLabel ->
                begin
                  let n_vcs = ref [] in
                  for line = 1 to (System.lines C.system) do
                    (* Self-acceptance *)
                    let self_vcs =
                      E.ThreadSet.fold (fun t ys ->
                        let v_t = match t with
                                  | E.VarTh v -> v
                                  | _ -> assert false in
                        if PVD.NodeIdSet.is_empty (PVD.succesor pvd n line v_t) then begin
                          let self_rho = C.rho System.Concurrent voc line t in
                          (List.map (fun rho ->
                            let processed_mu_m = E.prime_modified [rho; beta] unprimed_mu_m in
                            let antecedent = F.conj_list [mu_n; rho; processed_mu_m; beta] in
                            let consequent = PVD.ranking_function antecedent accept (n,m,kind) in
                            Tactics.create_vc_info [] Tactics.no_tid_constraint antecedent
                              consequent voc t line ~prime_goal:false
                          ) self_rho) @ ys
                        end else ys
                        ) n_voc [] in
                    (* Others-acceptance *)
                    let fresh_k = E.gen_fresh_tid voc in
                    let other_rho = C.rho System.Concurrent voc line fresh_k in
                    let tid_ineqs = E.ThreadSet.fold (fun t ys ->
                                      (fresh_k,t) :: ys
                                    ) voc [] in
                    let tid_constraints = Tactics.new_tid_constraint [] tid_ineqs in
                    let others_vcs = List.map (fun rho ->
                                       let processed_mu_m =
                                         E.prime_modified [rho; beta] unprimed_mu_m in
                                       let antecedent = F.conj_list [mu_n; rho; processed_mu_m; beta] in
                                       let consequent = PVD.ranking_function antecedent
                                                              accept (n,m,kind) in
                                       Tactics.create_vc_info [] tid_constraints antecedent
                                         consequent voc fresh_k line ~prime_goal:false
                                     ) other_rho in
                    n_vcs := self_vcs @ others_vcs @ !n_vcs
                  done;
                  !n_vcs @ xs
                end
            | PVD.Label ts ->
                begin
                  (List.fold_left (fun ys (line,v) ->
                    let t = E.VarTh v in
                    let rho_list = C.rho System.Concurrent voc line t in
                    (List.map (fun rho ->
                      let processed_mu_m = E.prime_modified [rho; beta] unprimed_mu_m in
                      let antecedent = F.conj_list [mu_n; rho; processed_mu_m; beta] in
                      let consequent = PVD.ranking_function antecedent accept (n,m,kind) in
                      Tactics.create_vc_info [] Tactics.no_tid_constraint antecedent
                        consequent voc t line ~prime_goal:false
                    ) rho_list) @ ys
                  ) [] ts ) @ xs
                end
          ) e_info_set []) @ edge_vcs
(*          end else edge_vcs *)
        ) [] edges) @ acc_vcs
      ) [] acceptance_list


(*

*)
      



    let gen_fairness (pvd:PVD.t) : Tactics.vc_info list =
      let edges = PVD.edge_list pvd in
      List.fold_left (fun vcs (n1,n2,info) ->
        let mu_n1 = PVD.node_mu pvd n1 in
        (PVD.EdgeInfoSet.fold (fun (_,trans) xs ->
          match trans with
          | PVD.NoLabel -> xs
          | PVD.Label trans_list ->
              (List.fold_left (fun gen_vcs (line,v) ->
                 let voc = E.voc mu_n1 in
                 let th = E.VarTh v in
                 let (_,stm) = System.get_statement_at C.system line in
                 let rho_list = C.rho System.Concurrent voc line th in
                 let next_mu =
                    F.disj_list $
                      PVD.NodeIdSet.fold (fun n xs ->
                        (PVD.node_mu pvd n) :: xs
                      ) (PVD.succesor pvd n1 line v) [] in
                 let conds =
                   F.disj_list (Statement.enabling_condition (E.V.Local v) stm) in
                  (* Enabled *)
                  let enable_vc = Tactics.create_vc_info [] Tactics.no_tid_constraint
                                    mu_n1 conds voc th line in
                  (* Successor *)
                  let successor_vcs =
                    List.map (fun rho ->
                      Tactics.create_vc_info [] Tactics.no_tid_constraint
                          (F.And (mu_n1,rho)) next_mu voc th line
                    ) rho_list in
                  enable_vc :: successor_vcs @ gen_vcs
              ) [] trans_list) @ xs
        ) info []) @ vcs
      ) [] edges




    let gen_vcs (pvd:PVD.t) : pvd_vc_t =
      Printf.printf "ACCEPTANCE VCS: %i\n" (List.length (gen_acceptance pvd));
      {
        initiation = gen_initiation pvd;
        consecution = gen_consecution pvd;
        acceptance = gen_acceptance pvd;
        fairness = gen_fairness pvd;
      }


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
              print_endline ("TAGS: " ^ (LeapLib.concat_map " , " Tag.tag_id supp_tags));
              let supp_formulas = C.read_tags_and_group_by_file supp_tags in
              print_endline ("SUPP_FORMULAS:\n" ^ (String.concat "\n" (List.map Expression.formula_to_str supp_formulas)));
              print_endline ("ORIG_VC: " ^ (Tactics.vc_info_to_str orig_vc));
                (Tactics.vc_info_add_support orig_vc supp_formulas,
                 PVD.supp_plan supp line)
            end in
      print_endline ("VC INFO:\n " ^ (Tactics.vc_info_to_str vc));
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
      let vc_list = (*pvd_vcs.initiation :: *)
                    pvd_vcs.consecution (*@
                    pvd_vcs.acceptance *)(*in
                    pvd_vcs.fairness in *) in
      let vc_count = ref 1 in
      let show_progress = not (LeapVerbose.is_verbose_enabled()) in
      Progress.init (List.length vc_list);
      List.fold_left (fun os vc ->
        let new_obligation = generate_obligations vc supp in

(************************************************************************)
(***   REMOVE THIS BEFORE COMPILING                                   ***)
(************************************************************************)
        C.solve_proof_obligations [new_obligation];
(************************************************************************)
(***   REMOVE THIS BEFORE COMPILING                                   ***)
(************************************************************************)

        if show_progress then (Progress.current !vc_count; incr vc_count);
        new_obligation :: os
      ) [] vc_list


    let solve_from_pvd (pvd:PVD.t)
                       (supp:PVD.support_t option)
          : Core.solved_proof_obligation_t list =
      C.solve_proof_obligations (gen_from_pvd pvd supp)

  end
