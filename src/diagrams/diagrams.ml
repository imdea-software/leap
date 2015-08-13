open LeapLib

module E = Expression
module F = Formula
module GSet = LeapGenericSet

type node_vc_tbl_t = (int, PVD.node_id_t) Hashtbl.t


type pvd_vc_t = {
  initiation : Tactics.vc_info list;
  consecution : Tactics.vc_info list;
  acceptance : Tactics.vc_info list;
  fairness : Tactics.vc_info list;
  node_vcs : node_vc_tbl_t;
}

type gen_t =
  {
    lines : E.PosSet.t;
    conditions : PVD.conditions_t list;
    nodes : PVD.node_id_t list;
  }


let new_options (lines:Expression.PosSet.t)
                (cs:PVD.conditions_t list)
                (ns:PVD.node_id_t list) : gen_t =
  {
    lines = lines ;
    conditions = cs;
    nodes = ns;
  }


let consider_node (opt:gen_t option)
                  (n:PVD.node_id_t) : bool =
  match opt with
  | None -> true
  | Some info -> info.nodes = [] || List.mem n info.nodes


let consider_condition (opt:gen_t option)
                       (cond:PVD.conditions_t) : bool =
  match opt with
  | None -> true
  | Some info -> info.conditions = [] || List.mem cond info.conditions


let lines_cache : E.PosSet.t option ref = ref None


let consider_lines (opt:gen_t option) (sys:System.t) : E.PosSet.t =
  match !lines_cache with
  | None -> begin
              match opt with
              | None -> begin
                          let set = ref E.PosSet.empty in
                          for i = 1 to System.lines sys do
                            set := E.PosSet.add i !set
                          done;
                          lines_cache := Some !set; !set
                        end
              | Some o -> (lines_cache := Some o.lines; o.lines)
            end
  | Some set -> set


let add_node_vc_tbl (tbl:node_vc_tbl_t)
                    (n:PVD.node_id_t)
                    (vcs:Tactics.vc_info list) : unit =
  List.iter (fun vc ->
    Hashtbl.add tbl (Tactics.get_original_vc_id vc) n
  ) vcs
  

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


module Make (C:Core.S) : S =
  struct


    let gen_initiation ?(opt=None)
                       (pvd:PVD.t) : Tactics.vc_info list =
      if consider_condition opt PVD.Initiation then begin      
        let init_mu = F.disj_list (PVD.NodeIdSet.fold (fun n xs ->
                                    (PVD.node_mu pvd n) :: xs
                                  ) (PVD.initial pvd) []) in
        let (theta, voc) = C.theta (E.voc init_mu) in
        [Tactics.create_vc_info [] Tactics.no_tid_constraint theta init_mu voc E.NoTid 0]
      end else []


    let gen_consecution ?(opt=None)
                        (pvd:PVD.t)
                        (node_vc_tbl:node_vc_tbl_t) : Tactics.vc_info list =
      if consider_condition opt PVD.Consecution then begin
        let free_voc = PVD.free_voc pvd in
        let nodes = PVD.nodes pvd in
        PVD.NodeIdSet.fold (fun n vcs ->

          if consider_node opt n then begin

            let n_voc = match PVD.node_box pvd n with
                        | None -> free_voc
                        | Some b -> E.ThreadSet.add (PVD.box_param pvd b) free_voc in
            let mu_n = PVD.node_mu pvd n in
            let boxed_next = PVD.cond_next pvd PVD.Pres n in
            let other_next = PVD.cond_next pvd PVD.Any n in

            let boxed_next_disj =
              F.disj_list (PVD.NodeIdSet.fold (fun m xs ->
                            (PVD.node_mu pvd m) :: xs
                          ) boxed_next []) in

            let (other_next_disj, pre_assumptions) =
              let (onds, assumps) =
                PVD.NodeIdSet.fold (fun m (xs,ys) ->
                  let mu = PVD.node_mu pvd m in
                  print_endline ("NEXT MU: " ^ (E.formula_to_str mu));
                  (* Search for model functions in boxes *)
                  let assumptions =
                    List.fold_left (fun zs phi ->
                      match phi with
                      | F.Literal (F.Atom (E.Eq (E.TidT t, (E.TidT (E.CellLockId (E.CellAt (_,E.LastLocked _)) as tid_phi)))))
                      | F.Literal (F.Atom (E.Eq (E.TidT (E.CellLockId (E.CellAt (_,E.LastLocked _)) as tid_phi), E.TidT t ))) -> begin
                              match PVD.node_box pvd m with
                              | Some b ->
                                  (print_endline "SOME BOX";
                                   print_endline ("BOX PARAM: " ^ (E.tid_to_str (PVD.box_param pvd b)));
                                   print_endline ("BOX FUNC PARAM: " ^ (E.tid_to_str t));
                                  if PVD.box_param pvd b = t then
                                    (print_endline ("ADD MODEL FUNCTION FOR " ^ (E.tid_to_str t) ^ " WITH FORMULA " ^ (E.tid_to_str tid_phi));
                                    Tactics.ModelFunc(t,tid_phi)::zs)
                                  else
                                    (print_endline "FALSE"; zs))
                              | None -> zs
                             end
                      | _ -> zs
                    ) ys (F.to_conj_list mu) in
                  (* Search for model functions in boxes *)
                  (mu :: xs, assumptions)
                ) other_next ([],[]) in
              (F.disj_list onds, assumps) in

            Debug.infoMsg (fun _ -> "BOXED_NEXT_DISJ: " ^ (E.formula_to_str boxed_next_disj));
            Debug.infoMsg (fun _ -> "OTHER_NEXT_DISJ: " ^ (E.formula_to_str other_next_disj));

            (* Generate a fresh thread identifier *)
            let full_voc = E.ThreadSet.union n_voc
                             (E.voc_from_list [mu_n; boxed_next_disj; other_next_disj]) in
            let fresh_t = E.gen_fresh_tid full_voc in

            let (full_mu_n, goal, assumptions) =
              match PVD.node_box pvd n with
              | None ->
                  begin
                    assert (PVD.NodeIdSet.is_empty boxed_next);
                    (mu_n, other_next_disj, pre_assumptions)
                  end
              | Some b ->
                  begin
                    let t = PVD.box_param pvd b in
    (*                let t' = E.prime_tid t in *)
    (*                let t_cond = E.eq_tid t' t in *)
                    let t_subst = E.new_tid_subst [(t,fresh_t)] in
    (*                let box_param_subst = E.new_tid_subst [(t,t')] in *)
                    let fresh_other_next_disj = E.subst_tid t_subst other_next_disj in
    (*                (F.And (mu_n, t_cond), F.Or (boxed_next_disj, fresh_other_next_disj)) *)
                    (mu_n,
                     F.Or (boxed_next_disj, fresh_other_next_disj),
                     List.map (fun a -> 
                       match a with
                       | Tactics.ModelFunc(t,tid_phi) ->
                           Tactics.ModelFunc (E.subst_tid_th t_subst t,
                                              E.subst_tid_th t_subst tid_phi)
                     ) pre_assumptions)
                  end in

            let full_voc = E.ThreadSet.add fresh_t full_voc in
            E.PosSet.fold (fun line vcs ->
              (* Self-consecution *)
              let self_vcs =
                E.ThreadSet.fold (fun t ys ->
                  let self_rho = C.rho System.Concurrent full_voc line t in
                  (List.map (fun rho ->
                              print_endline ("GOAL: " ^ E.formula_to_str goal);
                              print_endline ("ASSUMPTIONS:");
                              List.iter (fun a ->
                                match a with
                                | Tactics.ModelFunc(t,phi) ->
                                    print_endline ("ASSUMPTION: " ^ (E.tid_to_str t) ^ " --> " ^ (E.tid_to_str phi))
                              ) assumptions;

                              let init_vc = Tactics.create_vc_info []
                                             Tactics.no_tid_constraint
                                              (F.And (full_mu_n, rho))
                                              goal full_voc t line in
                              List.fold_left Tactics.add_modelfunc_assumption init_vc assumptions
                             ) self_rho) @ ys
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
              add_node_vc_tbl node_vc_tbl n (self_vcs @ others_vcs);
              self_vcs @ others_vcs @ vcs
            ) (consider_lines opt C.system) vcs
          end else vcs
        ) nodes []
      end else []



    let gen_acceptance ?(opt=None)
                        (pvd:PVD.t)
                        (node_vc_tbl:node_vc_tbl_t) : Tactics.vc_info list =
      if consider_condition opt PVD.Acceptance then begin
        let free_voc = PVD.free_voc pvd in
        let acceptance_list = PVD.acceptance_list pvd in
        let edges = PVD.edge_list pvd in
        List.fold_left (fun acc_vcs accept ->
          (List.fold_left (fun edge_vcs (n,m,e_info_set) ->
            if consider_node opt n then begin
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
                
                let delta_voc = List.fold_left (fun set (t,_) ->
                                  E.ThreadSet.union set (E.voc_term t)
                                ) E.ThreadSet.empty accept.PVD.delta in
                let voc = E.ThreadSet.union delta_voc
                                            (E.voc_from_list [mu_n;unprimed_mu_m;beta]) in
                let lines_to_consider = consider_lines opt C.system in
                match trans with
                | PVD.NoLabel ->
                    begin
                      E.PosSet.fold (fun line vcs ->
                        (* Self-acceptance *)
                        let self_vcs =
                          E.ThreadSet.fold (fun t ys ->
                            let v_t = match t with
                                      | E.VarTh v -> v
                                      | _ -> assert false in
                            if PVD.NodeIdSet.is_empty (PVD.successor pvd n line v_t) then begin
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
                        add_node_vc_tbl node_vc_tbl n (self_vcs @ others_vcs);
                        self_vcs @ others_vcs @ vcs
                      ) (consider_lines opt C.system) xs
                    end
                | PVD.Label ts ->
                    begin
                      (List.fold_left (fun ys (line,v) ->
                        if E.PosSet.mem line lines_to_consider then begin
                          let t = E.VarTh v in
                          let rho_list = C.rho System.Concurrent voc line t in
                          (List.map (fun rho ->
                            let processed_mu_m = E.prime_modified [rho; beta] unprimed_mu_m in
                            let antecedent = F.conj_list [mu_n; rho; processed_mu_m; beta] in
                            let consequent = PVD.ranking_function antecedent accept (n,m,kind) in
                            let vc = Tactics.create_vc_info [] Tactics.no_tid_constraint
                                      antecedent consequent voc t line ~prime_goal:false in
                            add_node_vc_tbl node_vc_tbl n [vc];
                            vc
                          ) rho_list) @ ys
                        end else ys
                      ) [] ts ) @ xs
                    end
              ) e_info_set []) @ edge_vcs
            end else edge_vcs
          ) [] edges) @ acc_vcs
        ) [] acceptance_list
      end else []



    let gen_fairness ?(opt=None)
                      (pvd:PVD.t)
                      (node_vc_tbl:node_vc_tbl_t) : Tactics.vc_info list =
      if consider_condition opt PVD.Fairness then begin
        let edges = PVD.edge_list pvd in
        List.fold_left (fun vcs (n1,_,info) ->
          if consider_node opt n1 then begin
            let mu_n1 = PVD.node_mu pvd n1 in
            (PVD.EdgeInfoSet.fold (fun (_,trans) xs ->
              match trans with
              | PVD.NoLabel -> xs
              | PVD.Label trans_list ->
                  let lines_to_consider = consider_lines opt C.system in
                  (List.fold_left (fun gen_vcs (line,v) ->
                     if E.PosSet.mem line lines_to_consider then begin
                       let voc = E.voc mu_n1 in
                       let th = E.VarTh v in
                       let (_,stm) = System.get_statement_at C.system line in
                       let rho_list = C.rho System.Concurrent voc line th in
                       let next_mu =
                          F.disj_list $
                            PVD.NodeIdSet.fold (fun n xs ->
                              (PVD.node_mu pvd n) :: xs
                            ) (PVD.successor pvd n1 line v) [] in
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
                        add_node_vc_tbl node_vc_tbl n1 (enable_vc :: successor_vcs);
                        successor_vcs @ gen_vcs
(*                        enable_vc :: successor_vcs @ gen_vcs *)
                     end else gen_vcs
                  ) [] trans_list) @ xs
            ) info []) @ vcs
          end else vcs
        ) [] edges
      end else []



    let gen_vcs ?(opt=None) (pvd:PVD.t) : pvd_vc_t =
      let node_vc_tbl = Hashtbl.create 8 in
      {
        initiation = gen_initiation pvd ~opt:opt;
        consecution = gen_consecution pvd node_vc_tbl ~opt:opt;
        acceptance = gen_acceptance pvd node_vc_tbl ~opt:opt;
        fairness = gen_fairness pvd node_vc_tbl ~opt:opt;
        node_vcs = node_vc_tbl;
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
                             (n:PVD.node_id_t option)
                             (c:PVD.conditions_t)
        : Core.proof_obligation_t =
      let line = Tactics.get_line_from_info orig_vc in
      let (vc, plan) =
        match supp_opt with
        | None -> (orig_vc, Tactics.empty_proof_plan)
        | Some supp ->
            begin
              let supp_tags = PVD.supp_fact supp line n c in
              Debug.infoMsg (fun _ ->
                              "TAGS: " ^ (LeapLib.concat_map " , " Tag.tag_id supp_tags));
              let supp_formulas = C.read_tags_and_group_by_file supp_tags in
              Debug.infoMsg (fun _ ->
                              "SUPP_FORMULAS:\n" ^
                              (String.concat "\n"
                                (List.map Expression.formula_to_str supp_formulas)));
              Debug.infoMsg (fun _ -> "ORIG_VC: " ^ (Tactics.vc_info_to_str orig_vc));
                (Tactics.vc_info_add_support orig_vc supp_formulas,
                 PVD.supp_plan supp line n c)
            end in
      Debug.infoMsg (fun _ -> "VC INFO:\n " ^ (Tactics.vc_info_to_str vc));
      let obligations = Tactics.apply_tactics_from_proof_plan [vc] plan in
      let proof_info = C.new_proof_info (Tactics.get_cutoff plan) in
      let proof_obligation = C.new_proof_obligation vc obligations proof_info in
        proof_obligation


    let gen_from_pvd ?(opt=None) (pvd:PVD.t) (supp:PVD.support_t option)
        : Core.proof_obligation_t list =
      let _ = match supp with
              | None -> ()
              | Some s -> check_well_defined_supp s in
      let pvd_vcs = gen_vcs pvd ~opt:opt in
(*
      let vc_count = ref 1 in
      let show_progress = not (LeapVerbose.is_verbose_enabled()) in
*)
      Progress.init ((List.length pvd_vcs.initiation) +
                     (List.length pvd_vcs.consecution) +
                     (List.length pvd_vcs.acceptance) +
                     (List.length pvd_vcs.fairness));
      List.fold_left (fun os (c,xs) ->
        List.fold_left (fun os vc ->
          let n = try
                    Some (Hashtbl.find pvd_vcs.node_vcs (Tactics.get_original_vc_id vc))
                  with Not_found -> None in
          let new_obligation = generate_obligations vc supp n c in
(*          if show_progress then (Progress.current !vc_count; incr vc_count); *)
          new_obligation :: os
        ) os xs
      ) [] [(PVD.Initiation, pvd_vcs.initiation);
            (PVD.Consecution, pvd_vcs.consecution);
            (PVD.Acceptance, pvd_vcs.acceptance);
            (PVD.Fairness, pvd_vcs.fairness)]


    let solve_from_pvd ?(opt=None)
                       (pvd:PVD.t)
                       (supp:PVD.support_t option)
          : Core.solved_proof_obligation_t list =
      C.solve_proof_obligations (gen_from_pvd pvd supp ~opt:opt)

  end
