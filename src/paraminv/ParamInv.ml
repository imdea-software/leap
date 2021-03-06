
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


open LeapLib


module E = Expression
module PE = PosExpression


module type S =
  sig

    exception No_invariant_folder

    val gen_from_graph : IGraph.t -> Core.proof_obligation_t list

    val solve_from_graph : IGraph.t -> Core.solved_proof_obligation_t list

  end

module Make (C:Core.S) : S =
  struct

    module Eparser = ExprParser
    module Elexer = ExprLexer

    exception No_invariant_folder



    (* General Initialization premise *)
    let premise_init ?(inv_id="") (inv:E.formula) : Tactics.vc_info =
      let inv_voc = E.voc inv in
      let (new_voc, new_inv) =
        if E.ThreadSet.is_empty inv_voc then
          let new_t = E.gen_fresh_tid_as_var inv_voc in
          let new_i = E.param (E.V.Local new_t) inv in
          (E.ThreadSet.singleton (E.VarTh new_t), new_i)
        else
          (inv_voc, inv) in
      let (initial_cond, voc) = C.theta new_voc in
      Tactics.create_vc_info [] Tactics.no_tid_constraint initial_cond new_inv voc E.NoTid 0
        ~tag:(Tag.new_tag inv_id "")



    (**********************)
    (*  CONCURRENT SPINV  *)
    (**********************)


    let gen_vcs ?(inv_id="")
                (supp:E.formula list)
                (inv:E.formula)
                (line:int)
                (premise:Premise.t)
                (trans_tid:E.tid)
                  : Tactics.vc_info list =
      (***********************  TESTING  *************************)
      (* This adds threads identifiers belonging to the support, *)
      (* which I should not add until instantiating the support  *)
      (* later as part of the tactics.                           *)
      (***********************************************************)
      (* let voc = E.voc (Formula.conj_list (inv::supp)) in      *)
      (***********************  TESTING  *************************)
      let voc = E.voc inv in
      let rho = C.rho System.Concurrent voc line trans_tid in
      let tid_constraint = match premise with
                           | Premise.SelfConseq -> Tactics.no_tid_constraint
                           | Premise.OthersConseq ->
                               begin
                                 let ineqs = E.ThreadSet.fold (fun t xs ->
                                               (trans_tid,t)::xs
                                             ) voc [] in
                                 Tactics.new_tid_constraint [] ineqs
                               end in
      List.fold_left (fun rs phi ->
        Log.print "Create with support" (String.concat "\n" (List.map E.formula_to_str supp));
        let new_vc = Tactics.create_vc_info supp tid_constraint
                        phi inv voc trans_tid line ~tag:(Tag.new_tag inv_id "")
        in
          new_vc :: rs
      ) [] rho


    let spinv_transitions ?(inv_id="")
                          (supp:E.formula list)
                          (inv:E.formula)
                          (cases:IGraph.case_tbl_t)
                                : Tactics.vc_info list =
      let load_support (line:E.pc_t) (prem:Premise.t) : E.formula list =
        match IGraph.lookup_case cases line prem with
        | None -> supp
        | Some (supp_tags,_) -> C.read_tags_and_group_by_file Core.Inv supp_tags
      in
      List.fold_left (fun vcs line ->
        let self_conseq_supp  = load_support line Premise.SelfConseq in
        let other_conseq_supp = load_support line Premise.OthersConseq in
        let fresh_k = E.gen_fresh_tid (E.voc (Formula.conj_list (inv::supp@other_conseq_supp))) in

        let self_conseq_vcs = E.ThreadSet.fold (fun i vcs ->
                                (gen_vcs (inv::self_conseq_supp) inv line Premise.SelfConseq i
                                  ~inv_id:inv_id
                              ) @ vcs
                              ) (System.filter_me_tid (E.voc inv)) [] in
        let other_conseq_vcs = gen_vcs (inv::other_conseq_supp) inv line Premise.OthersConseq fresh_k
                                  ~inv_id:inv_id
        in

          vcs @ self_conseq_vcs @ other_conseq_vcs
      ) [] C.lines_to_consider


    let spinv_with_cases ?(inv_id="")
                         (supp:E.formula list)
                         (inv:E.formula)
                         (cases:IGraph.case_tbl_t) : Tactics.vc_info list =
      let initiation = if C.requires_theta then
                         [premise_init inv ~inv_id:inv_id]
                       else
                         [] in

      let transitions = spinv_transitions supp inv cases ~inv_id:inv_id
      in
        initiation @ transitions


    let spinv ?(inv_id="")
              (supp:E.formula list)
              (inv:E.formula) : Tactics.vc_info list =
      spinv_with_cases supp inv (IGraph.empty_case_tbl()) ~inv_id:inv_id



    (**********************)
    (*  SEQUENTIAL SPINV  *)
    (**********************)

    let seq_gen_vcs ?(inv_id="")
                    (supp:E.formula list)
                    (inv:E.formula)
                    (line:int)
                    (trans_tid:E.tid)
                      : Tactics.vc_info list =
      let trans_var = E.voc_to_var trans_tid in
      let voc = E.voc (Formula.conj_list (inv::supp)) in
      let rho = C.rho System.Sequential voc line trans_tid in
      let supp = List.map (E.param (E.V.Local trans_var)) supp in
      let inv = if E.ThreadSet.is_empty (E.voc inv) then
                  E.param (E.V.Local trans_var) inv
                else
                  inv in
      List.fold_left (fun rs phi ->
        let new_vc = Tactics.create_vc_info supp Tactics.no_tid_constraint
                       phi inv voc trans_tid line ~tag:(Tag.new_tag inv_id "") in
          new_vc :: rs
      ) [] rho



    let seq_spinv_transitions ?(inv_id="")
                              (supp:E.formula list)
                              (inv:E.formula)
                              (cases:IGraph.case_tbl_t)
                                : Tactics.vc_info list =
      let inv_voc = E.voc inv in
      let trans_tid = if E.ThreadSet.is_empty inv_voc then
                        E.gen_fresh_tid E.ThreadSet.empty
                      else
                        try
                          E.ThreadSet.choose inv_voc
                        with Not_found -> assert false in
                        (* ALE: More than one thread parametrizing the invariant *)
      List.fold_left (fun vcs line ->
        let specific_supp = match IGraph.lookup_case cases line Premise.SelfConseq with
                            | None -> supp
                            | Some (supp_tags, _) -> C.read_tags_and_group_by_file Core.Inv supp_tags in
        vcs @ seq_gen_vcs (inv::specific_supp) inv line trans_tid ~inv_id:inv_id
      ) [] C.lines_to_consider




    let seq_spinv_with_cases ?(inv_id="")
                             (supp:E.formula list)
                             (inv:E.formula)
                             (cases:IGraph.case_tbl_t) : Tactics.vc_info list =
      let supp = inv :: supp in
      let initiation = if C.requires_theta then
                         [premise_init inv ~inv_id:inv_id]
                       else
                         [] in

      let transitions = seq_spinv_transitions supp inv cases ~inv_id:inv_id
      in
        initiation @ transitions


    let seq_spinv ?(inv_id="")
                  (supp:E.formula list)
                  (inv:E.formula) : Tactics.vc_info list =
      seq_spinv_with_cases supp inv (IGraph.empty_case_tbl()) ~inv_id:inv_id




    (***************************************************)
    (*              PROOF GRAPH ANALYSIS               *)
    (***************************************************)

    let check_well_defined_graph (graph:IGraph.t) : unit =
      let graph_tags = IGraph.graph_tags graph in
      let undef_tags = List.filter (fun t -> not (C.is_def_tag t)) graph_tags in
      if undef_tags <> [] then begin
        let undef_t = Tag.tag_id (List.hd undef_tags) in
        Interface.Err.msg "Undefined tag" $
          Printf.sprintf "Tag %s was used in the invariant graph \
            but it could not be read from the invariant folder." undef_t;
        raise(Tag.Undefined_tag undef_t)
      end


    let generate_obligations (vcs:Tactics.vc_info list)
                             (gral_plan:Tactics.proof_plan)
                             (cases:IGraph.case_tbl_t) : Core.proof_obligation_t list =
      (* let vc_count = ref 1 in
         let show_progress = not (LeapVerbose.is_verbose_enabled()) in *)
      Progress.init (List.length vcs);
      List.fold_left (fun res vc ->
      (* Ale: for lists
        let vc = Tactics.to_plain_vc_info E.PCVars vc in *)
        let prem = if Tactics.is_empty_tid_constraint (Tactics.get_tid_constraint_from_info vc) then
                     Premise.SelfConseq
                   else
                     Premise.OthersConseq in

        let line = Tactics.get_line_from_info vc in
        let (obligations,cutoff) =
          match IGraph.lookup_case cases line prem with
          | None       -> (Tactics.apply_tactics_from_proof_plan [vc] gral_plan,
                           Tactics.get_cutoff gral_plan)
          | Some (_,p) -> let joint_plan = if Tactics.is_empty_proof_plan p then
                                             gral_plan
                                           else
                                             p in
                          (Tactics.apply_tactics_from_proof_plan [vc] joint_plan,
                           Tactics.get_cutoff joint_plan) in

        let proof_info = C.new_proof_info cutoff in
        let proof_obligation = C.new_proof_obligation vc obligations proof_info in
        (* if show_progress then (Progress.current !vc_count; incr vc_count); *)
          proof_obligation :: res
      ) [] vcs


    let gen_from_graph (graph:IGraph.t) : Core.proof_obligation_t list =
      check_well_defined_graph graph;

      (* Process the graph *)
      let graph_info = IGraph.graph_info graph in
      List.fold_left (fun os (mode, suppTags, invTag, cases, plan) ->
        let supp_ids = String.concat "," $ List.map Tag.tag_id suppTags in
        let inv_id = Tag.tag_id invTag in
        let supp = C.read_tags_and_group_by_file Core.Inv suppTags in
        let inv = C.read_tag Core.Inv invTag in
        let vc_info_list = match mode with
                           | IGraph.Concurrent ->
                              if LeapVerbose.is_verbose_enabled() then
                                LeapVerbose.verbstr
                                  ("Concurrent problem for invariant " ^inv_id^
                                   " using as support [" ^supp_ids^ "]" ^
                                   " with " ^string_of_int (IGraph.num_of_cases cases)^
                                   " special cases.\n")
                              else
                                print_endline ("Generating verification conditions for " ^ inv_id);
                             spinv_with_cases supp inv cases ~inv_id:inv_id
                           | IGraph.Sequential ->
                              if LeapVerbose.is_verbose_enabled() then
                                LeapVerbose.verbstr
                                  ("Sequential problem for invariant " ^inv_id^
                                   " using as support [" ^supp_ids^ "]" ^
                                   " with " ^string_of_int (IGraph.num_of_cases cases)^
                                   " special cases.\n")
                              else
                                print_endline ("Generating verification conditions for " ^ inv_id);
                             seq_spinv_with_cases supp inv cases ~inv_id:inv_id in
        C.report_vcs vc_info_list;
        let new_obligations = generate_obligations vc_info_list plan cases in
        let obligations_num = List.fold_left (fun n po ->
                                n + (List.length (C.obligations po))
                              ) 0 new_obligations in
        if (not (LeapVerbose.is_verbose_enabled())) then
          print_endline ("Generated: " ^ (string_of_int (List.length vc_info_list)) ^
                         " VC with " ^(string_of_int obligations_num) ^
                         " proofs obligations\n")
        else
          if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
            Report.report_generated_vcs vc_info_list obligations_num;
        os @ new_obligations
      ) [] graph_info


    let solve_from_graph (graph:IGraph.t) : Core.solved_proof_obligation_t list =
      (* gen_from_graph graph; [] *)
      C.solve_proof_obligations (gen_from_graph graph)
      

  end
