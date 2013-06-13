open LeapLib
open Printf


module E = Expression
module PE = PosExpression


module GenOptions :
  sig

    val sys : System.t
    val focus : Expression.pc_t list
    val ignore : Expression.pc_t list
    val abs : System.abstraction
    val hide_pres : bool
    val output_file : string
    val inv_folder : string
    val dp : DP.t
    val pSolver : string
    val tSolver : string
    val use_smt : bool
    val compute_model : bool
    val group_vars : bool
    val forget_primed_mem : bool

  end

  =

  struct

    let sys               = System.empty_system
    let focus             = []
    let ignore            = []
    let abs               = System.NoAbstraction
    let hide_pres         = true
    let output_file       = ""
    let inv_folder        = ""
    let dp                = DP.NoDP
    let pSolver           = BackendSolvers.Yices.identifier
    let tSolver           = BackendSolvers.Z3.identifier
    let use_smt           = false
    let compute_model     = false
    let group_vars        = false
    let forget_primed_mem = true

  end



module type S =
  sig

    exception No_invariant_folder

    type proof_obligation_t

    type solving_status_t =
      Unverified      |   (* The formula has not been analyzed              *)
      Invalid         |   (* The formula is invalid                         *)
      Valid of DP.t       (* The formula is valid                           *)

    type solved_proof_obligation_t

    val decl_tag : Tag.f_tag option -> Expression.formula -> unit

    val gen_from_graph : IGraph.t ->
                         proof_obligation_t list

  end

module Make (Opt:module type of GenOptions) : S =
  struct

    module Eparser = Exprparser
    module Elexer = Exprlexer

    exception No_invariant_folder


    type proof_obligation_t =
      {
        vc : Tactics.vc_info; (* Maybe it should contain less information in the future *)
        obligations : E.formula list;
      }


    type solving_status_t =
      Unverified      |   (* The formula has not been analyzed              *)
      Invalid         |   (* The formula is invalid                         *)
      Valid of DP.t       (* The formula is valid                           *)


    type resolution_info_t =
      {
        status : solving_status_t;
        time : float;
      }


    type solved_proof_obligation_t =
      {
        vc_info : Tactics.vc_info;
        solved_obligations : (E.formula * resolution_info_t) list;
        result : resolution_info_t;
      }


    (************************************************)
    (*             TAGGING INFORMATION              *)
    (************************************************)

    let tags : Tag.tag_table = Tag.tag_table_new


    let tags_num () : int = Tag.tag_table_size tags


    let decl_tag (t : Tag.f_tag option) (phi : E.formula) : unit =
      match t with
      | None -> ()
      | Some tag -> if Tag.tag_table_mem tags tag
          then
            raise(Tag.Duplicated_tag(Tag.tag_id tag))
          else Tag.tag_table_add tags tag phi Tag.new_info


    let read_tag (t : Tag.f_tag) : E.formula =
      if Tag.tag_table_mem tags t then
        Tag.tag_table_get_formula tags t
      else
        raise(Tag.Undefined_tag(Tag.tag_id t))


    let is_def_tag (t:Tag.f_tag) : bool =
      Tag.tag_table_mem tags t


    let clear_tags () : unit =
      Tag.tag_table_clear tags


    let load_tags_from_folder (folder:string) : unit =
      let all_files = Array.fold_left (fun xs f ->
                        (folder ^ "/" ^ f)::xs
                      ) [] (Sys.readdir folder) in
      let inv_files = List.filter (fun s -> Filename.check_suffix s "inv") all_files in
      List.iter (fun i ->
        let (phiVars, tag, phi) = Parser.open_and_parse i
                                      (Eparser.invariant Elexer.norm) in
          decl_tag tag phi
      ) inv_files


    (********************)
    (*   CONFIGURATION  *)
    (********************)

    let lines_to_consider = E.gen_focus_list (System.get_trans_num Opt.sys)
                             Opt.focus Opt.ignore

  
    let posSolver  : (module PosSolver.S) = PosSolver.choose Opt.pSolver

    let numSolver  : (module NumSolver.S) = NumSolver.choose Opt.tSolver

    let tllSolver  : (module TllSolver.S) = TllSolver.choose Opt.tSolver

    let tslkSolver : (module TslkSolver.S) = TslkSolver.choose Opt.tSolver
                                              (DP.get_tslk_param Opt.dp)

    let calls_counter : (DP.t, int) Hashtbl.t = Hashtbl.create 5


    (*****************************)
    (*    INITIALIZATION CODE    *)
    (*****************************)
    let _ =
      if Opt.inv_folder <> "" then begin
        if Sys.is_directory Opt.inv_folder then begin
          load_tags_from_folder Opt.inv_folder
        end else begin
          Interface.Err.msg "Not a valid invariant folder" $
            sprintf "%s is not a valid folder." Opt.inv_folder;
            raise(No_invariant_folder)
        end
      end


    (******************)
    (*  CONSTRUCTORS  *)
    (******************)

    let new_proof_obligation (vc:Tactics.vc_info)
                             (obligations:E.formula list) : proof_obligation_t =
      {
        vc = vc;
        obligations = obligations;
      }


    let new_resolution_info (status:solving_status_t)
                            (time:float) : resolution_info_t =
      {
        status = status;
        time = time;
      }


    let new_solved_proof_obligation (vc_info:Tactics.vc_info)
                                    (solved_oblig:(E.formula * resolution_info_t) list)
                                    (result:resolution_info_t) : solved_proof_obligation_t =
      {
        vc_info = vc_info;
        solved_obligations = solved_oblig;
        result = result;
      }



    (*************************)
    (*  AUXILIARY FUNCTIONS  *)
    (*************************)

    let set_status (res:bool) : solving_status_t =
      if res then Valid Opt.dp else Invalid

    

    let add_calls_to (dp:DP.t) (n:int) : unit =
      try
        Hashtbl.replace calls_counter dp ((Hashtbl.find calls_counter dp) + n)
      with _ -> Hashtbl.add calls_counter dp n


    let add_calls (n:int) : unit =
      add_calls_to Opt.dp n


    (***********)
    (*  SPINV  *)
    (***********)

    (* SPINV Initialization *)
    let spinv_premise_init (inv:E.formula) : Tactics.vc_info =

      (* Initial condition *)
      let theta = System.gen_theta (System.SOpenArray (E.voc inv)) Opt.sys Opt.abs in
      let voc = E.voc (E.conj_list [theta;inv])
      in
        Tactics.create_vc_info [] E.True theta inv voc E.NoThid 0




    (**********************)
    (*  SEQUENTIAL SPINV  *)
    (**********************)

    let seq_gen_vcs (supp:E.formula list)
                    (inv:E.formula)
                    (line:int)
                    (premise:Premise.t)
                    (trans_tid:E.tid)
                      : Tactics.vc_info list =
      let voc = E.voc (E.conj_list (inv::supp)) in
      let rho = System.gen_rho Opt.sys (System.SOpenArray voc) line Opt.abs
                    Opt.hide_pres trans_tid in
      List.fold_left (fun rs phi ->
        let new_vc = Tactics.create_vc_info supp E.True phi inv voc trans_tid line
        in
          new_vc :: rs
      ) [] rho



    let seq_spinv_transitions (supp:E.formula list)
                              (inv:E.formula)
                              (cases:IGraph.case_tbl_t)
                                : Tactics.vc_info list =
      let trans_tid = match E.voc inv with
                      | [] -> E.gen_fresh_tid []
                      | i::[] -> i
                      | i::_ -> assert false in (* More than one thread parametrizing the invariant *)
      List.fold_left (fun vcs line ->
        let specific_supp = match IGraph.lookup_case cases line Premise.SelfConseq with
                            | None -> supp
                            | Some (supp_tags, _) -> List.map read_tag supp_tags in
        vcs @ seq_gen_vcs specific_supp inv line Premise.SelfConseq trans_tid
      ) [] lines_to_consider




    let seq_spinv_with_cases (supp:E.formula list)
                             (inv:E.formula)
                             (cases:IGraph.case_tbl_t) : Tactics.vc_info list =
      let need_theta = List.mem 0 lines_to_consider in
      let initiation = if need_theta then
                         [spinv_premise_init inv]
                       else
                         [] in

      let transitions = seq_spinv_transitions supp inv cases
      in
        initiation @ transitions


    let seq_spinv (supp:E.formula list)
                  (inv:E.formula) : Tactics.vc_info list =
      seq_spinv_with_cases supp inv (IGraph.empty_case_tbl())


    (*
    let tag_seq_spinv (sys : System.t)
                      (supInv_list : Tag.f_tag list)
                      (inv : Tag.f_tag) : Tactics.vc_info list =
      let supInv_list_as_formula =
        List.map (Tag.tag_table_get_formula tags) supInv_list in
      let inv_as_formula = Tag.tag_table_get_formula tags inv in
      seq_spinv sys supInv_list_as_formula inv_as_formula
    *)





    (************************************************)
    (*              FORMULA ANALYSIS                *)
    (************************************************)

    let check_well_defined_graph (graph:IGraph.t) : unit =
      let graph_tags = IGraph.graph_tags graph in
      let undef_tags = List.filter (fun t -> not (is_def_tag t)) graph_tags in
      if undef_tags <> [] then begin
        let undef_t = Tag.tag_id (List.hd undef_tags) in
        Interface.Err.msg "Undefined tag" $
          Printf.sprintf "Tag %s was used in the invariant graph \
            but it could not be read from the invariant folder." undef_t;
        raise(Tag.Undefined_tag undef_t)
      end


    let generate_obligations (vcs:Tactics.vc_info list)
                             (gral_plan:Tactics.proof_plan)
                             (cases:IGraph.case_tbl_t) : proof_obligation_t list =
      List.fold_left (fun res vc ->
        let prem = match Tactics.get_tid_constraint_from_info vc with
                   | E.True -> Premise.SelfConseq
                   | _      -> Premise.OthersConseq in
        let line = Tactics.get_line_from_info vc in
        let obligations = match IGraph.lookup_case cases line prem with
                          | None       -> Tactics.apply_tactics_from_proof_plan [vc] gral_plan
                          | Some (_,p) -> Tactics.apply_tactics_from_proof_plan [vc] p in
        Printf.printf "=========================================================\n";
        Printf.printf "FOR VERIFYING THE FOLLOWING VC_INFO:\n\n%s\n" (Tactics.vc_info_to_str vc);
        Printf.printf "THE FOLLOWING FORMULAS MUST BE VALID:\n";
        Printf.printf "----------------------\n%s\n" (String.concat "\n" (List.map E.formula_to_human_str obligations));
        Printf.printf "=========================================================\n";
        let proof_obligation = new_proof_obligation vc obligations
        in
          proof_obligation :: res
      ) [] vcs


    let gen_from_graph (graph:IGraph.t) : proof_obligation_t list =
      check_well_defined_graph graph;

      (* Process the graph *)
      let graph_info = IGraph.graph_info graph in
      List.fold_left (fun os (mode, suppTags, invTag, cases, plan) ->
        let supp_ids = String.concat "," $ List.map Tag.tag_id suppTags in
        let inv_id = Tag.tag_id invTag in
        let supp = List.map read_tag suppTags in
        let inv = read_tag invTag in
        match mode with
        | IGraph.Concurrent ->
            (* Add the code for concurrent proof rules *)
            os
        | IGraph.Sequential ->
            if IGraph.num_of_cases cases <> 0 then begin
              (* Use seq_spinv with particular cases *)
              print_endline ("seq_spinv with cases for " ^supp_ids^ " -> " ^inv_id);
              let op_name = "_seq_sinvsp_" ^ supp_ids ^ "->" ^ inv_id in
              let out_file = Opt.output_file ^ op_name in
              (* Generate the vc_info for each transition *)
              let vc_info_list = seq_spinv_with_cases supp inv cases in
              Printf.printf "VC_INFO_LENGTH: %i\n" (List.length vc_info_list);
              let new_obligations = generate_obligations vc_info_list plan cases
              in
                os @ new_obligations
            end else begin
              match supp with
              | [] -> begin
                        (* No support. Use b-inv *)
                        let op_name = "_seq_binv_" ^ inv_id in
                        print_endline op_name;
                        let out_file = Opt.output_file ^ op_name in
                        let new_obligations = []
                        in
                          os @ new_obligations
                      end
              | _  -> begin
                        (* There's support. Use seq_spinv *)
                        let op_name = "_seq_sinv_" ^ supp_ids ^ "->" ^ inv_id in
                        print_endline op_name;
                        let out_file = Opt.output_file ^ op_name in
                        let new_obligations = []
                        in
                          os @ new_obligations
                      end
            end
      ) [] graph_info


    let f : (module PosSolver.S) =
      PosSolver.choose Opt.pSolver


    let solve_proof_obligations (to_analyze:proof_obligation_t list)
                                    : solved_proof_obligation_t list =
      let module Pos  = (val posSolver) in
      let module Num  = (val numSolver) in
      let module Tll  = (val tllSolver) in
      let module Tslk = (val tslkSolver) in

      let case_timer = new LeapLib.timer in
      let phi_timer = new LeapLib.timer in
      Hashtbl.clear calls_counter;

      let prog_lines = (System.get_trans_num Opt.sys) in


      List.map (fun case ->
        case_timer#start;
        let res_list =
              List.map (fun phi ->
                phi_timer#start;
                let status =
                  if Pos.is_valid prog_lines (fst (PE.keep_locations phi)) then
                    (add_calls_to DP.Loc 1; Valid DP.Loc)
                  else begin
                    let (valid, calls) =
                      match Opt.dp with
                      | DP.NoDP   -> (false, 0)
                      | DP.Loc    -> (false, 0)
                      | DP.Num    -> let num_phi = NumInterface.formula_to_int_formula phi in
                                      Num.is_valid_with_lines_plus_info prog_lines num_phi
                      | DP.Tll    -> (false, 0) (*let tll_phi = TllInterface.formula_to_tll_formula phi in
                                      Tll.is_valid_plus_info prog_lines cutoff tll_phi*)
                      | DP.Tsl    -> (false, 0)
                      | DP.Tslk k -> (false, 0) in
                    add_calls calls;
                    set_status valid
                   end in
                (* Analyze the formula *)
                phi_timer#stop;
                let phi_result = new_resolution_info status (phi_timer#elapsed_time) in
                (phi, phi_result)
              ) case.obligations in

        case_timer#stop;
        let case_result = new_resolution_info Unverified (case_timer#elapsed_time) in
        new_solved_proof_obligation case.vc res_list case_result
      ) to_analyze
  end
