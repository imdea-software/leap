open LeapLib

module Sys = System
module E = Expression
module Tac = Tactics


type premise_t = Self | Others

type desc_t =
  {
    mutable detFolder : string ;
      (** Folder for detailed information output  *)
    mutable detProg : string ;
      (** Program name for detailed information   *)
    mutable detInv : string ;
      (** Target invariant used for detailed info *)
    mutable gral_supp : Tag.f_tag list ;
      (** General support tags *)
    supp_table : (E.pc_t*IGraph.premise_t, Tag.f_tag list) Hashtbl.t;
      (** Special cases support tags *)
  }


type special_cases_form_tbl_t = (E.pc_t * IGraph.premise_t,
                                 E.formula list * Tac.proof_plan) Hashtbl.t


type solver_info =
  {
(*
    mutable prog_lines : int ;
    dp : dp_info;
    mutable cutoff : Smp.cutoff_strategy_t ;
*)
    mutable out_file : string ;
    mutable detailed_desc : desc_t ;
    mutable focus : E.pc_t list;
    mutable hide_pres : bool;
    mutable abstraction : Sys.abstraction;
    mutable specialCases : special_cases_form_tbl_t;
    mutable general_proof_plan : Tac.proof_plan;
  }


let solverInfo : solver_info = {
(*  prog_lines = 0; *)
(*  dp = { pos_dp  = false;
         tll_dp  = false;
         num_dp  = false;
         tsl_dp  = false;
         tslk_dp = (false, 0) };
  cutoff = Smp.Dnf;
*)
  out_file = "";
  detailed_desc = {detFolder = ""; detProg = ""; detInv = "";
                   gral_supp = []; supp_table = Hashtbl.create 10; };
  focus = [];
  hide_pres = false;
  abstraction = Sys.NoAbstraction;
  specialCases = Hashtbl.create 10;
  general_proof_plan = Tac.new_proof_plan (Some Smp.Dnf) [] [] [] [];
}



(****************************************************************)
(*                   TAGGING INFORMATION                        *)
(****************************************************************)

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



(****************************************************************)
(*               PARAMETRIZED INVARIANCE RULES                  *)
(****************************************************************)


let gen_vcs (sys:Sys.system_t)
            (supp:E.formula list)
            (inv:E.formula)
            (line:int)
            (premise:premise_t)
            (trans_tid:E.tid)
              : Tac.vc_info list =
(*    LOG "Entering gen_vcs..." LEVEL TRACE; *)
  let me_subst = E.new_tid_subst [(Sys.me_tid_th, trans_tid)] in
  let voc = E.voc (E.conj_list (inv::supp)) in
  let rho = Sys.gen_rho sys (Sys.SOpenArray voc) line solverInfo.abstraction
                solverInfo.hide_pres trans_tid in
  List.fold_left (fun rs phi ->
    let rho = E.subst_tid me_subst phi in
    let tid_constr = match premise with
                     | Self -> E.True
                     | Others -> E.conj_list $
                                   List.map (fun j ->
                                     E.ineq_tid trans_tid j
                                   ) (List.filter (fun i -> i<>trans_tid) voc) in
    let new_vc = Tac.create_vc_info supp tid_constr rho inv voc trans_tid line
    in
      new_vc :: rs
  ) [] rho


(***********)
(*  SPINV  *)
(***********)

(* SPINV Initialization *)
let spinv_premise_init (sys:Sys.system_t)
                       (inv:E.formula)
                          : Tac.vc_info =

  (* Initial condition *)
  let theta = Sys.gen_theta (Sys.SOpenArray (E.voc inv)) sys solverInfo.abstraction in
  let voc = E.voc (E.conj_list [theta;inv])
  in
    Tac.create_vc_info [] E.True theta inv voc E.NoThid 0



(* SPINV Conseqution *)

let spinv_premise_transitions (sys:Sys.system_t)
                              (lines_to_consider:int list)
                              (supp:E.formula list)
                              (inv:E.formula)
                                : Tac.vc_info list =
(*    LOG "Entering spinv_premise_transitions..." LEVEL TRACE; *)
  let voc = E.voc (E.conj_list (inv::supp)) in
  let k = E.gen_fresh_tid voc in
  List.fold_left (fun vcs line ->
    let self_vc = List.fold_left (fun vs i ->
                    vs @ gen_vcs sys supp inv line Self i
                  ) [] voc in
    let others_vc = gen_vcs sys supp inv line Others k
    in
      vcs @ self_vc @ others_vc
  ) [] lines_to_consider


let spinv (sys:Sys.system_t)
          (supp:E.formula list)
          (inv:E.formula) : Tac.vc_info list =
  let need_theta = List.mem 0 solverInfo.focus in
  let lines_to_consider = List.filter (fun x -> x <> 0) solverInfo.focus in
 
  let premise_init = if need_theta then
                       [spinv_premise_init sys inv]
                     else
                       [] in

  let premise_transitions = spinv_premise_transitions sys lines_to_consider supp inv
  in
    premise_init @ premise_transitions


let tag_spinv (sys : Sys.system_t)
              (supInv_list : Tag.f_tag list)
              (inv : Tag.f_tag) : Tac.vc_info list =
  let supInv_list_as_formula = 
    List.map (Tag.tag_table_get_formula tags) supInv_list in
  let inv_as_formula = Tag.tag_table_get_formula tags inv in
  spinv sys supInv_list_as_formula inv_as_formula


(**********************)
(*  SEQUENTIAL SPINV  *)
(**********************)

let seq_gen_vcs (sys:Sys.system_t)
                (supp:E.formula list)
                (inv:E.formula)
                (line:int)
                (premise:premise_t)
                (trans_tid:E.tid)
                  : Tac.vc_info list =
  let voc = E.voc (E.conj_list (inv::supp)) in
  let rho = Sys.gen_rho sys (Sys.SOpenArray voc) line solverInfo.abstraction
                solverInfo.hide_pres trans_tid in
  List.fold_left (fun rs phi ->
    let new_vc = Tac.create_vc_info supp E.True phi inv voc trans_tid line
    in
      new_vc :: rs
  ) [] rho



let seq_spinv_premise_transitions (sys:Sys.system_t)
                                  (lines_to_consider:int list)
                                  (supp:E.formula list)
                                  (inv:E.formula)
                                    : Tac.vc_info list =
  let trans_tid = match E.voc inv with
                  | [] -> E.gen_fresh_tid []
                  | i::[] -> i
                  | i::_ -> assert false in (* More than one thread parametrizing the invariant *)
  List.fold_left (fun vcs line ->
    vcs @ seq_gen_vcs sys supp inv line Self trans_tid
  ) [] lines_to_consider


let seq_spinv (sys:Sys.system_t)
              (supp:E.formula list)
              (inv:E.formula) : Tac.vc_info list =
  let need_theta = List.mem 0 solverInfo.focus in
  let lines_to_consider = List.filter (fun x -> x <> 0) solverInfo.focus in

  Printf.printf "LINES TO CONSIDER: %s" (String.concat "," (List.map string_of_int solverInfo.focus));
  Printf.printf "PROGRAM LINES: %i\n" (Sys.lines sys);

  let premise_init = if need_theta then
                       [spinv_premise_init sys inv]
                     else
                       [] in

  let premise_transitions = seq_spinv_premise_transitions sys lines_to_consider supp inv
  in
    premise_init @ premise_transitions


let tag_seq_spinv (sys : Sys.system_t)
                  (supInv_list : Tag.f_tag list)
                  (inv : Tag.f_tag) : Tac.vc_info list =
  let supInv_list_as_formula =
    List.map (Tag.tag_table_get_formula tags) supInv_list in
  let inv_as_formula = Tag.tag_table_get_formula tags inv in
  seq_spinv sys supInv_list_as_formula inv_as_formula



(****************************************************************)
(*             VERIFICATION CONDITIONS GENERATION               *)
(****************************************************************)


let gen_from_graph (sys:Sys.system_t)
                   (graph:IGraph.iGraph_t) : E.formula list =
  let graph_info = IGraph.graph_info graph in
  List.fold_left (fun vcs (mode, suppTags, invTag, cases, tacs) ->
    let supp_ids = String.concat "," $ List.map Tag.tag_id suppTags in
    let inv_id = Tag.tag_id invTag in
    let supp = List.map read_tag suppTags in
    let inv = read_tag invTag in
    match mode with
    | IGraph.Concurrent ->
        (* Add the code for concurrent proof rules *)
        vcs
    | IGraph.Sequential ->
        if Hashtbl.length cases <> 0 then begin
          (* Use seq_spinv with particular cases *)
          print_endline ("seq_spinv with cases for " ^supp_ids^ " -> " ^inv_id);
          let op_name = "_seq_sinvsp_" ^ supp_ids ^ "->" ^ inv_id in
          solverInfo.out_file <- (solverInfo.out_file ^ op_name);
          (* Generate the vc_info for each transition *)
          let vc_info_list = seq_spinv sys supp inv in
          Printf.printf "VC_INFO_LENGTH: %i\n" (List.length vc_info_list);
          let new_vcs = Tac.apply_tactics vc_info_list [] None [] []
          in
            vcs @ new_vcs
        end else begin
          match supp with
          | [] -> begin
                    (* No support. Use b-inv *)
                    let op_name = "_seq_binv_" ^ inv_id in
                    print_endline op_name;
                    solverInfo.out_file <- (solverInfo.out_file ^ op_name);
                    let new_vcs = []
                    in
                      vcs @ new_vcs
                  end
          | _  -> begin
                    (* There's support. Use seq_spinv *)
                    let op_name = "_seq_sinv_" ^ supp_ids ^ "->" ^ inv_id in
                    print_endline op_name;
                    solverInfo.out_file <- (solverInfo.out_file ^ op_name);
                    let new_vcs = []
                    in
                      vcs @ new_vcs
                  end
        end
  ) [] graph_info


(**************************************)
(*
    let load_cases (sc_tbl:special_cases_tag_tbl_t) : special_cases_form_tbl_t =
    let case_tbl = Hashtbl.create (Hashtbl.length sc_tbl) in
    let _ = Hashtbl.iter (fun (pc, prem) (tags, tacs) ->
              set_descSuppTbl solverInfo.detailed_desc (pc,prem) tags;
              Hashtbl.add case_tbl (pc, prem)
                (List.map (fun t -> let phi = read_tag t in
                                      Option.default E.False phi
                 )tags, tacs)
            ) sc_tbl
    in
      case_tbl in
      
  (* Process each rule in the invariant relation graph *)
  let graph_info = IGraph.graph_info graph in
  let base_out_name = solverInfo.out_file in
  let foldop res (mode, sup, inv, cases, tacs) =
    solverInfo.tactics <- tacs;
    let inv_id = Tag.tag_id inv in
    let sup_id = String.concat "," $ List.map Tag.tag_id sup in
    let inv_phi = Option.default E.False (read_tag inv) in
    let sup_phi = List.map (read_tag>>Option.(default E.False)) sup in
    let _ = set_detFileName inv_id in
    let _ = set_descGralSupp solverInfo.detailed_desc sup in
    let case_tbl = load_cases cases in
    solverInfo.special <- case_tbl;
    solverInfo.tactics <- tacs;
    match mode with
    | IGraph.Concurrent ->
      if sup_phi = [] then begin
        (* PINV *)
        if Hashtbl.length cases = 0 then printf "PINV+ for %s\n" inv_id
        else printf "PINV+ WITH CASES for %s\n" inv_id;
        let output_name = "_pinv_" ^ inv_id in
        solverInfo.out_file <- (base_out_name ^ output_name);
        let this_res = check_with_pinv_plus sys inv_phi in
          res && this_res
      end else begin
        if Hashtbl.length cases = 0 then begin
          (* SPINV *)
          printf "SPINV for %s -> %s\n" sup_id inv_id;
          let output_name = "_sinv_" ^ sup_id ^ "->" ^ inv_id in
          solverInfo.out_file <- (base_out_name ^ output_name);
          let this_res = check_with_spinv sys sup_phi inv_phi  in
            res && this_res
        end else begin
          (* SPINV WITH SPECIAL CASES *)
          printf "SPINV WITH CASES for %s -> %s\n" sup_id inv_id;
          let output_name = "_sinvsp_" ^ sup_id ^ "->" ^ inv_id in
          solverInfo.out_file <- (base_out_name ^ output_name);
          let this_res = check_with_spinv sys sup_phi inv_phi in
            res & this_res
        end
      end
  | IGraph.Sequential ->
      if Hashtbl.length cases <> 0 then begin
        (* SEQ_SPINV WITH SPECIAL CASES *)
          printf "SEQ_SPINV WITH CASES for %s -> %s\n" sup_id inv_id;
          let output_name = "_seq_sinvsp_" ^ sup_id ^ "->" ^ inv_id in
          solverInfo.out_file <- (base_out_name ^ output_name);
          let this_res = check_with_seq_spinv sys sup_phi inv_phi in
            res & this_res
      end else begin
        if sup_phi = [] then begin
          (* B-INV *)
          printf "B-INV+ for %s\n" inv_id;
          let output_name = "_seq_binv_" ^ inv_id in
          solverInfo.out_file <- (base_out_name ^ output_name);
(*            let this_res = check_with_seq_binv sys inv_phi in *)
          let this_res = check_with_seq_spinv sys [] inv_phi
          in
            res & this_res
        end else begin
          printf "SEQ_SPINV for %s -> %s\n" sup_id inv_id;
          let output_name = "_seq_sinv_" ^ sup_id ^ "->" ^ inv_id in
          solverInfo.out_file <- (base_out_name ^ output_name);
          let this_res = check_with_seq_spinv sys sup_phi inv_phi
          in
            res && this_res
        end
      end
  in
    List.fold_left foldop true graph_info
*)
