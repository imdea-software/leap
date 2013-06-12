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
                                  (supp:E.formula list)
                                  (inv:E.formula)
                                  (lines:E.pc_t list)
                                  (cases:IGraph.case_tbl_t)
                                    : Tac.vc_info list =
  let trans_tid = match E.voc inv with
                  | [] -> E.gen_fresh_tid []
                  | i::[] -> i
                  | i::_ -> assert false in (* More than one thread parametrizing the invariant *)
  List.fold_left (fun vcs line ->
    let specific_supp = match IGraph.lookup_case cases line Self with
                        | None -> supp
                        | Some (supp_tags, _) -> List.map read_tag supp_tags in
    vcs @ seq_gen_vcs sys specific_supp inv line Self trans_tid
  ) [] lines




let seq_spinv_using (sys:Sys.system_t)
                    (supp:E.formula list)
                    (inv:E.formula)
                    (lines:E.pc_t list)
                    (cases:supp_tbl_t) : Tac.vc_info list =
  let need_theta = List.mem 0 lines in
  let premise_init = if need_theta then
                       [spinv_premise_init sys inv]
                     else
                       [] in

  let premise_transitions = seq_spinv_premise_transitions sys supp inv lines cases
  in
    premise_init @ premise_transitions
  
  []


let seq_spinv (sys:Sys.system_t)
              (supp:E.formula list)
              (inv:E.formula) : Tac.vc_info list =
  seq_spinv_using sys supp inv (Sys.lines sys) (Hashtbl.create 1)


(*
let tag_seq_spinv (sys : Sys.system_t)
                  (supInv_list : Tag.f_tag list)
                  (inv : Tag.f_tag) : Tac.vc_info list =
  let supInv_list_as_formula =
    List.map (Tag.tag_table_get_formula tags) supInv_list in
  let inv_as_formula = Tag.tag_table_get_formula tags inv in
  seq_spinv sys supInv_list_as_formula inv_as_formula
*)



(****************************************************************)
(*             VERIFICATION CONDITIONS GENERATION               *)
(****************************************************************)


let gen_from_graph (sys:Sys.system_t)
                   (graph:IGraph.iGraph_t) : E.formula list =
  []



