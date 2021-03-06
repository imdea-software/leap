
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


open Printf

module E = Expression
module GenSet = LeapGenericSet
module F = Formula
module UF = LeapUnionFind

type vc_id = int

type polarity = Pos | Neg | Both

type assumption_t = ModelFunc of E.tid * E.tid

type vc_extra_info_t =
  {
    orig_vc_id : vc_id;
    prime_goal : bool;
    assume: assumption_t list;
    tag : Tag.f_tag;
  }

type support_t = E.formula list

type tid_constraints_t =
  {
    eq : (E.tid * E.tid) list;
    ineq : (E.tid * E.tid) list;
  }

type vc_info = {
  original_support : support_t ; (* Boxed formulas, tids must be renamed *)
  tid_constraint   : tid_constraints_t ;
  
  rho             : E.formula  ;   (* transition relation *)

  original_goal   : E.formula  ;
  goal            : E.formula  ;
  transition_tid  : E.tid      ;
  line            : E.pc_t     ;
  vocabulary      : E.ThreadSet.t ; (* May not be needed *)
  extra_info      : vc_extra_info_t;
}


type verification_condition = {
  antecedent : E.formula ;
  consequent : E.formula ;
  support         : support_t ; 
  (* this is the support computed using some tactic, including 
     exhaustive brute force *)
  info            : vc_info   ;
}


type implication = {
  ante : E.formula ;
  conseq : E.formula ;
}

type support_option_t =
  | DefaultSupport 
  | FilterSupport

type support_split_tactic_t = vc_info -> vc_info list
type support_tactic_t = (vc_info -> support_t) * support_option_t
type formula_split_tactic_t = implication -> implication list
type formula_tactic_t = implication -> implication

type proof_plan =
  {
    cutoff_algorithm : Smp.cutoff_strategy_t option     ;
    support_split_tactics : support_split_tactic_t list ;
    support_tactics  : support_tactic_t list            ;
    formula_split_tactics : formula_split_tactic_t list ;
    formula_tactics  : formula_tactic_t list            ;
  }


type gen_supp_op_t =
  | KeepOriginal
      (* When generating support keeps the original support unmodified     *)
  | RestrictSubst of (int -> E.tid_subst_t -> bool)
      (* Restricts assignments to the ones satisfies by the given function *)


type filter_criteria_t =
  | NoCriteria
  | AllExceptHeap
  | LocalOnly
  | MallocCrit

exception Invalid_tactic of string

let empty_tag : Tag.f_tag = Tag.new_tag "" ""

(*********************)
(**  Configuration  **)
(*********************)

let fixed_voc : E.ThreadSet.t ref = ref E.ThreadSet.empty

let unique_vc_id = ref 1


(***********************)
(* CONSTRUCTORS        *)
(***********************)

let new_tid_constraint (eqs:(E.tid * E.tid) list)
                       (ineqs:(E.tid * E.tid) list) : tid_constraints_t =
  {
    eq = eqs;
    ineq = ineqs;
  }


let new_proof_plan (smp:Smp.cutoff_strategy_t option)
                   (supp_split_tacs:support_split_tactic_t list)
                   (supp_tacs:support_tactic_t list)
                   (formula_split_tacs:formula_split_tactic_t list)
                   (formula_tacs:formula_tactic_t list) : proof_plan =
  {
    cutoff_algorithm = smp;
    support_split_tactics = supp_split_tacs;
    support_tactics = supp_tacs;
    formula_split_tactics = formula_split_tacs;
    formula_tactics = formula_tacs;
  }

let tid_constraint_to_formula (tc:tid_constraints_t) : E.formula =
  let eqs = List.map (fun (t,r) -> E.eq_tid t r) tc.eq in
  let ineqs = List.map (fun (t,r) -> E.ineq_tid t r) tc.ineq
  in
    F.conj_list (eqs @ ineqs)
 
let vc_info_to_implication (info:vc_info) (sup:support_t): implication =
  (* Propagate equalities between threads so we just keep the minimum
   * amount of required threads *)
  let me = System.me_tid_th in
  let me' = E.prime_tid me in
  let t = info.transition_tid in
  let t' = E.prime_tid info.transition_tid in

  let tid_eq = F.conj_list (List.fold_left (fun xs (t,r) ->
                 if t <> me && r <> me && t <> me' && r <> me' then
                   (E.eq_tid t r) :: xs
                 else
                   xs
               ) [] info.tid_constraint.eq) in
  let tid_ineq = F.conj_list (List.map (fun (t,r) -> E.ineq_tid t r) info.tid_constraint.ineq) in
  let eq_subst = E.new_tid_subst (info.tid_constraint.eq @ [(me,t);(me',t')]) in
  let substed_rho = E.subst_tid eq_subst info.rho in
  let rho = match (tid_eq, tid_ineq) with
            | (F.True, F.True) -> substed_rho
            | (F.True, _     ) -> F.And(tid_ineq, substed_rho)
            | (_     , F.True) -> F.And(tid_eq, substed_rho)
            | (_     , _     ) -> F.conj_list [tid_eq; tid_ineq; substed_rho] in
  let goal = E.subst_tid eq_subst info.goal in
  

  (* This code adds equalities that were implicit when we used arrays to represent local vars *)
  let build_pc pr i = E.build_pc_var pr (E.V.Local (E.voc_to_var i)) in
  let goal_voc = E.voc goal in
  let pc_updates : (E.V.t, E.V.t) Hashtbl.t = Hashtbl.create 4 in
  let var_updates : (E.V.t, E.ThreadSet.t) Hashtbl.t = Hashtbl.create 4 in

  E.ThreadSet.iter (fun i -> Hashtbl.add pc_updates (build_pc false i) (build_pc true i)) goal_voc;
  List.iter (fun phi ->
    match phi with
    | F.Or (F.Literal (F.Atom (E.PCUpdate (_,i))), _)
    | F.Literal (F.Atom (E.PCUpdate (_,i))) ->
        Hashtbl.remove pc_updates (build_pc false i)
    | F.Literal (F.Atom (E.Eq (E.ArrayT (E.VarArray v), E.ArrayT (E.ArrayUp (_,i,_))))) ->
        begin
          try
            Hashtbl.replace var_updates v (E.ThreadSet.remove i (Hashtbl.find var_updates v))
          with _ -> Hashtbl.add var_updates v (E.ThreadSet.remove i goal_voc)
        end
    | _ -> ()
  ) (F.to_conj_list rho);
  let pc_pres = E.V.new_subst () in
  Hashtbl.iter (fun v v' -> E.V.add_subst pc_pres v' v) pc_updates;
  let var_pres = E.V.new_subst () in
  Hashtbl.iter (fun v' tids ->
    E.V.VarSet.iter (fun i ->
      E.V.add_subst var_pres (E.V.set_param v' (E.V.Local i))
                             (E.V.set_param (E.V.unprime v') (E.V.Local i))
    ) (E.voc_to_vars tids)
  ) var_updates;
  (* This code adds equalities that were implicit when we used arrays to represent local vars *)
  let new_goal = if info.extra_info.prime_goal then
                   E.prime_modified [rho] goal
                 else
                   goal in
  let pre_antecedent = F.And (F.conj_list sup, rho) in
  (* let the_antecedent = E.to_plain_formula E.PCVars pre_antecedent in *)
  let the_antecedent =
    E.to_plain_formula E.PCVars (
      List.fold_left (fun phi a ->
        let assumption =
          match a with
          | ModelFunc (t, psi) ->
              begin
                let other_tids = E.ThreadSet.remove t goal_voc in
                let cond = F.conj_list (E.ThreadSet.fold (fun r conj ->
                                         E.ineq_tid r psi :: conj
                                        ) other_tids []) in
                E.prime_modified [rho] (F.Implies (cond, E.eq_tid t psi))
              end in
        F.And (assumption, phi)
      ) pre_antecedent info.extra_info.assume) in

  let the_consequent =
      E.subst_vars pc_pres
        (E.to_plain_formula E.PCVars
        (E.subst_vars var_pres new_goal)) in
  { ante = the_antecedent; conseq = the_consequent; }


let vc_info_to_formula (info:vc_info) (sup:support_t): E.formula =
  let implication = vc_info_to_implication info sup in
  Formula.Implies (implication.ante, implication.conseq)


let vc_info_to_vc (info:vc_info) (sup:support_t): verification_condition =
  let implication = vc_info_to_implication info sup in
  { 
    info       = info                ;
    support    = sup                 ;
    antecedent = implication.ante    ; 
    consequent = implication.conseq  ; 
  }


let default_cutoff_algorithm = Smp.Dnf


let to_plain_vc_info (fol_mode:E.fol_mode_t) (info:vc_info) : vc_info =
  let f = E.to_plain_formula fol_mode in
  let tf = E.to_plain_tid fol_mode in
  let tf_map = List.map (fun (t,r) -> (tf t, tf r)) in
  {
    original_support = List.map f info.original_support;
    tid_constraint = {eq = tf_map info.tid_constraint.eq;
                      ineq = tf_map info.tid_constraint.ineq;};
    rho = f info.rho;
    original_goal = f info.original_goal;
    goal = f info.goal;
    transition_tid = info.transition_tid;
    line = info.line;
    vocabulary = info.vocabulary;
    extra_info = info.extra_info;
  }


let vc_info_to_str (vc:vc_info) : string =
  let tid_constraint = tid_constraint_to_formula vc.tid_constraint in
  let vars_to_declare = E.all_vars (F.conj_list (tid_constraint     ::
                                                 vc.rho             ::
                                                 vc.goal            ::
                                                 vc.original_support)) in
  let vars_str = (String.concat "\n"
                   (List.map (fun v ->
                     (E.sort_to_str (E.V.sort v)) ^ " " ^
                     (E.V.to_str v)
                   ) vars_to_declare)) in
  let supp_str = String.concat "\n" (List.map E.formula_to_str vc.original_support) in
  let tid_eqs = List.map (fun (t,r) -> E.formula_to_str (E.eq_tid t r)) vc.tid_constraint.eq in
  let tid_ineqs = List.map (fun (t,r) -> E.formula_to_str (E.ineq_tid t r)) vc.tid_constraint.ineq in

  let tidconst_str = String.concat " , " (tid_eqs @ tid_ineqs) in
  
  let rho_str = E.formula_to_str vc.rho in
  let goal_str = E.formula_to_str vc.goal in
  let tid_str = E.tid_to_str vc.transition_tid in
  let line_str = string_of_int vc.line
  in
    "vars:\n" ^ vars_str ^ "\n\n" ^
    "Support:\n" ^ supp_str ^ "\n\n" ^
    "TidConstraint:\n" ^ tidconst_str ^ "\n\n" ^
    "Rho:\n" ^ rho_str ^ "\n\n" ^
    "Goal:\n" ^ goal_str ^ "\n\n" ^
    "Tid: " ^ tid_str ^ "\n\n" ^
    "Line: " ^ line_str ^ "\n\n"


let vc_info_to_plain_str (vc:vc_info) : string =
  vc_info_to_str (to_plain_vc_info E.PCVars vc)


let vc_info_to_str_simple (vc:vc_info) : string =
  let conj_to_str (phi:E.formula) : string =
    String.concat "\n" (List.map E.formula_to_str (F.to_conj_list phi)) in

  let supp_str = String.concat "\n------\n" (List.map conj_to_str vc.original_support) in
  let tidconst_str = E.formula_to_str (tid_constraint_to_formula vc.tid_constraint) in
  let rho_str = conj_to_str vc.rho in
  let goal_str = conj_to_str vc.goal
  in
    "SUPPORT:\n" ^ supp_str ^ "\n" ^
    "CONSTRAINT:\n" ^ tidconst_str ^ "\n" ^
    "RHO:\n" ^ rho_str ^ "\n" ^
    "GOAL:\n" ^ goal_str ^ "\n"


let vc_info_list_to_folder (output_file:string) (vcs:vc_info list) : unit =
  let infoTbl = Hashtbl.create (List.length vcs) in
  List.iter (fun vc_info ->
    let line = vc_info.line in
    let vc_num = try
                   let prev = Hashtbl.find infoTbl line in
                   Hashtbl.replace infoTbl line (prev+1);
                   string_of_int (prev+1)
                 with _ -> (Hashtbl.add infoTbl line 1; "1") in
    let out_file = output_file ^
                      ("vc_" ^ (string_of_int line) ^ "_" ^ vc_num ^ ".vcfile") in
    let out_ch = Pervasives.open_out out_file in
    Pervasives.output_string out_ch (vc_info_to_plain_str vc_info);
    Pervasives.close_out out_ch
  ) vcs


let create_vc_info ?(prime_goal=true)
                   ?(tag=empty_tag)
                   (supp       : support_t)
                   (tid_constr : tid_constraints_t)
                   (rho        : E.formula)
                   (goal       : E.formula)
                   (vocab      : E.ThreadSet.t)
                   (trans_tid  : E.tid)
                   (line       : E.pc_t) : vc_info =
  let id = !unique_vc_id in
  incr unique_vc_id;
    {
      original_support   = supp ;
      tid_constraint     = tid_constr ;
      rho                = rho ;
      original_goal      = goal ;
      goal               = if prime_goal then E.prime_modified [rho] goal else goal;
      transition_tid     = trans_tid ;
      line               = line ;
      vocabulary         = vocab ; (* ALE: We may not need it here, as it can be computed. *)
      extra_info         = {orig_vc_id = id;
                            prime_goal = prime_goal;
                            assume = [];
                            tag = tag; } ;
    }


let create_vc ?(prime_goal=true)
              ?(tag=empty_tag)
              (orig_supp  : support_t)
              (tid_constr : tid_constraints_t)
              (rho        : E.formula)
              (goal       : E.formula)
              (vocab      : E.ThreadSet.t)
              (trans_tid  : E.tid)
              (line       : E.pc_t) 
              (support    : support_t)
                : verification_condition =
  vc_info_to_vc (create_vc_info orig_supp tid_constr rho goal vocab trans_tid line ~prime_goal:prime_goal ~tag:tag) support


let dup_vc_info_with_support (info:vc_info) (new_support:support_t) : vc_info =
  {
    original_support = new_support ;
    tid_constraint   = info.tid_constraint;
    rho              = info.rho ;
    original_goal    = info.original_goal ;
    goal             = info.goal ;
    transition_tid   = info.transition_tid ;
    line             = info.line ;
    vocabulary       = info.vocabulary ; (* ALE: May need to be recomputed. *)
    extra_info       = info.extra_info ;
  }


let dup_vc_info_with_goal (info:vc_info) (new_goal:E.formula) : vc_info =
  {
    original_support   = info.original_support ;
    tid_constraint = info.tid_constraint;
    rho            = info.rho ;
    original_goal  = info.original_goal ;
    goal           = new_goal ;
    transition_tid = info.transition_tid ;
    line           = info.line ;
    vocabulary     = info.vocabulary ; (* ALE: May need to be recomputed. *)
    extra_info     = info.extra_info ;
  }


let dup_vc_info_with_supp_constr_rho_and_goal (info:vc_info)
                                              (new_support:support_t)
                                              (new_constr:tid_constraints_t)
                                              (new_rho:E.formula)
                                              (new_goal:E.formula) : vc_info =
  {
    original_support = new_support ;
    tid_constraint = new_constr;
    rho            = new_rho ;
    original_goal  = info.original_goal ;
    goal           = new_goal ;
    transition_tid = info.transition_tid ;
    line           = info.line ;
    vocabulary     = info.vocabulary ; (* ALE: May need to be recomputed. *)
    extra_info     = info.extra_info ;
  }


let add_modelfunc_assumption (info:vc_info) (a:assumption_t) : vc_info =
  {
    original_support = info.original_support ;
    tid_constraint   = info.tid_constraint;
    rho              = info.rho ;
    original_goal    = info.original_goal ;
    goal             = info.goal ;
    transition_tid   = info.transition_tid ;
    line             = info.line ;
    vocabulary       = info.vocabulary ; (* ALE: May need to be recomputed. *)
    extra_info       = {orig_vc_id = info.extra_info.orig_vc_id;
                        prime_goal = info.extra_info.prime_goal;
                        assume = a :: info.extra_info.assume;
                        tag = info.extra_info.tag;} ;
  }


let set_fixed_voc (ts:E.ThreadSet.t) : unit =
  fixed_voc := E.ThreadSet.add System.me_tid_th ts


let vc_info_add_support (info:vc_info) (supp:support_t) : vc_info =
  {
    original_support = info.original_support @ supp ;
    tid_constraint   = info.tid_constraint;
    rho              = info.rho ;
    original_goal    = info.original_goal ;
    goal             = info.goal ;
    transition_tid   = info.transition_tid ;
    line             = info.line ;
    vocabulary       = info.vocabulary ; (* ALE: May need to be recomputed. *)
    extra_info       = info.extra_info ;
  }
  


let filter_fixed_voc (ts:E.ThreadSet.t) : E.ThreadSet.t =
  let unprimed_ts = E.ThreadSet.fold (fun t set ->
                      E.ThreadSet.add (E.unprime_tid t) set
                    ) ts E.ThreadSet.empty in
  E.ThreadSet.diff unprimed_ts !fixed_voc


(****************************)
(* SELECTORS                *)
(****************************)

(* Get functions for type plan *)

let get_cutoff (plan:proof_plan) : Smp.cutoff_strategy_t option =
  plan.cutoff_algorithm
and get_support_tactics (plan:proof_plan) : support_tactic_t list =
  plan.support_tactics
and get_formula_tactics (plan:proof_plan) : formula_tactic_t list =
  plan.formula_tactics
and is_empty_proof_plan (plan:proof_plan) : bool =
  plan.support_split_tactics = [] && plan.support_tactics = [] &&
  plan.formula_split_tactics = [] && plan.formula_tactics = [] &&
  plan.cutoff_algorithm = None
and empty_proof_plan : proof_plan =
  new_proof_plan None [] [] [] []



let get_unprocessed_support_from_info (info:vc_info) : support_t =
  info.original_support
and get_tid_constraint_from_info (info:vc_info) : tid_constraints_t = info.tid_constraint
and get_vocabulary_from_info (info:vc_info) : E.ThreadSet.t    =  info.vocabulary
and get_rho_from_info (info:vc_info) : E.formula =  info.rho
and get_goal_from_info (info:vc_info) : E.formula =  info.goal
and get_transition_tid_from_info (info:vc_info) : E.tid =  info.transition_tid
and get_line_from_info (info:vc_info) : E.pc_t = info.line
and get_original_vc_id (info:vc_info) : int = info.extra_info.orig_vc_id
and get_vc_tag (info:vc_info) : Tag.f_tag = info.extra_info.tag


let get_antecedent (vc:verification_condition) : E.formula=
  vc.antecedent
let get_consequent (vc:verification_condition) : E.formula=
  vc.consequent
let get_support (vc:verification_condition) : support_t =
  vc.support
let get_unprocessed_support (vc:verification_condition) : support_t =
  get_unprocessed_support_from_info vc.info
let get_tid_constraint (vc:verification_condition) : tid_constraints_t =
  get_tid_constraint_from_info vc.info
let get_rho (vc:verification_condition) : E.formula =
  get_rho_from_info vc.info
let get_goal (vc:verification_condition) : E.formula =
  get_goal_from_info vc.info
let get_transition_tid (vc:verification_condition) : E.tid =
  get_transition_tid_from_info vc.info
let get_line (vc:verification_condition) : E.pc_t =
  get_line_from_info vc.info
let get_vocabulary (vc:verification_condition) : E.ThreadSet.t =
  get_vocabulary_from_info vc.info


let no_tid_constraint : tid_constraints_t =
  { eq = []; ineq = []; }


let is_empty_tid_constraint (tc:tid_constraints_t) : bool =
  tc.eq == [] && tc.ineq == []



(***************)
(* SIMPLIFIERS *)
(***************)

(* Auxiliary simplification functions *)

let invert_polarity pol =
  match pol with
      Pos -> Neg
    | Neg -> Pos
    | Both -> Both


let generic_simplifier (phi:E.formula) (simp_lit:E.literal-> polarity->E.formula) : E.formula =
  let is_true  (f:E.formula):bool = match f with F.True  -> true | _ -> false in
  let is_false (f:E.formula):bool = match f with F.False -> true | _ -> false in
  let rec simplify_f (f:E.formula) (pol:polarity): E.formula=
    match f with
        F.Literal(lit) -> (simp_lit lit pol)
      | F.True         -> F.True
      | F.False        -> F.False
      | F.And(x,y)     -> let sx = (simplify_f x pol) in
                          let sy = (simplify_f y pol) in
                            if (is_false sx || is_false sy) then F.False
                            else if (is_true sx && is_true sy) then F.True
                            else if (is_true sx) then sy
                            else if (is_true sy) then sx
                            else F.And(sx,sy)
      | F.Or(x,y)      -> let sx = (simplify_f x pol) in
                          let sy = (simplify_f y pol) in
                            if (is_true sx || is_true sy) then F.True
                            else if (is_false sx && is_false sy) then F.False
                            else if (is_false sx ) then sy
                            else if (is_false sy ) then sx
                            else F.Or(sx,sy)
      | F.Not(x)       -> let sx = (simplify_f x (invert_polarity pol)) in
                            if (is_true sx) then F.False
                            else if(is_false sx) then F.True
                            else F.Not(sx)
      | F.Implies(x,y) -> let sx = (simplify_f x (invert_polarity pol)) in
                          let sy = (simplify_f y pol) in
                            if (is_false sx || is_true sy) then F.True
                            else if (is_true sx) then sy
                            else if (is_false sy) then F.Not(sx)
                            else F.Implies(sx,sy)
      | F.Iff(x,y)     -> let sx = (simplify_f x Both) in
                          let sy = (simplify_f y Both) in
                            if (is_false sx && is_false sy) then F.True
                            else if (is_true sx && is_true sy) then F.True
                            else if (is_true sx) then sy
                            else if (is_true sy) then sx
                            else if (is_false sx) then F.Not(sy)
                            else if (is_false sy) then F.Not(sx)
                            else F.Iff(sx,sy)
  in
    simplify_f phi Pos

let simplify (phi:E.formula) : E.formula =
  let id l _ = F.Literal l in
    generic_simplifier phi id



(* simplify_with_vocabulary: simply removes the whole formula if the vocabulary
 *                           is irrelevant *)
let simplify_with_vocabulary (phi:E.formula) (vocabulary:E.V.t list): E.formula =
  let vars_in_phi = E.all_vars_as_set phi in
  let relevant = List.exists (fun v -> E.V.VarSet.mem v vars_in_phi) vocabulary in
    if relevant then
      phi
    else
      F.True


(**************************************************************************)
(* SUPPORT TACTICS, that generate support (E.formula list) from vc_info   *)
(**************************************************************************)
let generate_support (info:vc_info) : E.formula list =
  (* ALE: May need to review this part. *)
  let (no_param,param) =
    List.partition (fun phi -> E.ThreadSet.is_empty (E.voc phi)) info.original_support in
  let target_voc = E.ThreadSet.elements (E.voc (F.And (info.goal, info.rho))) in
  (* ALE: Review this *)
  let instantiate_one_support phi =
    let subst = E.new_comb_subst (E.ThreadSet.elements (E.voc phi)) target_voc in
    List.map (fun s -> E.subst_tid s phi) subst 
  in
  let instantiated_support = List.fold_left 
    (fun supp phi -> (instantiate_one_support phi) @ supp) [] param
  in
  no_param @ instantiated_support


(***************************)
(*  FORMULA SPLIT TACTICS  *)
(***************************)



let split_implication (imp:implication) : implication list =
  let new_conseqs = F.to_conj_list imp.conseq in
  List.map (fun phi -> { ante=imp.ante ; conseq=phi }) new_conseqs


let split_antecedent_pc (imp:implication) : implication list =
  let candidates (phi:E.formula) : E.formula list =
    List.fold_left (fun xs conj ->
      let cand_disj = F.to_disj_list conj in
      if List.length cand_disj > 1 &&
         List.for_all (fun x ->
            match x with
            | F.Literal (F.Atom (E.Eq (E.IntT (E.VarInt v), E.IntT (E.IntVal _))))
            | F.Literal (F.Atom (E.Eq (E.IntT (E.IntVal _), E.IntT (E.VarInt v)))) -> E.is_pc_var v
            | _ -> false
        ) cand_disj then
            cand_disj @ xs
      else
        xs
    ) [] (F.to_conj_list phi)
  in
  let cases = candidates imp.ante in
  match cases with
  | [] -> [imp]
  | _  -> List.map (fun a ->
            {
              ante = F.And (a,imp.ante);
              conseq = imp.conseq;
            }
          ) cases


(***************************)
(*  SUPPORT SPLIT TACTICS  *)
(***************************)

let split_goal (info:vc_info) : vc_info list =
  let new_goals = F.to_conj_list info.goal in
  List.map (fun phi -> {
        original_support = info.original_support;
        tid_constraint   = info.tid_constraint  ;
        rho              = info.rho ;
        original_goal    = info.original_goal;
        goal             = phi ;
        transition_tid   = info.transition_tid ;
        line             = info.line ;
        vocabulary       = info.vocabulary ;
        extra_info       = info.extra_info ;
    })
    new_goals
(* aux functions *)
let is_true (f:E.formula) : bool =
  match f with
  F.True -> true
  | _  -> false

let is_false (f:E.formula) : bool =
  match f with
    F.False -> true
  | _     -> false


let rec get_literals f =
  match f with
    F.Literal l  -> [l]
  | F.And(f1,f2)       -> get_literals f1 @ get_literals f2
  | F.Not(F.Or(f1,f2)) -> get_literals f1 @ get_literals f2
  | _          -> []


(* simplify_with_fact: takes the given literal as a fact, and removes all
                         instances of identical literals in the formula for true *)
let generic_simplify_with_fact (fact:'a)
    (implies:'a -> E.literal -> bool)
    (implies_neg:'a -> E.literal -> bool)
    (phi:E.formula): E.formula =
  let rec simplify_lit f = 
    match f with
      F.Literal l -> 
  if      (implies fact l)     then F.True 
  else if (implies_neg fact l) then F.False
  else f
    | F.True        -> F.True
    | F.False       -> F.False
    | F.And(f1, f2) -> F.And(simplify_lit f1, simplify_lit f2)
    | F.Or (f1, f2) -> F.Or (simplify_lit f1, simplify_lit f2)
    | F.Not f       -> F.Not(simplify_lit f)
    | F.Implies(f1,f2) -> F.Implies (simplify_lit f1, simplify_lit f2)
    | F.Iff    (f1,f2) -> F.Iff (simplify_lit f1, simplify_lit f2)
  in
  simplify (simplify_lit phi)
  

let simplify_with_fact (lit:E.literal) 
                       (implies:E.literal -> E.literal -> bool)
                       (implies_neg:E.literal -> E.literal -> bool)
                       (phi:E.formula) : E.formula =
  generic_simplify_with_fact lit implies implies_neg phi

let generic_simplify_with_many_facts (facts:'a list)
    (implies:'a -> E.literal -> bool)
    (implies_not:'a -> E.literal -> bool)
    (phi:E.formula) : E.formula =
  let rec simplify_lit f =
    match f with
    | F.Literal l -> begin
                       if List.exists (fun p -> implies p l) facts then begin
                         Log.print "** simplifying" ((E.literal_to_str l) ^ " with true");
                         F.True
                       end else if List.exists (fun p -> implies_not p l) facts then begin
                         Log.print "** simplifying" ((E.literal_to_str l) ^ " with false");
                         F.False
                       end else
                         F.Literal l
                     end
    | F.True           -> F.True
    | F.False          -> F.False
    | F.And(f1,f2)     -> F.And(simplify_lit f1, simplify_lit f2)
    | F.Or (f1,f2)     -> F.Or (simplify_lit f1, simplify_lit f2)
    | F.Not f          -> F.Not(simplify_lit f)
    | F.Implies(f1,f2) -> F.Implies (simplify_lit f1, simplify_lit f2)
    | F.Iff    (f1,f2) -> F.Iff (simplify_lit f1, simplify_lit f2)
  in
  let res = simplify (simplify_lit phi) in
   res
  
let simplify_with_many_facts (ll:E.literal list) 
    (implies:E.literal -> E.literal -> bool)
    (implies_neg:E.literal -> E.literal -> bool)
    (phi:E.formula) : E.formula =
  generic_simplify_with_many_facts ll implies implies_neg phi

let get_unrepeated_literals (phi:E.formula) : E.literal list = 
  let candidates = get_literals phi in
  List.fold_left (fun res l ->
    if (List.exists (fun alit -> E.identical_literal alit l) res) then
      res
    else
      res@[l]
  ) [] candidates


(*********************)
(*  SUPPORT TACTICS  *)
(*********************)

let gen_support (op:gen_supp_op_t) (info:vc_info) : support_t =
  Log.print_ocaml "entering gen_support()";
  match op with
  | KeepOriginal -> info.original_support
  | RestrictSubst f ->
      let goal_voc = E.voc info.goal in
      let tid_eqs = info.tid_constraint.eq in
      let tid_ineqs = info.tid_constraint.ineq in
      let tid_constraint_voc = List.fold_left (fun set (t,r) ->
                                 E.ThreadSet.add t (E.ThreadSet.add r set)
                               ) E.ThreadSet.empty (tid_eqs @ tid_ineqs) in
      let used_tids = ref (E.ThreadSet.union tid_constraint_voc
                           (E.ThreadSet.union (E.voc info.rho) goal_voc)) in

      let (unparam_support, param_support) =
        List.fold_left (fun (u_set,p_set) supp ->
          let supp_voc = filter_fixed_voc (E.voc supp) in


          let fresh_tids = E.gen_fresh_tid_set !used_tids (E.ThreadSet.cardinal supp_voc) in
          let fresh_subst = E.new_tid_subst
                              (List.combine (E.ThreadSet.elements supp_voc)
                                            (E.ThreadSet.elements fresh_tids)) in
          used_tids := E.ThreadSet.union fresh_tids !used_tids;


          let fresh_supp = E.subst_tid fresh_subst supp in
          let split_supp = F.to_conj_list fresh_supp in
          List.fold_left (fun (us,ps) phi ->
            if E.ThreadSet.is_empty (filter_fixed_voc (E.voc phi)) then
              (E.FormulaSet.add phi us,ps)
            else
              (us,E.FormulaSet.add phi ps)
          ) (u_set,p_set) split_supp
        ) (E.FormulaSet.empty,E.FormulaSet.empty) info.original_support in

      let processed_support =
        E.FormulaSet.fold (fun phi set ->

          let supp_voc = filter_fixed_voc (E.voc phi) in

          let rho_voc = filter_fixed_voc (E.voc info.rho) in

          let voc_to_consider = List.fold_left E.ThreadSet.union
                                  (E.ThreadSet.singleton info.transition_tid)
                                  [rho_voc; goal_voc] in
          Debug.infoMsg (fun _ -> "PROCESSING SUPPORT: " ^ (E.formula_to_str phi));
          Debug.infoMsg (fun _ -> "RHO IS: " ^ (E.formula_to_str info.rho));
          Debug.infoMsg (fun _ -> "THE GOAL IS: " ^ (E.formula_to_str info.goal));

          Debug.infoMsg (fun _ -> "SUPP_VOC: " ^ (E.tidset_to_str supp_voc));
          Debug.infoMsg (fun _ -> "VOC_TO_CONSIDER: " ^ (E.tidset_to_str voc_to_consider));
          (* assert (not (E.ThreadSet.mem System.me_tid_th voc_to_consider)); *)
          (* let voc_to_consider = E.ThreadSet.add info.transition_tid
                                  (E.ThreadSet.union supp_voc goal_voc) in *)
          let subst = List.filter (f (E.ThreadSet.cardinal supp_voc))
                        (E.new_comb_subst
                          (E.ThreadSet.elements supp_voc)
                          (E.ThreadSet.elements voc_to_consider)) in

          Log.print "Thread id substitution" (String.concat " -- " (List.map E.subst_to_str subst));
          List.fold_left (fun set s ->
            Debug.infoMsg (fun _ -> "GENERATED SUPPORT: " ^ (E.formula_to_str (E.subst_tid s phi)));
            E.FormulaSet.add (E.subst_tid s phi) set
          ) set subst
        ) param_support unparam_support in
      E.FormulaSet.elements processed_support


let full_support (info:vc_info) : support_t =
  gen_support (RestrictSubst (fun _ _ -> true)) info


let reduce_support (info:vc_info) : support_t =
  let voc_to_analyze = E.ThreadSet.union (E.voc info.rho) (E.voc info.goal) in
    gen_support (RestrictSubst
      (fun i subst ->
        E.subst_codomain_in voc_to_analyze subst && E.subst_domain_size subst == i)) info


let reduce2_support (info:vc_info) : support_t =
  let voc_to_analyze = E.ThreadSet.union (E.voc info.rho) (E.voc info.goal) in
  Debug.infoMsg (fun _ -> "REDUCE2 RHO: " ^ (E.formula_to_str info.rho));
  Debug.infoMsg (fun _ -> "REDUCE2 GOAL: " ^ (E.formula_to_str info.goal));
  Debug.infoMsg (fun _ -> "REDUCE2 VOC TO ANALYZE: " ^ (E.tidset_to_str voc_to_analyze));
  F.cleanup_dups
    (gen_support (RestrictSubst
      (fun i subst ->
        E.subst_codomain_in voc_to_analyze subst && E.subst_domain_size subst == i)) info)


let id_support (info:vc_info) : support_t =
  F.cleanup_dups (gen_support KeepOriginal info)


let self_support (info:vc_info) : support_t =
  F.cleanup_dups
    (gen_support (RestrictSubst
      (fun i subst ->
        E.subst_codomain_in (E.ThreadSet.singleton info.transition_tid) subst)) info)


(*********************)
(*  FORMULA TACTICS  *)
(*********************)
let tactic_propositional_propagate (imp:implication) : implication =
  Log.print_ocaml "entering tactic_propositional_propagate()";
  let implies     = E.identical_literal in
  let implies_neg = E.opposite_literal in
  let rec simplify_propagate (f:implication) (used:E.literal list) : 
      (implication * E.literal list) =
    (* ALE: I have removed from new_facts already learned facts *)
    let new_facts = List.filter (fun x ->
                      not (List.mem x used)
                    ) (get_unrepeated_literals f.ante) in
    Log.print "* New facts:" (String.concat "; " (List.map E.literal_to_str new_facts));
    
    if List.length new_facts = 0 then (f,used) else
      begin
        let new_conseq = simplify_with_many_facts new_facts implies implies_neg f.conseq in
        let new_ante   = simplify_with_many_facts new_facts implies implies_neg f.ante in
          simplify_propagate { ante = new_ante; conseq = new_conseq } (used @ new_facts)
      end
  in
  let (new_imp,facts) = simplify_propagate imp [] in
  let new_ante = F.cleanup (F.And((F.conj_literals facts), new_imp.ante)) in
  let new_conseq = new_imp.conseq in
  { ante = new_ante ; conseq = new_conseq }


let extract_pc_integer_eq (l:E.literal) : ((E.V.t * int) option) =
  match l with
    F.Atom(E.Eq(E.VarT(v),          E.IntT(E.IntVal k)))
  | F.Atom(E.Eq(E.IntT(E.VarInt(v)),E.IntT(E.IntVal k)))
  | F.Atom(E.Eq(E.IntT(E.IntVal(k)),E.VarT(v)))
  | F.Atom(E.Eq(E.IntT(E.IntVal(k)),E.IntT(E.VarInt(v)))) ->
      if E.is_pc_var v then
        Some (v,k)
      else
        None
  | _  -> None

let integer_implies ((v,k):E.V.t * int) (l:E.literal) : bool =
  let same (v1,k1) (v2,k2) = (E.V.same_var v1 v2) && (k1=k2) in
  match l with
    (* v=k -> v2=k2 *)
    F.Atom(E.Eq(E.VarT(v2),E.IntT(E.IntVal k2)))            -> 
      (E.V.sort v2)==E.Int && same (v,k) (v2,k2)
  |  (* v=k -> v2=k2 *)
      F.Atom(E.Eq(E.IntT(E.VarInt(v2)),E.IntT(E.IntVal k2)))  -> 
    same (v,k) (v2,k2)
  | (* v=k -> k2=v2 *)
      F.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.VarT(v2)))           -> 
    (E.V.sort v2)==E.Int && same (v,k) (v2,k2)
  | (* v=k -> k2=v2 *)
      F.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.IntT(E.VarInt(v2)))) -> 
    same (v,k) (v2,k2)
  | (* v=k -> k2<v2 *)
      F.Atom(E.Less(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.V.same_var v v2) && (k > k2)
  | (* v=k -> v2>k2 *)
      F.Atom(E.Greater(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.V.same_var v v2) && (k > k2)
  | (* v=k -> v2<k2 *)
      F.Atom(E.Less(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.V.same_var v v2) && (k < k2)
  | (* v=k -> k2>v2 *)
      F.Atom(E.Greater(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.V.same_var v v2) && (k < k2)
  | (* v=k -> k2<=v2 *)
      F.Atom(E.LessEq(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.V.same_var v v2) && (k >= k2)
  | (* v=k -> v2>=k2 *)
      F.Atom(E.GreaterEq(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.V.same_var v v2) && (k >= k2)
  | (* v=k -> v2<=k2 *)
      F.Atom(E.LessEq(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.V.same_var v v2) && (k <= k2)
  | (* v=k -> k2>=v2 *)
      F.Atom(E.GreaterEq(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.V.same_var v v2) && (k <= k2)
  | _ -> false

let integer_implies_neg ((v,k):E.V.t * int) (l:E.literal) : bool =
  (* let same (v1,k1) (v2,k2) = (E.V.same_var v1 v2) && (k1=k2) in *)
  match l with
    (* v=k -> v2=k2 *)
    F.Atom(E.Eq(E.VarT(v2),E.IntT(E.IntVal k2)))            ->
      (E.V.sort v2)==E.Int && E.V.same_var v v2 && k!=k2
  |  (* v=k -> v2=k2 *)
      F.Atom(E.Eq(E.IntT(E.VarInt(v2)),E.IntT(E.IntVal k2)))  ->
      E.V.same_var v v2 && k!=k2
  | (* v=k -> k2=v2 *)
      F.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.VarT(v2)))           ->
      (E.V.sort v2)==E.Int && E.V.same_var v v2 && k!=k2
  | (* v=k -> k2=v2 *)
      F.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.IntT(E.VarInt(v2)))) ->
      E.V.same_var v v2 && k!=k2
  | (* v=k -> k2<v2 *)
      F.Atom(E.Less(E.IntVal(k2),E.VarInt(v2))) -> (E.V.same_var v v2) && not (k > k2)
  | (* v=k -> v2>k2 *)
      F.Atom(E.Greater(E.VarInt(v2),E.IntVal(k2))) -> (E.V.same_var v v2) && not (k > k2)
  | (* v=k -> v2<k2 *)
      F.Atom(E.Less(E.VarInt(v2),E.IntVal(k2))) -> (E.V.same_var v v2) && not (k < k2)
  | (* v=k -> k2>v2 *)
      F.Atom(E.Greater(E.IntVal(k2),E.VarInt(v2))) -> (E.V.same_var v v2) && not (k < k2)
  | (* v=k -> k2<=v2 *)
      F.Atom(E.LessEq(E.IntVal(k2),E.VarInt(v2))) -> (E.V.same_var v v2) && not (k >= k2)
  | (* v=k -> v2>=k2 *)
      F.Atom(E.GreaterEq(E.VarInt(v2),E.IntVal(k2))) -> (E.V.same_var v v2) && not (k >= k2)
  | (* v=k -> v2<=k2 *)
      F.Atom(E.LessEq(E.VarInt(v2),E.IntVal(k2))) -> (E.V.same_var v v2) && not (k <= k2)
  | (* v=k -> k2>=v2 *)
      F.Atom(E.GreaterEq(E.IntVal(k2),E.VarInt(v2))) -> (E.V.same_var v v2) && not 
  (k <= k2)
  | _ -> false

(* tactic_simplify_pc: *)
(*    discovers all facts of the form v=k and propagates them *)
(* ALE: Idea, apply recursively until no more facts are discovered. *)
(* ALE: perhaps optionally append back facts to the antecedent. *)
let tactic_simplify_pc (imp:implication) : implication =
  (* 1. Search for facts of the form "pc = k" or "k = pc" *)
  Log.print_ocaml "entering tactic_simplify_pc";
  Log.print "simplify_pc antecedent" (E.formula_to_str imp.ante);
  Log.print "simplify_pc consequent" (E.formula_to_str imp.conseq);

  let get_integer_literals (f:E.formula) : ((E.V.t * int) list * bool) =
    let facts = Hashtbl.create 10 in
    let contradiction = ref false in
    let try_to_store (v:E.V.t) (i:int) : unit =
      try
        let prev = Hashtbl.find facts v in
        if prev <> i then contradiction := true
      with Not_found -> Hashtbl.add facts v i in
    let rec find (phi:E.formula) : unit =
      match phi with
        F.Literal l -> begin
                         match (extract_pc_integer_eq l) with
                         | Some (v,k) -> try_to_store v k
                         | None       -> ()
                       end
      | F.And(f1,f2)       -> (find f1; find f2)
      | F.Not(F.Or(f1,f2)) -> (find f1; find f2)
      | _                  -> ()
    in
      find f;
      (Hashtbl.fold (fun v i xs -> (v,i)::xs) facts [], !contradiction)
  in
  (* DEBUG *)
  let print_all facts =
    Log.print "" "Found pc facts:";
    let str = List.fold_left (fun s (v,k) -> s ^ (sprintf "(%s=%d)" (E.V.to_str v) k )) "" facts in
    Log.print "" str
  in
  (* 2. Simplify the antecedent and the consequent with the facts *)
  let (facts, contradiction) = get_integer_literals imp.ante in
  let _ = print_all facts in
  let new_ante  = if contradiction then
                    F.False
                  else
                    simplify (generic_simplify_with_many_facts facts
                                integer_implies integer_implies_neg imp.ante) in
  let new_conseq = simplify (generic_simplify_with_many_facts facts integer_implies integer_implies_neg imp.conseq) in
  Log.print "simplify_pc new antecedent" (E.formula_to_str new_ante);
  Log.print "simplify_pc new consequent" (E.formula_to_str new_conseq);
  (* 3. Propagate propositional, if new facts are stated,
        by calling propositional_propagate *)
  tactic_propositional_propagate { ante = new_ante; conseq = new_conseq }



(* tactic_simplify_pc_plus: *)
(* Checks the consequent. If the consequent is an implication whose
   antecedent is based on a condition over the program counter of a thread,
   then it simplifies the antecedent of the formula, removing unnecessary
   assumptions *)
let tactic_simplify_pc_plus (imp:implication) : implication =
  (* Apply simplify_pc by default *)
  let imp = tactic_simplify_pc imp in
  (* 1. search for facts of the form "pc = k" or "k = pc" in the consequent *)
  let fact =
    match imp.conseq with
    | F.Implies(F.Literal(F.Atom(E.Eq(E.VarT v,E.IntT(E.IntVal k)))), _)
    | F.Implies(F.Literal(F.Atom(E.Eq(E.IntT(E.IntVal k),E.VarT v))), _)
    | F.Implies(F.Literal(F.Atom(E.Eq(E.IntT(E.VarInt v),E.IntT(E.IntVal k)))), _)
    | F.Implies(F.Literal(F.Atom(E.Eq(E.IntT(E.IntVal k),E.IntT(E.VarInt v)))), _) ->
        if E.is_pc_var v then Some (v,k,k) else None
    | F.Implies(F.And(F.Literal(F.Atom(E.LessEq(E.IntVal n,E.VarInt v1))),
                      F.Literal(F.Atom(E.LessEq(E.VarInt v2,E.IntVal m)))),_) ->
        if v1 = v2 && E.is_pc_var v1 then Some (v1,n,m) else None
    | _ -> None in
  (* 2. if there is some fact, then remove useless implications from the antecedent *)
  match fact with
  | None -> imp
  | Some (w,i,j) ->
      begin
        let new_ante =
          F.conj_list
            ( List.fold_left (fun xs phi ->
              match phi with
              | F.Implies(F.Literal(F.Atom(E.Eq(E.VarT v,E.IntT(E.IntVal k)))), _)
              | F.Implies(F.Literal(F.Atom(E.Eq(E.IntT(E.IntVal k),E.VarT v))), _)
              | F.Implies(F.Literal(F.Atom(E.Eq(E.IntT(E.VarInt v),E.IntT(E.IntVal k)))), _)
              | F.Implies(F.Literal(F.Atom(E.Eq(E.IntT(E.IntVal k),E.IntT(E.VarInt v)))), _) ->
                  if v = w && (k < i || j < k) then xs else phi::xs
              | F.Implies(F.And(F.Literal(F.Atom(E.LessEq(E.IntVal n,E.VarInt v1))),
                                F.Literal(F.Atom(E.LessEq(E.VarInt v2,E.IntVal m)))),_) ->
                  if v1 = v2 && v1 = w && (m < i || j < n) then xs else phi::xs
              | _ -> phi::xs
            ) [] (F.to_conj_list imp.ante)) in
        { ante = new_ante; conseq = imp.conseq; }
      end


(* eliminate from the antecedent all literals without variables in common
   with the goal *)
let tactic_filter_vars_nonrec (criteria:filter_criteria_t) (imp:implication) : implication =
  let vs_conseq = E.all_vars_as_set imp.conseq in

  let filtered_vs_conseq =
    match criteria with
    | NoCriteria -> vs_conseq
    | AllExceptHeap
    | LocalOnly
    | MallocCrit -> E.V.VarSet.filter (fun v -> E.V.id v <> Conf.heap_name) vs_conseq in
  let conjs = F.to_conj_list imp.ante in
  let share_vars (vl: E.V.t list) : bool =
    match criteria with
    | LocalOnly -> List.exists (fun v ->
                     E.V.parameter v = E.V.Shared ||
                     E.V.VarSet.mem v filtered_vs_conseq
                   ) vl
    | NoCriteria
    | AllExceptHeap ->
        List.exists (fun v -> E.V.VarSet.mem v filtered_vs_conseq) vl
    | MallocCrit ->
        (not (List.mem Bridge.fresh_addr vl)) ||
         List.exists (fun v -> E.V.VarSet.mem v filtered_vs_conseq) vl
  in
  let new_conjs = List.filter (fun f -> share_vars (E.all_vars f)) conjs in
  { ante = F.conj_list new_conjs ; conseq = imp.conseq }


(*************************************)
(* TACTIC FILTER_THEORY : UNFINISHED *)
(*************************************)
let tactic_filter_theory (imp:implication) : implication =
  imp


let is_literal (f:E.formula) : bool =
  match f with  
    F.Literal _ -> true  
  | _           -> false


let neg_literal (l:E.literal) : E.literal =
  match l with 
    F.Atom(a)    -> F.NegAtom(a)
  | F.NegAtom(a) -> F.Atom(a)



let apply_literal_to_implication (l:E.literal) (ante:E.formula) (conseq:E.formula) : implication =
  let implies     = E.identical_literal in
  let implies_neg = E.opposite_literal in
  { ante   = (F.And((simplify_with_fact l implies implies_neg ante), F.Literal l));
    conseq = (simplify_with_fact l implies implies_neg conseq) }

let tactic_conseq_propagate_second_disjunct (imp:implication) : implication =
  match imp.conseq with
    F.Or(a ,F.Literal l) -> 
      apply_literal_to_implication (neg_literal l) imp.ante a
  | F.Implies(a, F.Literal l) ->
      apply_literal_to_implication (neg_literal l) imp.ante (F.Not a)
  | _ -> { ante = imp.ante; conseq = imp.conseq }
    

let tactic_conseq_propagate_first_disjunct (imp:implication) : implication =
  match imp.conseq with
    F.Or(F.Literal l, b) -> 
      apply_literal_to_implication (neg_literal l) imp.ante b
  | F.Implies(F.Literal l,b) ->
    apply_literal_to_implication l imp.ante b
  | _ -> 
    { ante = imp.ante; conseq = imp.conseq }



(**************************************************************************)
(* APPLICATION OF TACTICS                                                 *)
(**************************************************************************)

let unify_support (vc:vc_info) : vc_info =
  let unify_tbl : (int, (E.tid list * E.formula) list) Hashtbl.t = Hashtbl.create 4 in
  List.iter (fun phi ->
    let this_voc = E.ThreadSet.elements (E.voc phi) in
    let this_voc_size = List.length this_voc in
    try
      Hashtbl.replace unify_tbl this_voc_size
        ((this_voc,phi)::(Hashtbl.find unify_tbl this_voc_size))
    with Not_found ->
      Hashtbl.add unify_tbl this_voc_size [(this_voc, phi)]
  ) vc.original_support;
  let new_supp = Hashtbl.fold (fun _ phi_list xs ->
                   match phi_list with
                   | [] -> assert false
                   | [(_,phi)] -> phi :: xs
                   | (voc,phi)::ys -> F.conj_list (phi ::
                                      (List.map (fun (v,f) ->
                                         let subs = E.new_tid_subst (List.combine v voc) in
                                         E.subst_tid subs f
                                       ) ys)) :: xs
                 ) unify_tbl [] in
  dup_vc_info_with_support vc new_supp



let apply_support_split_tactics (vcs:vc_info list)
                                (tacs:support_split_tactic_t list)
                                  : vc_info list =
  List.fold_left (fun ps f -> List.flatten (List.map f ps)) vcs tacs


let apply_support_tactic (vcs:vc_info list)
                         (tac:support_tactic_t option)
                            : implication list =
  let rec build_ineqs (parts:E.tid list list) : (E.tid * E.tid) list =
    match parts with
    | [] -> []
    | _::[] -> []
    | eqc::xs -> begin
                   let i = List.hd eqc in
                   (List.map (fun ys -> (i, List.hd ys)) xs) @ (build_ineqs xs)
                 end in



  let process_supp (this_vc:vc_info) : support_t =
    match tac with
    | None -> get_unprocessed_support_from_info this_vc
    | Some (f,_) -> f this_vc in

  List.fold_left (fun imps vc ->
    let goal_voc = E.voc vc.original_goal in
    let requires_tid_propagation = (E.ThreadSet.cardinal goal_voc) > 1 in
    (* If necessary, from a vc_info we create multiple vc_info following equalities of
        thread ids parametrizing the goal *)

    let vc_cases =
      begin
        if requires_tid_propagation then begin
          let parts = Partition.gen_partitions (E.ThreadSet.elements goal_voc) [] in
          List.map (fun part ->
            let eq_classes = Partition.to_list part in
            let eq_pairs = List.fold_left (fun xs eq_class ->
                             if List.mem vc.transition_tid eq_class then
                               (List.map (fun j -> (j,vc.transition_tid)) eq_class) @ xs
                             else
                               let i = List.hd eq_class in
                               (List.map (fun j -> (j, i)) (List.tl eq_class)) @ xs
                               ) [] eq_classes in
            let subst = E.new_tid_subst eq_pairs in
            let subst_goal = E.subst_tid subst vc.goal in
            let tid_ineqs = build_ineqs eq_classes in
            let new_support = List.map (E.subst_tid subst) (process_supp vc) in
            let new_rho = E.subst_tid subst vc.rho in
            let new_constr = { eq   = vc.tid_constraint.eq @ eq_pairs;
                               ineq = vc.tid_constraint.ineq @ tid_ineqs;} in
            (dup_vc_info_with_supp_constr_rho_and_goal
                vc new_support new_constr new_rho subst_goal, new_support)
          ) parts
        end else begin

          match tac with
          | None
          | Some (_, DefaultSupport) -> [(vc, process_supp vc)]
          | Some (_, FilterSupport) ->
              begin

                let vs = E.V.VarSet.union (E.all_vars_as_set vc.rho)
                                          (E.all_vars_as_set vc.goal) in 
                let filtered_vs = E.V.VarSet.filter (fun v ->
                                     E.V.sort v <> E.Tid
                                  ) vs in

                let supp_conjs = List.fold_left (fun xs phi ->
                                   (F.to_conj_list phi) @ xs
                                 ) [] (process_supp vc) in
            
                let share_vars (vl: E.V.t list) : bool =
                  List.for_all (fun v ->
                    (E.V.VarSet.mem v filtered_vs) ||
                    (E.V.parameter v = E.V.Shared)
                  ) vl in

                let new_supp = List.filter (fun f ->
                                 share_vars (E.all_vars f)
                               ) supp_conjs in

                let new_vc = dup_vc_info_with_support vc new_supp in
                [(new_vc, new_supp)]
              end
        end
      end in
    (List.map (fun (vc_case, supp) ->
      (vc_info_to_implication vc_case supp)
     ) vc_cases) @ imps
  ) [] vcs


let gen_eq_prop_from_list (conjs:E.formula list) : (E.formula list * E.V.subst_t) =
  let build_subst (vs:E.V.t list list) : E.V.subst_t =
    let sub_pairs =
      List.fold_left (fun slist xs ->
        if (List.length xs > 1) then
          let (fs, nfs) = List.partition E.V.is_fresh xs in
          let concat = nfs @ fs in
          let h = List.hd concat in
          (List.map (fun v -> (v,h)) (List.tl concat)) @ slist
        else
          slist
      ) [] vs in
    E.V.new_subst_from_list sub_pairs in
  let uf = UF.empty() in
  let conjs' =
    List.fold_left (fun xs conj->
      (* print_endline ("CONSIDERING CONJUNCTION: " ^ (E.formula_to_str conj)); *)
      match conj with
      | F.Literal(F.Atom (E.Eq(t1, t2))) ->
          begin
            if (E.term_is_var t1 && E.term_is_var t2) then begin
              let v1 = E.term_to_var t1 in
              let v2 = E.term_to_var t2 in
              if (E.V.is_primed v1 || E.V.is_primed v2) then
                conj :: xs
              else begin
                UF.union uf (E.term_to_var t1) (E.term_to_var t2);
                xs
              end
            end else                         
              conj :: xs
          end
      | _ -> conj :: xs
    ) [] conjs in
  (conjs', build_subst (UF.to_list uf))


let gen_eq_propagation (phi:E.formula) : (E.formula * E.V.subst_t) =
  let (conjs, subst) = gen_eq_prop_from_list (F.to_conj_list phi) in
  (F.conj_list conjs, subst)


let apply_eq_propagation (imps:implication list) : implication list =
  let eq_prop (imp:implication) : implication =
    let (ante',subst) = gen_eq_propagation imp.ante in
    { ante = E.subst_vars subst ante';
      conseq = E.subst_vars subst imp.conseq; }
  in
    List.map eq_prop imps


let apply_formula_split_tactics (imps:implication list)
                                (tacs:formula_split_tactic_t list)
                                  : implication list =
  List.fold_left (fun ps f -> List.flatten (List.map f ps)) imps tacs


let apply_formula_tactics (imps:implication list)
                          (tacs:formula_tactic_t list)
                            : implication list =
  List.fold_left (fun ps f -> List.map f ps) imps tacs


let apply_tactics (vcs:vc_info list)
                  (supp_split_tacs:support_split_tactic_t list)
                  (supp_tac:support_tactic_t option)
                  (formula_split_tacs:formula_split_tactic_t list)
                  (formula_tacs:formula_tactic_t list)
                    : E.formula list =
  Log.print_ocaml "entering apply_tactics()";
  List.fold_left (fun phi_list vc ->
    let split_vc_info_list = apply_support_split_tactics [vc] supp_split_tacs in
    let original_implications = apply_support_tactic split_vc_info_list supp_tac in
    let propagated_implications = apply_eq_propagation original_implications in
    let split_implications = apply_formula_split_tactics propagated_implications formula_split_tacs in
    let final_implications = apply_formula_tactics split_implications formula_tacs in
    Log.print "* From this vc_info" (vc_info_to_str vc);
    Log.print "* Leap generated the following formulas" "";
    let final_formulas = List.map (fun imp ->
                           let phi = F.Implies (imp.ante, imp.conseq) in phi
                           (* Log.print "" (E.formula_to_str phi); phi *)
                         ) final_implications in

    phi_list @ final_formulas
  ) [] vcs


let apply_tactics_from_proof_plan (vcs:vc_info list)
                                  (plan:proof_plan) : E.formula list =
  let support_tac = match plan.support_tactics with
                    | [] -> None
                    | xs  -> Some (List.hd xs) in
  apply_tactics vcs plan.support_split_tactics
                    support_tac
                    plan.formula_split_tactics
                    plan.formula_tactics



(***************************************************************)
(*            CONVERTERS FORM STRING TO TACTICS                *)
(***************************************************************)

let support_split_tactic_from_string (s:string) : support_split_tactic_t =
  match s with
  | "split-goal" -> split_goal
  | _ -> raise(Invalid_tactic (s ^ " is not a support_split_tactic"))


let support_tactic_from_string (s:string) : support_tactic_t =
  match s with
  | "full"                -> (full_support, DefaultSupport)
  | "full-and-filter"     -> (full_support, FilterSupport)
  | "reduce"              -> (reduce_support, DefaultSupport)
  | "reduce-and-filter"   -> (reduce_support, FilterSupport)
  | "reduce2"             -> (reduce2_support, DefaultSupport)
  | "reduce2-and-filter"  -> (reduce2_support, FilterSupport)
  | "identity"            -> (id_support, DefaultSupport)
  | "identity-and-filter" -> (id_support, FilterSupport)
  | "self"                -> (self_support, DefaultSupport)
  | "self-and-filter"     -> (self_support, FilterSupport)
  | _ -> raise(Invalid_tactic (s ^ " is not a support_tactic"))


let formula_split_tactic_from_string (s:string): formula_split_tactic_t =
  match s with
  | "split-consequent"        -> split_implication
  | "split-antecedent-pc"     -> split_antecedent_pc
  | _ -> raise(Invalid_tactic (s ^ "is not a formula_split_tactic"))


let formula_tactic_from_string (s:string) : formula_tactic_t =
  match s with
  | "simplify-pc"               -> tactic_simplify_pc
  | "simplify-pc-plus"          -> tactic_simplify_pc_plus
  | "propositional-propagate"   -> tactic_propositional_propagate
  | "filter-strict"             -> tactic_filter_vars_nonrec NoCriteria
  | "filter-strict-local"       -> tactic_filter_vars_nonrec LocalOnly
  | "filter-strict-except-heap" -> tactic_filter_vars_nonrec AllExceptHeap
  | "filter-malloc"             -> tactic_filter_vars_nonrec MallocCrit
  | "filter-theory"             -> tactic_filter_theory
  | "propagate-disj-conseq-fst" -> tactic_conseq_propagate_first_disjunct
  | "propagate-disj-conseq-snd" -> tactic_conseq_propagate_second_disjunct
  | _ -> raise(Invalid_tactic (s ^ " is not a formula_tactic"))
