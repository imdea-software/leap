open LeapLib
open Printf

module E = Expression
module GenSet = LeapGenericSet

type polarity = Pos | Neg | Both


type support_t = E.formula list
type vc_info = { 
  original_support : support_t ; (* BOXED formulas, tids must be renamed *)
  tid_constraint   : E.formula      ;
  
  rho             : E.formula ;   (* TRANSITION RELATION *)

  original_goal   : E.formula  ;
  goal            : E.formula  ;
  transition_tid  : E.tid      ;
  line            : E.pc_t     ;
  vocabulary      : E.tid list ; (* MAY GO *)
}


type verification_condition = {
  antecedent : E.formula ;

  consequent : E.formula ;

  support         : support_t ; 
                                (* this is the support computed
           using some tactic, including 
                                   exhaustive brute force *)
  info            : vc_info   ;
}


type implication = {
  ante : E.formula ;
  conseq : E.formula ;
}


type support_split_tactic_t = vc_info -> vc_info list
type support_tactic_t = vc_info -> support_t
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
  | RestrictSubst of (E.tid_subst_t -> bool)
      (* Restricts assignments to the ones satisfies by the given function *)
  



(***********************)
(* CONSTRUCTORS        *)
(***********************)

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
 
let vc_info_to_implication (info:vc_info) (sup:support_t): implication =
  let the_antecedent =
    E.conj_list (sup @ [ info.tid_constraint ] @ [info.rho]) in
  let consequent = E.prime_modified info.rho info.goal in
  { ante = the_antecedent ; conseq = consequent }

let vc_info_to_formula  (info:vc_info) (sup:support_t): E.formula =
  let implication = vc_info_to_implication info sup in
  E.Implies (implication.ante, implication.conseq)


let vc_info_to_vc (info:vc_info) (sup:support_t): verification_condition =
  let implication = vc_info_to_implication info sup in
  { 
    info       = info                ;
    support    = sup                 ;
    antecedent = implication.ante    ; 
    consequent = implication.conseq  ; 
  }

exception Invalid_tactic of string

let default_cutoff_algorithm = Smp.Dnf


let vc_info_to_str (vc:vc_info) : string =
  let to_fol = E.to_fol_formula E.PCVars in
  let fol_tid_constraint = to_fol vc.tid_constraint in
  let fol_rho = to_fol vc.rho in
  let fol_goal = to_fol vc.goal in
  let fol_supp = List.map to_fol vc.original_support in

  let vars_to_declare = E.all_vars (E.conj_list (fol_tid_constraint ::
                                                 fol_rho            ::
                                                 fol_goal           ::
                                                 fol_supp)) in

  let vars_str = (String.concat "\n"
                   (List.map (fun v ->
                     (E.sort_to_str (E.var_sort v)) ^ " " ^
                     (E.variable_to_str v)
                   ) vars_to_declare)) in
  let supp_str = String.concat "\n" (List.map E.formula_to_str fol_supp) in
  let tidconst_str = E.formula_to_str fol_tid_constraint in
  let rho_str = E.formula_to_str fol_rho in
  let goal_str = E.formula_to_str fol_goal in
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
    Pervasives.output_string out_ch (vc_info_to_str vc_info);
    Pervasives.close_out out_ch
  ) vcs


let create_vc_info (supp       : support_t)
                   (tid_constr : E.formula)
                   (rho        : E.formula)
                   (goal       : E.formula)
                   (vocab      : E.tid list)
                   (trans_tid  : E.tid)
                   (line       : E.pc_t) : vc_info =
    {
      original_support   = supp ;
      tid_constraint     = tid_constr ;
      rho                = rho ;
      original_goal      = goal ;
      goal               = E.prime_modified rho goal ;
      transition_tid     = trans_tid ;
      line               = line ;
      vocabulary         = vocab ; (* fix: can be computed *)
    }


let to_fol_vc_info (fol_mode:E.fol_mode_t) (info:vc_info) : vc_info =
  let f = E.to_fol_formula fol_mode in
  {
    original_support = List.map f info.original_support;
    tid_constraint = f info.tid_constraint;
    rho = f info.rho;
    original_goal = f info.original_goal;
    goal = f info.goal;
    transition_tid = info.transition_tid;
    line = info.line;
    vocabulary = info.vocabulary;
  }


let create_vc (orig_supp       : support_t)
              (tid_constr : E.formula)
              (rho        : E.formula)
              (goal       : E.formula)
              (vocab      : E.tid list)
              (trans_tid  : E.tid)
              (line       : E.pc_t) 
        (support    : support_t)
        : verification_condition =
  vc_info_to_vc (create_vc_info orig_supp tid_constr rho goal vocab trans_tid line) support


let dup_vc_info_with_goal (info:vc_info) (new_goal:E.formula) : vc_info =
  {
    original_support   = info.original_support ;
    tid_constraint = info.tid_constraint;
    rho            = info.rho ;
    original_goal  = info.original_goal ;
    goal           = new_goal ;
    transition_tid = info.transition_tid ;
    line           = info.line ;
    vocabulary     = info.vocabulary ; (* FIX need recompute *)
  }



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


let get_unprocessed_support_from_info (info:vc_info) : support_t =
  info.original_support
and get_tid_constraint_from_info (info:vc_info) : E.formula = info.tid_constraint
and get_vocabulary_from_info (info:vc_info) : E.tid list    =  info.vocabulary
and get_rho_from_info (info:vc_info) : E.formula =  info.rho
and get_goal_from_info (info:vc_info) : E.formula =  info.goal
and get_transition_tid_from_info (info:vc_info) : E.tid =  info.transition_tid
and get_line_from_info (info:vc_info) : E.pc_t =  info.line


let rec get_antecedent (vc:verification_condition) : E.formula=
  vc.antecedent
and get_consequent (vc:verification_condition) : E.formula=
  vc.consequent
and get_support (vc:verification_condition) : support_t =
  vc.support
and get_unprocessed_support (vc:verification_condition) : support_t =
  get_unprocessed_support_from_info vc.info
and get_tid_constraint (vc:verification_condition) : E.formula =
  get_tid_constraint_from_info vc.info
and get_rho (vc:verification_condition) : E.formula =
  get_rho_from_info vc.info
and get_goal (vc:verification_condition) : E.formula =
  get_goal_from_info vc.info
and get_transition_tid (vc:verification_condition) : E.tid =
  get_transition_tid_from_info vc.info
and get_line (vc:verification_condition) : E.pc_t =
  get_line_from_info vc.info
and get_vocabulary (vc:verification_condition) : E.tid list =
  get_vocabulary_from_info vc.info




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
  let is_true  (f:E.formula):bool = match f with E.True  -> true | _ -> false in
  let is_false (f:E.formula):bool = match f with E.False -> true | _ -> false in
  let rec simplify_f (f:E.formula) (pol:polarity): E.formula=
    match f with
        E.Literal(lit) -> (simp_lit lit pol)
      | E.True         -> E.True
      | E.False        -> E.False
      | E.And(x,y)     -> let sx = (simplify_f x pol) in
                          let sy = (simplify_f y pol) in
                            if (is_false sx || is_false sy) then E.False
                            else if (is_true sx && is_true sy) then E.True
                            else if (is_true sx) then sy
                            else if (is_true sy) then sx
                            else E.And(sx,sy)
      | E.Or(x,y)      -> let sx = (simplify_f x pol) in
                          let sy = (simplify_f y pol) in
                            if (is_true sx || is_true sy) then E.True
                            else if (is_false sx && is_false sy) then E.False
                            else if (is_false sx ) then sy
                            else if (is_false sy ) then sx
                            else E.Or(sx,sy)
      | E.Not(x)       -> let sx = (simplify_f x (invert_polarity pol)) in
                            if (is_true sx) then E.False
                            else if(is_false sx) then E.True
                            else E.Not(sx)
      | E.Implies(x,y) -> let sx = (simplify_f x (invert_polarity pol)) in
                          let sy = (simplify_f y pol) in
                            if (is_false sx || is_true sy) then E.True
                            else if (is_true sx) then sy
                            else if (is_false sy) then E.Not(sx)
                            else E.Implies(sx,sy)
      | E.Iff(x,y)     -> let sx = (simplify_f x Both) in
                          let sy = (simplify_f y Both) in
                            if (is_false sx && is_false sy) then E.True
                            else if (is_true sx && is_true sy) then E.True
                            else if (is_true sx) then sy
                            else if (is_true sy) then sx
                            else if (is_false sx) then E.Not(sy)
                            else if (is_false sy) then E.Not(sx)
                            else E.Iff(sx,sy)
  in
    simplify_f phi Pos

let simplify (phi:E.formula) : E.formula =
  let id l pol = E.Literal l in
    generic_simplifier phi id


(* let simplify_with_pc (phi:E.formula) (i:E.tid) (lines:int list) (primed:bool) : E.formula = *)
(*   let is_same_tid (j:E.tid) : bool = *)
(*     match (i,j) with *)
(*       E.VarTh(v),E.VarTh(w) -> E.same_var v w *)
(*     | _                     -> false in *)
(*   let matches_tid (a:E.atom) : bool = *)
(*     match a with *)
(*       E.PC(line,E.Local j,pr)       -> is_same_tid j *)
(*     | E.PCRange(l1,l2,E.Local j,pr) -> is_same_tid j *)
(*     | _                             -> false in *)
(*   let matches_line (a:E.atom) : bool = *)
(*     match a with *)
(*       E.PC(l,E.Local j,pr)       -> List.mem l lines *)
(*     | E.PCRange(l1,l2,E.Local j,pr) -> List.exists (fun l -> l1<= l && l <= l2) lines *)
(*     | _                              -> false in *)
(*   let simplify_pc (lit:E.literal) (pol:polarity) : E.formula = *)
(*     match lit with *)
(*       E.Atom(a)    -> if (matches_tid a) then *)
(*                         (if (matches_line a) then E.True else E.False) *)
(*                       else *)
(*                           E.Literal lit *)
(*     | E.NegAtom(a) -> if (matches_tid a) then *)
(*                         (if (matches_line a) then E.False else E.True) *)
(*                         else *)
(*                           E.Literal lit *)
(*   in *)
(*   generic_simplifier phi simplify_pc *)


(* simplify_with_vocabulary: simply removes the whole formula if the vocabulary
 *                           is irrelevant *)
let simplify_with_vocabulary (phi:E.formula) (vocabulary:E.variable list): E.formula =
  let vars_in_phi = E.all_vars_as_set phi in
  let relevant = List.exists (fun v -> E.VarSet.mem v vars_in_phi) vocabulary in
    if relevant then
      phi
    else
      E.True


(**************************************************************************)
(* SUPPORT TACTICS, that generate support (E.formula list) from vc_info   *)
(**************************************************************************)
let generate_support (info:vc_info) : E.formula list =
  let (param,no_param) =  
    List.partition (fun phi -> E.voc phi <> []) info.original_support in
  let target_voc = E.voc (E.And (info.goal, info.rho)) in
  let instantiate_one_support phi =
    let subst = E.new_comb_subst (E.voc phi) target_voc in
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
  let new_conseqs = E.to_conj_list imp.conseq in
  List.map (fun phi -> { ante=imp.ante ; conseq=phi }) new_conseqs


(***************************)
(*  SUPPORT SPLIT TACTICS  *)
(***************************)

let split_goal (info:vc_info) : vc_info list =
  let new_goals = E.to_conj_list info.goal in
  List.map (fun phi -> {
        original_support = info.original_support;
        tid_constraint   = info.tid_constraint  ;
        rho              = info.rho ;
        original_goal    = info.original_goal;
        goal             = phi ;
        transition_tid   = info.transition_tid ;
        line             = info.line ;
        vocabulary       = info.vocabulary ;})
    new_goals
(* aux functions *)
let is_true (f:E.formula) : bool =
  match f with
  E.True -> true
  | _  -> false

let is_false (f:E.formula) : bool =
  match f with
    E.False -> true
  | _     -> false


let rec get_literals f =
  match f with
    E.Literal l  -> [l]
  | E.And(f1,f2)       -> get_literals f1 @ get_literals f2
  | E.Not(E.Or(f1,f2)) -> get_literals f1 @ get_literals f2
  | _          -> []


(* simplify_with_fact: takes the given literal as a fact, and removes all
                         instances of identical literals in the formula for true *)
let generic_simplify_with_fact (fact:'a)
    (implies:'a -> E.literal -> bool)
    (implies_neg:'a -> E.literal -> bool)
    (phi:E.formula): E.formula =
  let rec simplify_lit f = 
    match f with
      E.Literal l -> 
  if      (implies fact l)     then E.True 
  else if (implies_neg fact l) then E.False
  else f
    | E.True        -> E.True
    | E.False       -> E.False
    | E.And(f1, f2) -> E.And(simplify_lit f1, simplify_lit f2)
    | E.Or (f1, f2) -> E.Or (simplify_lit f1, simplify_lit f2)
    | E.Not f       -> E.Not(simplify_lit f)
    | E.Implies(f1,f2) -> E.Implies (simplify_lit f1, simplify_lit f2)
    | E.Iff    (f1,f2) -> E.Iff (simplify_lit f1, simplify_lit f2)
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
    | E.Literal l -> begin
                       if List.exists (fun p -> implies p l) facts then
                         let str = "** simplifying " ^ (E.literal_to_str l) ^ " with true" in
                         let _   = print_endline str in
                         E.True
                       else if List.exists (fun p -> implies_not p l) facts then
                         let str = "** simplifying " ^ (E.literal_to_str l) ^ " with false" in
                         let _   = print_endline str in
                         E.False
                       else
                         E.Literal l
                     end
    | E.True           -> E.True
    | E.False          -> E.False
    | E.And(f1,f2)     -> E.And(simplify_lit f1, simplify_lit f2)
    | E.Or (f1,f2)     -> E.Or (simplify_lit f1, simplify_lit f2)
    | E.Not f          -> E.Not(simplify_lit f)
    | E.Implies(f1,f2) -> E.Implies (simplify_lit f1, simplify_lit f2)
    | E.Iff    (f1,f2) -> E.Iff (simplify_lit f1, simplify_lit f2)
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
  match op with
  | KeepOriginal -> info.original_support
  | RestrictSubst f ->
      let goal_voc = E.voc info.goal in
      let used_tids = ref (E.voc info.tid_constraint @ E.voc info.rho @ goal_voc) in
      let fresh_original_support = List.map (fun supp ->
                                     let supp_voc = E.voc supp in
                                     let fresh_tids = E.gen_fresh_tid_list !used_tids (List.length supp_voc) in
                                     let fresh_subst = E.new_tid_subst (List.combine supp_voc fresh_tids) in
                                     used_tids := !used_tids @ fresh_tids;
                                       E.subst_tid fresh_subst supp
                                   ) info.original_support in
      let split_support = List.fold_left (fun xs phi ->
                            E.to_conj_list phi @ xs
                          ) [] fresh_original_support in
      let (param_support, unparam_support) = List.partition (fun phi ->
                                              E.voc phi <> []
                                            ) split_support in
    (*
      printf "UNPARAM SUPPORT: %s\n" (String.concat " ; " (List.map E.formula_to_str unparam_support));
      printf "PARAM SUPPORT: %s\n" (String.concat " ; " (List.map E.formula_to_str param_support));
    *)
      List.fold_left (fun xs supp_phi ->
        let supp_voc = E.voc supp_phi in
        let voc_to_consider = if List.mem info.transition_tid goal_voc then
                                supp_voc @ goal_voc
                              else
                                info.transition_tid :: supp_voc @ goal_voc in
        let subst = List.filter f (E.new_comb_subst supp_voc voc_to_consider) in
        xs @ List.map (fun s ->
               E.subst_tid s supp_phi
             ) subst
      ) unparam_support param_support


let full_support (info:vc_info) : support_t =
  gen_support (RestrictSubst (fun _ -> true)) info


let reduce_support (info:vc_info) : support_t =
  gen_support (RestrictSubst (E.subst_codomain_in (E.voc info.rho @ E.voc info.goal))) info


let reduce2_support (info:vc_info) : support_t =
  E.cleanup_dup
    (gen_support (RestrictSubst (E.subst_codomain_in (E.voc info.rho @ E.voc info.goal))) info)


let id_support (info:vc_info) : support_t =
  E.cleanup_dup (gen_support KeepOriginal info)


(*********************)
(*  FORMULA TACTICS  *)
(*********************)
let tactic_propositional_propagate (imp:implication) : implication =
  let implies     = E.identical_literal in
  let implies_neg = E.opposite_literal in
  let rec simplify_propagate (f:implication) (used:E.literal list) : 
      (implication * E.literal list) =
    (* ALE: I have removed from new_facts already learned facts *)
    let new_facts = List.filter (fun x ->
                      not (List.mem x used)
                    ) (get_unrepeated_literals f.ante) in
    
    if List.length new_facts = 0 then (f,used) else
      begin
        let new_conseq = simplify_with_many_facts new_facts implies implies_neg f.conseq in
        let new_ante   = simplify_with_many_facts new_facts implies implies_neg f.ante in
          simplify_propagate { ante = new_ante; conseq = new_conseq } (used @ new_facts)
      end
  in
  let (new_imp,facts) = simplify_propagate imp [] in
  let new_ante = E.cleanup (E.And((E.conj_literals facts), new_imp.ante)) in
  let new_conseq = new_imp.conseq in
  { ante = new_ante ; conseq = new_conseq }


let extract_integer_eq (l:E.literal) : ((E.variable * int) option) =
  match l with
    E.Atom(E.Eq(E.VarT(v),          E.IntT(E.IntVal k))) -> Some (v,k)
  | E.Atom(E.Eq(E.IntT(E.VarInt(v)),E.IntT(E.IntVal k))) -> Some (v,k)
  | E.Atom(E.Eq(E.IntT(E.IntVal(k)),E.VarT(v)))           -> Some (v,k)
  | E.Atom(E.Eq(E.IntT(E.IntVal(k)),E.IntT(E.VarInt(v)))) -> Some (v,k)
  | _  -> None

let integer_implies ((v,k):E.variable * int) (l:E.literal) : bool =
  let same (v1,k1) (v2,k2) = (E.same_var v1 v2) && (k1=k2) in
  match l with
    (* v=k -> v2=k2 *)
    E.Atom(E.Eq(E.VarT(v2),E.IntT(E.IntVal k2)))            -> 
      (E.var_sort v2)==E.Int && same (v,k) (v2,k2)
  |  (* v=k -> v2=k2 *)
      E.Atom(E.Eq(E.IntT(E.VarInt(v2)),E.IntT(E.IntVal k2)))  -> 
    same (v,k) (v2,k2)
  | (* v=k -> k2=v2 *)
      E.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.VarT(v2)))           -> 
    (E.var_sort v2)==E.Int && same (v,k) (v2,k2)
  | (* v=k -> k2=v2 *)
      E.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.IntT(E.VarInt(v2)))) -> 
    same (v,k) (v2,k2)
  | (* v=k -> k2<v2 *)
      E.Atom(E.Less(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.same_var v v2) && (k > k2)
  | (* v=k -> v2>k2 *)
      E.Atom(E.Greater(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.same_var v v2) && (k > k2)
  | (* v=k -> v2<k2 *)
      E.Atom(E.Less(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.same_var v v2) && (k < k2)
  | (* v=k -> k2>v2 *)
      E.Atom(E.Greater(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.same_var v v2) && (k < k2)
  | (* v=k -> k2<=v2 *)
      E.Atom(E.LessEq(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.same_var v v2) && (k >= k2)
  | (* v=k -> v2>=k2 *)
      E.Atom(E.GreaterEq(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.same_var v v2) && (k >= k2)
  | (* v=k -> v2<=k2 *)
      E.Atom(E.LessEq(E.VarInt(v2),E.IntVal(k2))) -> 
    (E.same_var v v2) && (k <= k2)
  | (* v=k -> k2>=v2 *)
      E.Atom(E.GreaterEq(E.IntVal(k2),E.VarInt(v2))) -> 
    (E.same_var v v2) && (k <= k2)
  | _ -> false

let integer_implies_neg ((v,k):E.variable * int) (l:E.literal) : bool =
  let same (v1,k1) (v2,k2) = (E.same_var v1 v2) && (k1=k2) in
  match l with
    (* v=k -> v2=k2 *)
    E.Atom(E.Eq(E.VarT(v2),E.IntT(E.IntVal k2)))            -> 
      (E.var_sort v2)==E.Int && E.same_var v v2 && k!=k2
  |  (* v=k -> v2=k2 *)
      E.Atom(E.Eq(E.IntT(E.VarInt(v2)),E.IntT(E.IntVal k2)))  -> 
    E.same_var v2 v2 && k!=k2
  | (* v=k -> k2=v2 *)
      E.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.VarT(v2)))           -> 
      (E.var_sort v2)==E.Int && E.same_var v v2 && k!=k2
  | (* v=k -> k2=v2 *)
      E.Atom(E.Eq(E.IntT(E.IntVal(k2)),E.IntT(E.VarInt(v2)))) -> 
    E.same_var v v2 && k!=k2
  | (* v=k -> k2<v2 *)
      E.Atom(E.Less(E.IntVal(k2),E.VarInt(v2))) -> (E.same_var v v2) && not (k > k2)
  | (* v=k -> v2>k2 *)
      E.Atom(E.Greater(E.VarInt(v2),E.IntVal(k2))) -> (E.same_var v v2) && not (k > k2)
  | (* v=k -> v2<k2 *)
      E.Atom(E.Less(E.VarInt(v2),E.IntVal(k2))) -> (E.same_var v v2) && not (k < k2)
  | (* v=k -> k2>v2 *)
      E.Atom(E.Greater(E.IntVal(k2),E.VarInt(v2))) -> (E.same_var v v2) && not (k < k2)
  | (* v=k -> k2<=v2 *)
      E.Atom(E.LessEq(E.IntVal(k2),E.VarInt(v2))) -> (E.same_var v v2) && not (k >= k2)
  | (* v=k -> v2>=k2 *)
      E.Atom(E.GreaterEq(E.VarInt(v2),E.IntVal(k2))) -> (E.same_var v v2) && not (k >= k2)
  | (* v=k -> v2<=k2 *)
      E.Atom(E.LessEq(E.VarInt(v2),E.IntVal(k2))) -> (E.same_var v v2) && not (k <= k2)
  | (* v=k -> k2>=v2 *)
      E.Atom(E.GreaterEq(E.IntVal(k2),E.VarInt(v2))) -> (E.same_var v v2) && not (k <= k2)
  | _ -> false

(* tactic_simplify_pc: *)
(*    discovers all facts of the form v=k and propagates them *)
(* TODO : Apply recursively until no more facts are discovered. *)
(* TODO:  perhaps optionally append back facts to the antecedent. *)
let tactic_simplify_pc (imp:implication) : implication =
  (* 1. Search for facts of the form "pc = k" or "k = pc" *)
  let _ = print_endline "tactic_simplify_pc invoked" in
  let rec get_integer_literals (f:E.formula) : ((E.variable * int) list) =
    match f with
      E.Literal l -> begin
  match (extract_integer_eq l) with 
    Some (v,k) -> [(v,k)] 
  | None       -> []
      end
    | E.And(f1,f2)       -> get_integer_literals f1 @ get_integer_literals f2
    | E.Not(E.Or(f1,f2)) -> get_integer_literals f1 @ get_integer_literals f2
    | _                  -> []
  in
  (* DEBUG *)
  let print_all facts = 
    print_endline "Found pc facts:" ;
    let str = 
      List.fold_left (fun s (v,k) -> s ^ (sprintf "(%s=%d)" (E.variable_to_str v) k )) "" facts in
    print_endline str
  in
  (* 2. Simplify the antecedent and the consequent with the facts *)
  let facts     = get_integer_literals imp.ante in
  let _ = print_all facts in
  let new_ante  = simplify (generic_simplify_with_many_facts facts integer_implies integer_implies_neg imp.ante) in
  let new_conseq = simplify (generic_simplify_with_many_facts facts integer_implies integer_implies_neg imp.conseq) in
  (* 3. Propagate propositional, if new facts are stated,
        by calling propositional_propagate *)
  tactic_propositional_propagate { ante = new_ante; conseq = new_conseq }




(* eliminate from the antecedent all literals without variables in common
   with the goal *)
let tactic_filter_vars_nonrec (imp:implication) : implication =
  let vs_conseq = E.all_vars_as_set imp.conseq in
  let conjs = E.to_conj_list imp.ante in
  let share_vars (vl: E.variable list) : bool =
    List.exists (fun v -> E.VarSet.mem v vs_conseq) vl
  in
  let new_conjs = List.filter (fun f -> share_vars (E.all_vars f)) conjs in
  { ante = E.conj_list new_conjs ; conseq = imp.conseq }


(*************************************)
(* TACTIC FILTER_THEORY : UNFINISHED *)
(*************************************)
(* tactic_filter_theory: eliminates from the antecedent all those formulas
      that are not in some theory in the consequent *)
(* type theory = Level | Int | Ord | Array | Cell | Mem | Reach | Set | SetTh | Bridge | Other  *)

(* let get_term_theory (t:E.term) : theory = *)
(*   match t with *)
(*     SetT _ -> Set *)
(*   | ElemT  -> Other *)
(*   | TidT  -> Other *)
(*   | AddrT  -> Mem *)
(*   |  *)

(* let get_atom_theory (a:E.atom) : theory = *)
(*   match a with *)
(*     E.Append  _      -> Reach *)
(*   | E.Reach   _      -> Reach *)
(*   | E.ReachAt _      -> Reach *)
(*   | E.OrdList _      -> Bridge *)
(*   | E.SkipList _     -> Bridge *)
(*   | E.In _           -> Set *)
(*   | E.SubsetEq _     -> Set *)
(*   | E.InTh _         -> SetTh *)
(*   | E.SubsetEqTh _   -> SetTh *)
(*   | E.InInt _        -> Other (\* SetInt? *\) *)
(*   | E.SubseqEqInt _  -> Other *)
(*   | E.InElem _       -> Elem *)
(*   | E.SubsetEqElem _ -> Elem *)
(*   | E.Less _         -> Int (\* or Level *\) *)
(*   | E.Greater _      -> Int *)
(*   | E.LessEq _       -> Int *)
(*   | E.GreaterEq _    -> Int *)
(*   | E.LessTid _      -> Other *)
(*   | E.LessElem _     -> Other *)
(*   | E.GreaterElem _  -> Other *)
(*   | E.Eq             ->  *)
let tactic_filter_theory (imp:implication) : implication =
  imp


let is_literal (f:E.formula) : bool =
  match f with  
    E.Literal _ -> true  
  | _           -> false


let neg_literal (l:E.literal) : E.literal =
  match l with 
    E.Atom(a)    -> E.NegAtom(a)
  | E.NegAtom(a) -> E.Atom(a)



let apply_literal_to_implication (l:E.literal) (ante:E.formula) (conseq:E.formula) : implication =
  let implies     = E.identical_literal in
  let implies_neg = E.opposite_literal in
  { ante   = (E.And((simplify_with_fact l implies implies_neg ante), E.Literal l));
    conseq = (simplify_with_fact l implies implies_neg conseq) }

let tactic_conseq_propagate_second_disjunct (imp:implication) : implication =
  match imp.conseq with
    E.Or(a ,E.Literal l) -> 
      apply_literal_to_implication (neg_literal l) imp.ante a
  | E.Implies(a, E.Literal l) ->
      apply_literal_to_implication (neg_literal l) imp.ante (E.Not a)
  | _ -> { ante = imp.ante; conseq = imp.conseq }
    

let tactic_conseq_propagate_first_disjunct (imp:implication) : implication =
  match imp.conseq with
    E.Or(E.Literal l, b) -> 
      apply_literal_to_implication (neg_literal l) imp.ante b
  | E.Implies(E.Literal l,b) ->
    apply_literal_to_implication l imp.ante b
  | _ -> 
    { ante = imp.ante; conseq = imp.conseq }



(**************************************************************************)
(* APPLICATION OF TACTICS                                                 *)
(**************************************************************************)

let apply_support_split_tactics (vcs:vc_info list)
                                (tacs:support_split_tactic_t list)
                                  : vc_info list =
  List.fold_left (fun ps f -> List.flatten (List.map f ps)) vcs tacs


let apply_support_tactic (vcs:vc_info list)
                         (tac:support_tactic_t option)
                            : implication list =
  List.map (fun vc ->
    let processed_supp = match tac with
                               | None -> get_unprocessed_support_from_info vc
                               | Some f -> f vc in
    vc_info_to_implication vc processed_supp
  ) vcs


let apply_formula_split_tactics (imps:implication list)
                                (tacs:formula_split_tactic_t list)
                                  : implication list =
  List.fold_left (fun ps f -> List.flatten (List.map f ps)) imps tacs


let apply_formula_tactics (imps:implication list)
                          (tacs:formula_tactic_t list)
                            : implication list =
  let res = List.fold_left (fun ps f -> List.map f ps) imps tacs in
  res


let apply_tactics (vcs:vc_info list)
                  (supp_split_tacs:support_split_tactic_t list)
                  (supp_tac:support_tactic_t option)
                  (formula_split_tacs:formula_split_tactic_t list)
                  (formula_tacs:formula_tactic_t list)
                    : E.formula list =
  let split_vc_info_list = apply_support_split_tactics vcs supp_split_tacs in
  let original_implications = apply_support_tactic split_vc_info_list supp_tac in
  let split_implications = apply_formula_split_tactics original_implications formula_split_tacs in
  let final_implications = apply_formula_tactics split_implications formula_tacs in
    List.map (fun imp ->
      E.Implies (imp.ante, imp.conseq)
    ) final_implications


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
  | "full"     -> full_support
  | "reduce"   -> reduce_support
  | "reduce2"  -> reduce2_support
  | "identity" -> id_support
  | _ -> raise(Invalid_tactic (s ^ " is not a support_tactic"))


let formula_split_tactic_from_string (s:string): formula_split_tactic_t =
  match s with
  | "split-consequent"        -> split_implication
  | _ -> raise(Invalid_tactic (s ^ "is not a formula_split_tactic"))


let formula_tactic_from_string (s:string) : formula_tactic_t =
  match s with
  | "simplify-pc"             -> tactic_simplify_pc
  | "propositional-propagate" -> tactic_propositional_propagate
  | "filter-strict"           -> tactic_filter_vars_nonrec
  | "filter-theory"           -> tactic_filter_theory
  | "propagate-disj-conseq-fst" -> tactic_conseq_propagate_first_disjunct
  | "propagate-disj-conseq-snd" -> tactic_conseq_propagate_second_disjunct
  | _ -> raise(Invalid_tactic (s ^ " is not a formula_tactic"))
