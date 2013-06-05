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

type support_tactic = Full | Reduce | Reduce2
type formula_tactic = SimplifyPC | PropositionalPropagate
type formula_split_tactic = SplitConsequent
type solve_tactic = Cases

type support_split_tactic_t = vc_info -> vc_info list
type support_tactic_t = vc_info -> support_t
type formula_split_tactic_t = implication -> implication list
type formula_tactic_t = implication -> implication

type proof_plan =
  {
    cutoff_algorithm : Smp.cutoff_strategy_t option     ;
    solve            : solve_tactic option              ;
    support_split_tactics : support_split_tactic_t list ;
    support_tactics  : support_tactic list              ;
    formula_split_tactics : formula_split_tactic_t list ;
    formula_tactics  : formula_tactic list              ;
  }



(***********************)
(* CONSTRUCTORS        *)
(***********************)

let new_proof_plan (smp:Smp.cutoff_strategy_t option)
                   (solve:solve_tactic option)
                   (supp_split_tacs:support_split_tactic_t list)
                   (supp_tacs:support_tactic list)
                   (formula_split_tacs:formula_split_tactic_t list)
                   (formula_tacs:formula_tactic list) : proof_plan =
  {
    cutoff_algorithm = smp;
    solve = solve;
    support_split_tactics = supp_split_tacs;
    support_tactics = supp_tacs;
    formula_split_tactics = formula_split_tacs;
    formula_tactics = formula_tacs;
  }
 
let vc_info_to_implication (info:vc_info) (sup:support_t): implication =
  let the_antecedent =
    E.conj_list (info.goal::( sup @ [ info.tid_constraint ] @ [info.rho])) in
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

let support_tactic_from_string (s:string) : support_tactic =
  match s with
  | "full"    -> Full
  | "reduce"  -> Reduce
  | "reduce2" -> Reduce2
  | _ -> raise(Invalid_tactic (s ^ "is not a support_tactic"))


let formula_tactic_from_string (s:string) : formula_tactic =
  match s with
  | "simplify-pc"             -> SimplifyPC
  | "propositional-propagate" -> PropositionalPropagate
  | _ -> raise(Invalid_tactic (s ^ "is not a formula_tactic"))


let formula_split_tactic_from_string (s:string): formula_split_tactic =
  match s with
  | "split-consequent"        -> SplitConsequent
  | _ -> raise(Invalid_tactic (s ^ "is not a formula_split_tactic"))


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
      rho            = rho ;
      goal           = goal ;
      transition_tid = trans_tid ;
      line           = line ;
      vocabulary     = vocab ; (* fix: can be computed *)
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
and get_solve (plan:proof_plan)  : solve_tactic option =
  plan.solve
and get_support_tactics (plan:proof_plan) : support_tactic list =
  plan.support_tactics
and get_formula_tactics (plan:proof_plan) : formula_tactic list =
  plan.formula_tactics


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


let simplify_with_pc (phi:E.formula) (i:E.tid) (lines:int list) (primed:bool) : E.formula =
  let is_same_tid (j:E.tid) : bool =
    match (i,j) with
      E.VarTh(v),E.VarTh(w) -> E.same_var v w
    | _                     -> false in
  let matches_tid (a:E.atom) : bool =
    match a with
      E.PC(line,E.Local j,pr)       -> is_same_tid j
    | E.PCRange(l1,l2,E.Local j,pr) -> is_same_tid j
    | _                             -> false in
  let matches_line (a:E.atom) : bool =
    match a with
      E.PC(l,E.Local j,pr)       -> List.mem l lines
    | E.PCRange(l1,l2,E.Local j,pr) -> List.exists (fun l -> l1<= l && l <= l2) lines
    | _                              -> false in
  let simplify_pc (lit:E.literal) (pol:polarity) : E.formula =
    match lit with
      E.Atom(a)    -> if (matches_tid a) then
                        (if (matches_line a) then E.True else E.False)
                      else
                          E.Literal lit
    | E.NegAtom(a) -> if (matches_tid a) then
                        (if (matches_line a) then E.False else E.True)
                        else
                          E.Literal lit
  in
  generic_simplifier phi simplify_pc



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
                        



let split_implication (imp:implication) : implication list =
  let new_conseqs = E.to_conj_list imp.conseq in
  List.map (fun phi -> { ante=imp.ante ; conseq=phi }) new_conseqs


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
let simplify_with_fact (lit:E.literal) (phi:E.formula) : E.formula =
  let rec simplify_lit f = 
    match phi with
      E.Literal l -> if (E.identical_literal l lit) then E.True else phi
    | E.True        -> E.True
    | E.False       -> E.False
    | E.And(f1, f2) -> E.And(simplify_lit f1, simplify_lit f2)
    | E.Or (f1, f2) -> E.Or (simplify_lit f1, simplify_lit f2)
    | E.Not f       -> E.Not(simplify_lit f)
    | E.Implies(f1,f2) -> E.Implies (simplify_lit f1, simplify_lit f2)
    | E.Iff    (f1,f2) -> E.Iff (simplify_lit f1, simplify_lit f2)
  in
  simplify (simplify_lit phi)

let simplify_with_many_facts (ll:E.literal list) (phi:E.formula) : E.formula =
  let rec simplify_lit f = 
    match f with
      E.Literal l -> 
	if List.exists (fun lit -> E.identical_literal l lit) ll then E.True 
	else phi 
    | E.True           ->  E.True
    | E.False          ->  E.False
    | E.And(f1,f2)     -> E.And(simplify_lit f1, simplify_lit f2)
    | E.Or (f1,f2)     -> E.Or (simplify_lit f1, simplify_lit f2)
    | E.Not f          -> E.Not(simplify_lit f)
    | E.Implies(f1,f2) -> E.Implies (simplify_lit f1, simplify_lit f2)
    | E.Iff    (f1,f2) -> E.Iff (simplify_lit f1, simplify_lit f2)
  in
  let _ = printf "entering simplify_with_many_facts\n" in
  let res = simplify (simplify_lit phi) in
  let _ = printf "exiting simplify_with_many_facts\n" in
   res


let tactic_propositional_propagate (imp:implication) : implication =
  let rec simplify_propagate (f:implication) (used:E.literal list) : 
      (implication * E.literal list) =
    let new_facts = get_literals f.ante in
    if List.length new_facts = 0 then (f,used) else
      let _ = printf "simplify_propagate with %n literals\n" (List.length new_facts) in
      let new_conseq = simplify_with_many_facts new_facts f.conseq in
      let new_ante   = simplify_with_many_facts new_facts f.ante in
      simplify_propagate { ante = new_ante; conseq = new_conseq } (used @ new_facts)
  in
  let _ = printf "one\n" in
  let (new_imp,facts) = simplify_propagate imp [] in
  let _ = printf "two\n" in
  let new_ante = E.cleanup (E.And((E.conj_literals facts), new_imp.ante)) in
  let _ = printf "three\n" in
  let new_conseq = new_imp.conseq in
  { ante = new_ante ; conseq = new_conseq }


(**************************************************************************)
(* CONVERTERS: From tactic names to tactics functions                     *)
(**************************************************************************)

let pick_formula_split_tac (tac_name:formula_split_tactic) : formula_split_tactic_t =
  match tac_name with
  | SplitConsequent -> split_implication

let pick_formula_tac (tac_name:formula_tactic) : formula_tactic_t =
  match tac_name with
  | SimplifyPC -> id (* TO BE IMPLEMENTED *)
  | PropositionalPropagate -> 
    let _ = printf "pick\n" in
    tactic_propositional_propagate
