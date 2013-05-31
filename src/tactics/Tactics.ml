open LeapLib
open Printf

module E = Expression
module GenSet = LeapGenericSet


(***************)
(* NEW TACTICS *)
(***************)

type polarity = Pos | Neg | Both

type pre_tacic_t = Full | Reduce | Reduce2

type post_tactic_t = SplitConsequent | SimplifyPC | PropositionalPropagate

type support_info_t {
  support        : E.formula list ;
  extra_support  : E.formula list ;
  tid_constraint : E.formula      ; (* tid inequalities *)
  vocabulary     : E.tid list     ; (* tids in support  *) 
  fresh_tid      : E.tid          ;
}

type verification_condition {
  (* ANTECEDENT *)
  antecedent : E.formula ;

  (* CONSEQUENT *)
  consequent : E.formula ;
  consequent_renamed : E.formula ;

  (* SUPPORT INFO *)
  support_info : support_info_t ;

  (* TRANSITION RELATION *)
  rho                : E.formula ;

  (* EXTRA INFO *)
  goal               : E.formula  ;
  transition_tid     : E.tid      ;
  line               : E.pc_t     ;
  vocabulary         : E.tid list ;
}

type proof_plan =
  {
    cutoff_algorithm : Smp.cutoff_strategy_t option ;
    solve            : solve_tactic_t option        ;
    pre_tactics      : pre_tactics_t list           ;
    post_tactics     : post_tactics_t list          ;
  }


(* Conversion function *)
let task_to_formula (hide_pres:bool) (info:task_t) : (E.formula * res_info_t) =
  let diff_list = match info.diff with
                    None -> []
                  | Some phi -> [phi] in
  let antecedent = E.And (E.conj_list (info.inv.E.formula :: info.supp_form @ diff_list), info.rho) in
  let consequent = if hide_pres then
                     E.prime_modified antecedent (E.unprime info.inv.E.primed)
                   else
                     info.inv.E.primed in
  let res_info = {try_pos = info.try_posdp; }
  in
    (E.Implies (antecedent, consequent), res_info)


let compute_antecedent_consequent (vc:verification_condition) : unit =
  let tid_constraint = match vc.tid_constraint with
      None -> []
    | Some phi -> [phi] in
  let the_antecedent =
    E.And (E.conj_list (vc.goal :: vc.support @ tid_constraint), !vc.rho) in
  let primed_consequent = E.prime vc.goal in
  let renamed_consequent = E.prime_modify the_antecedent vc.goal in
  vc.antecedent := the_antecedent ; 
  vc.consequent := primed_consequent ;
  vc.consequent_renamed := renamed_consequent

 exception Invalid_post_tac of string

let post_tactic_from_string (s:string) : post_tactic_t =
  match s with
  | "split-consequent"        -> SplitConsequent
  | "simplify-pc"             -> SimplifyPC
  | "propositional-propagate" -> PropositionalPropagate
  | _ -> raise(Invalid_post_tac s)


let default_cutoff_algorithm = Smp.Dnf

(* Get functions for type plan *)

let get_cutoff (plan:proof_plan) : Smp.cutoff_strategy_t option =
  plan.cutoff_algorithm
and get_solve (plan:proof_plan) : solve_tactic_t option =
  plan.solve
and get_pre_tactics (plan:proof_plan) : pre_tac_t  list =
  plan.pre_tactics
and get_post_tactics (plan:proof_plan) : post_tac_t list =
  plan.post_tactics


(* Get functions for type verification_condition *)

let get_antecedent (vc:verification_condition) : E.formula=
  vc.antecedent
and get_consequent_with_primes (vc:verification_condition) : E.formula=
  vc.consequent
and get_consequent_no_primes (vc:verification_condition) : E.formula=
  vc.consequent_renamed
and get_support (vc:verification_condition) : E.formula list =
  vc.support
and get_tid_constraint (vc:verification_condition) : E.formula =
  vc.tid_constraint
and get_suport_vocabulary (vc:verification_condition) : E.tid list =
  vc.support_vocabulary
and get_support_fresh_tid (vc:verification_condition) : E.tid =
  vc.support_fresh_tid
and get_rho (vc:verification_condition) : E.tid =
  vc.rho
and get_goal (vc:verification_condition) : E.tid =
  vc.goal
and get_transition_tid (vc:verification_condition) : E.tid =
  vc.transition_tid
and get_line (vc:verification_condition) : E.tid =
  vc.line
and get_vocabulary (vc:verification_condition) : E.tid =
  vc.vocabulary

(* Auxiliary simplification functions *)

let invert_polarity pol =
  match pol with
      Pos -> Neg
    | Neg -> Pos
    | Both -> Both


let simplifier_gen (phi:E.formula) (simp_lit:E.literal-> polarity->E.formula) : E.formula =
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
    simplifier_gen phi id


let simplify_with_pc (phi:E.formula) (i:E.tid) (lines:int list) (primed:bool) : E.formula =
  let is_same_tid (j:E.tid) : bool =
    match (i,j) with
      E.VarTh(v),E.VarTh(w) -> E.same_var v w
    | _                     -> false in
  let matches_tid (a:E.atom) : bool =
    match a with
      E.PC(line,Some j,pr)       -> is_same_tid j
    | E.PCRange(l1,l2,Some j,pr) -> is_same_tid j
    | _                             -> false in
  let matches_line (a:E.atom) : bool =
    match a with
      E.PC(line,Some j,pr)       -> List.mem line ls
    | E.PCRange(l1,l2,Some j,pr) -> List.exists (fun l -> l1<= l && l <= l2) ls
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
    simplifier_gen phi simplify_pc



(* This simplification simply removes the whole formula if the vocabulary
 * is irrelevant *)
let simplify_with_vocabulary (phi:E.formula) (vocabulary:E.variable list): E.formula =
  let vars_in_phi = E.all_vars_as_set phi in
  let relevant = List.exists (fun v -> E.VarSet.mem v vars_in_phi) vocabulary in
    if relevant then
      phi
    else
      E.True


let gen_fresh_support_tids (phi_list:E.formula list)
                            : (E.formula list * E.formula list * E.tid list) =
  let (param, no_param) = List.partition (fun phi -> E.voc phi <> []) phi_list in
  let (new_phi_list, voc_list) =
    List.fold_left (fun (fs, vs) phi ->
      let phi_voc  = E.voc phi in
      let new_tids = E.gen_fresh_tid_list vs (List.length phi_voc) in
      let subst    = E.new_tid_subst (List.combine phi_voc new_tids) in
      let new_phi  = E.subst_tid subst phi
      in
        ([new_phi] @ fs, new_tids@vs)
    ) ([],[]) param
  in
    (no_param, new_phi_list, voc_list)


let generate_support (phi_list:E.formula list)
                     (goal_vocabulary:E.tid list)
                     (tacs:support_tacic list) : support_info_t =
  (* For now: only support a single pre-tactic *)
  let _ = assert (List.length tacs <= 1) in
  let tactic = match tacs with
                  [] -> Full
                | _  -> List.hd tacs in
  let (unparam_supp, fresh_supp_list, fresh_supp_voc) =
    gen_fresh_support_tids phi_list in
  let fresh_supp = E.conj_list fresh_supp_list in

  let supp_fresh_tid = E.gen_fresh_thread fresh_supp_voc in

  let diff_conj = E.conj_list $ List.map (fun j ->
                                  E.ineq_tid supp_fresh_tid j
                                ) (fresh_supp_voc @ inv_voc) in


  (* Construct substitutions for support *)
  let pre_subst_normal = E.new_comb_subst fresh_supp_voc inv_voc in
  let pre_subst_fresh = E.new_comb_subst fresh_supp_voc (supp_fresh_tid::inv_voc) in

  let (subst_normal, subst_fresh) =
    match pre_tac with
      Full   -> (pre_subst_normal, pre_subst_fresh)
    | Reduce -> (List.filter (E.subst_full_assign fresh_supp_voc) pre_subst_normal,
                 List.filter (E.subst_full_assign fresh_supp_voc) pre_subst_fresh)
    | Reduce2-> (List.filter (E.subst_full_assign fresh_supp_voc) pre_subst_normal,
                 List.filter (E.subst_full_assign fresh_supp_voc) pre_subst_fresh) in
  
  (* We apply substitution *)
  let supp = unparam_supp @ List.map (fun s ->
               E.subst_tid s fresh_supp
             ) subst_normal in

  let extra_supp = unparam_supp @ List.map (fun s ->
                     E.subst_tid s fresh_supp
                   ) subst_fresh in

  let (final_supp, final_extra_supp) =
    match pre_tac with
    | Full -> (supp, extra_supp)
    | Reduce -> (supp, extra_supp)
    | Reduce2 -> (E.cleanup_dup supp, E.cleanup_dup extra_supp)
  in

    {
      supp = final_supp ;
      extra_supp = final_extra_supp ;
      diff_conj = diff_conj ;
      supp_voc = fresh_supp_voc ;
      supp_fresh_tid = supp_fresh_tid ;
    }
                        

let create_vc (supp       : E.formula list)
              (tid_constr : E.formula option)
              (rho        : E.formula)
              (goal       : E.formula_info_t)
              (vocab      : E.tid list)
              (trans_tid  : E.tid)
              (line       : E.pc_t) : verification_condition =
  let the_vc = 
  {
    suports        = supp ;
    tid_constraint = tid_constr;
    rho            = rho ;
    goal           = goal ;
    transition_tid = trans_tid ;
    line           = line ;
    vocabulary     = vocab ; (* fix: can be computed *)
    (* missing : support_vocabulary, support_fresh_tid *)
  } ;
    compute_antecedent_consequent the_vc ; the_vc


let dup_vc_with_goal (vc:verification_condition) (new_goal:formula) : verification_condition =
  let new_vc =  {
    suport         = vc.support ;
    tid_constraint = vc.tid_constraint;
    rho            = vc.rho ;
    goal           = new_goal ;
    transition_tid = vc.transition_tid ;
    line           = vc.line ;
    vocabulary     = vc.vocabualry ; (* fix *)
  } ;
    compute_antecedent_consequent new_vc ; new_vc


(*** Tactics functions ***)

let tactic_split_consequent (vc:verification_condition)  : verification_condition list =
  let _ = printf "tactic_split_consequent called\n" in
  let cases = E.to_conj_list vc.goal in
  if List.length cases > 1 then
    let new_vcs = List.map (fun phi ->
                        dup_vc_with_goal vc phi
                    ) cases
    in
      new_vcs
  else
    [vc]


















