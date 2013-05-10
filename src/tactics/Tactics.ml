open LeapLib
open Printf

module E = Expression

type solve_tactic_t = Cases

type pre_tac_t = Full | Reduce | Reduce2

type post_tac_t = SplitConseq | SimplPCVoc

type t =
  {
    smp   : Smp.cutoff_strategy_t option ;
    solve : solve_tactic_t option        ;
    pre   : pre_tac_t list               ;
    post  : post_tac_t list              ;
  }


type polarity = Pos | Neg | Both


type support_info_t =
  {
    supp : E.formula list       ;    (* Normal generated support formula  *)
    extra_supp : E.formula list ;    (* Extra generated support formula   *)
    diff_conj : E.formula       ;    (* Vocabulary tid inequality formula *)
    supp_voc : E.tid list       ;    (* Normal support formula vocabulary *)
    supp_fresh_tid : E.tid      ;    (* Extra fresh generated tid         *)
  }


type task_t =
  {
    supp_form : E.formula list     ;
    diff      : E.formula option   ;
    rho       : E.formula          ;
    inv       : E.formula_info_t   ;
    all_voc   : E.tid list         ;
    trans_tid : E.tid              ;
    line      : E.pc_t             ;
  }



(* Configuration *)
let default_smp = Smp.Dnf



let new_tactics (smp:Smp.cutoff_strategy_t option)
                (solve_tac:solve_tactic_t option)
                (pre:pre_tac_t list)
                (post:post_tac_t list) : t =
  {smp = smp; solve = solve_tac; pre = pre; post = post }


let smp_cutoff (tacs:t) : Smp.cutoff_strategy_t option =
  tacs.smp


let solve_tactic (tacs:t) : solve_tactic_t option =
  tacs.solve


let pre_tacs (tacs:t) : pre_tac_t  list =
  tacs.pre


let post_tacs (tacs:t) : post_tac_t list =
  tacs.post



(* supp_info manipulation *)


let supp_voc (info:support_info_t) : E.tid list =
  info.supp_voc



let supp_list (info:support_info_t) : E.formula list =
  info.supp


let extra_supp_list (info:support_info_t) : E.formula list =
  info.extra_supp


let diff_conj (info:support_info_t) : E.formula =
  info.diff_conj


let supp_fresh_tid (info:support_info_t) : E.tid =
  info.supp_fresh_tid


(* Tactics specialization *)

let specialize_tacs (gral_tacs:t) (spec_tacs:t) : t =
  let pre_tacs  = match spec_tacs.pre with
                  | [] -> gral_tacs.pre
                  | _  -> spec_tacs.pre in
  let post_tacs = match spec_tacs.post with
                  | [] -> gral_tacs.post
                  | _  -> spec_tacs.post in
  let smp =       match spec_tacs.smp with
                  | None -> gral_tacs.smp
                  | _    -> spec_tacs.smp in
  let solve =     match spec_tacs.solve with
                  | None -> gral_tacs.solve
                  | _    -> spec_tacs.solve
  in
     { smp = smp; solve = solve; pre = pre_tacs; post = post_tacs }


(* Auxiliary simplification functions *)

let invert_polarity pol =
  match pol with
      Pos -> Neg
    | Neg -> Pos
    | Both -> Both


let simplify_aux (phi:E.formula) (auxf:E.literal-> polarity->E.formula) : E.formula =
  let is_true  (f:E.formula):bool = match f with E.True  -> true | _ -> false in
  let is_false (f:E.formula):bool = match f with E.False -> true | _ -> false in
  let rec simplify_f (f:E.formula) (pol:polarity): E.formula=
    match f with
        E.Literal(lit) -> (auxf lit pol)
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
  let idf l pol = E.Literal l in
    simplify_aux phi idf

(*                                                        *)
(* Simplifies a formula under the assumption that pc(i)=l *)
(*                                                        *)
let simplify_with_pc (phi:E.formula) (i:E.tid) (l:int) : E.formula =
  let is_same_tid (j:E.tid) : bool =
    match (i,j) with
      E.VarTh(v),E.VarTh(w) -> E.same_var v w
    | _                     -> false in
  let matches_tid (a:E.atom) : bool =
    match a with
      E.PC(line,Some j,false)       -> is_same_tid j
    | E.PCRange(l1,l2,Some j,false) -> is_same_tid j
    | _                             -> false in
  let matches_line (a:E.atom) : bool =
    match a with
      E.PC(line,Some j,false)        -> line == l
    | E.PCRange(l1,l2,Some j, false) -> l1<=l && l<=l2
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
    simplify_aux phi simplify_pc


(* This simplification simply removes the whole formula if the vocabulary
 * is irrelevant *)
let simplify_with_vocabulary (phi:E.formula) (voc:E.variable list): E.formula =
  let vars_in_phi = E.all_vars_as_set phi in
  let relevant = List.exists (fun v -> E.VarSet.mem v vars_in_phi) voc in
    if relevant then
      phi
    else
      E.True



(***************************************************************************)


let gen_fresh_support_tids (phi_list:E.formula list)
                            : (E.formula list * E.formula list * E.tid list) =
  let (param, unparam) = List.partition (fun phi -> E.voc phi <> []) phi_list in
  let (new_phi_list, voc_list) =
    List.fold_left (fun (fs, vs) phi ->
      let phi_voc  = E.voc phi in
      let new_tids = E.gen_fresh_thread_list vs (List.length phi_voc) in
      let subst    = E.new_tid_subst (List.combine phi_voc new_tids) in
      let new_phi  = E.subst_tid subst phi
      in
        ([new_phi] @ fs, new_tids@vs)
    ) ([],[]) param
  in
    (unparam, new_phi_list, voc_list)


(****************** Possible support generation tactics ********************)

(* General support generation *)
let gen_support (phi_list:E.formula list)
                (inv_voc:E.tid list)
                (tacs:pre_tac_t list) : support_info_t =
  (* Momentary support for a single pre-tactic *)
  let _ = assert (List.length tacs <= 1) in

  let pre_tac = match tacs with
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







(****************** Possible support generation tactics ********************)



(* Conversion function *)
let task_to_formula (hide_pres:bool) (info:task_t) : E.formula =
  let diff_list = match info.diff with
                    None -> []
                  | Some phi -> [phi] in
  let antecedent = E.And (E.conj_list (info.supp_form @ diff_list), info.rho) in
  let consequent = if hide_pres then
                     E.prime_modified antecedent info.inv.E.formula
                   else
                     info.inv.E.primed
  in
    E.Implies (antecedent, consequent)


(* Task manipulation *)

let new_task (supp:E.formula list)
             (diff:E.formula option)
             (rho:E.formula)
             (inv:E.formula_info_t)
             (all_voc:E.tid list)
             (trans_tid:E.tid)
             (line:E.pc_t) : task_t =
  {
    supp_form = supp      ;
    diff      = diff      ;
    rho       = rho       ;
    inv       = inv       ;
    all_voc   = all_voc   ;
    trans_tid = trans_tid ;
    line      = line      ;
  }

let dupl_task_with_inv (task:task_t) (inv:E.formula_info_t) : task_t =
  {
    supp_form = task.supp_form ;
    diff = task.diff ;
    rho = task.rho ;
    inv = inv ;
    all_voc = E.voc (E.conj_list (inv.E.formula :: task.supp_form)) ;
    trans_tid = task.trans_tid ;
    line = task.line ;
  }


let dupl_task_with_supp (task:task_t) (supp:E.formula list) : task_t =
  {
    supp_form = supp ;
    diff = task.diff ;
    rho = task.rho ;
    inv = task.inv ;
    all_voc = E.voc (E.conj_list (task.inv.E.formula :: supp)) ;
    trans_tid = task.trans_tid ;
    line = task.line ;
  }

(*** Tactics functions ***)


let tac_split (task:task_t) (tac:post_tac_t) : task_t list =
  let _ = printf "Split called\n" in
  let cases = E.to_conj_list task.inv.E.formula in
  if List.length cases > 1 then
    let new_tasks = List.map (fun phi ->
                      let inv_info = E.new_formula_info phi
                      in
                        dupl_task_with_inv task inv_info
                    ) cases
    in
      new_tasks
  else
    [task]


let tac_simple (task:task_t) (tac:post_tac_t) : task_t list =
  let psi_simpl = List.map (fun psi ->
                    let vars = task.inv.E.vars @ (E.all_vars task.rho) in
                    let simpl_pc = simplify_with_pc psi task.trans_tid task.line
                    in
                      simplify_with_vocabulary simpl_pc vars
                  ) task.supp_form
  (* TODO: Extend simplification to diff conjunction *)
  in
    [dupl_task_with_supp task psi_simpl]



(*** Tactics functions ***)

let apply_post_tac (task:task_t) (tac:post_tac_t) : task_t list =
  let _ = Printf.printf "POST-TACTIC INVARIANT: %s\n" (E.formula_to_str task.inv.E.formula) in
  match tac with
    SplitConseq -> tac_split task tac
  | SimplPCVoc -> tac_simple task tac


let apply_post_tacs (tasks:task_t list)
                    (tacs:post_tac_t list)
                    (hide_pres:bool)
                      : E.formula list =
  let res = match tacs with
              [] -> tasks
            | _  -> List.fold_left (fun ts tac ->
                      let new_ts = List.fold_left (fun xs task ->
                                     let new_tasks = apply_post_tac task tac
                                     in
                                       xs @ new_tasks
                                   ) [] tasks
                      in
                        ts @ new_ts
                    ) [] tacs
  in
    List.map (task_to_formula hide_pres) res
