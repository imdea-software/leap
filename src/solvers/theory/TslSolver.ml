
module TslExp = TSLExpression
open TSLExpression


let comp_model : bool ref = ref false
(* Should we compute a model in case of courter example? *)

let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
(* The structure where we store the options for cutoff *)


let gen_fresh_addr_var (vs:TslExp.VarSet.t) : TslExp.variable =
  let rec find (n:int) : TslExp.variable =
    let v_cand_id = "fresh_addr_" ^ (string_of_int n) in
    let v_cand = TslExp.build_var v_cand_id TslExp.Int false None None in
      if TslExp.VarSet.mem v_cand vs then find (n+1) else v_cand
  in
    find 0


let sanitize (cf:TslExp.conjunctive_formula) : TslExp.conjunctive_formula =
  let find_candidates (ls:TslExp.literal list)
        : (TslExp.VarSet.t * TslExp.VarSet.t)  =
    List.fold_left (fun (cs,ss) l ->
      match l with
      | Atom(Eq(_,AddrArrayT(AddrArrayUp(_,VarInt v,_)))) ->
        (TslExp.VarSet.add v cs, ss)
      | Atom(Eq(IntT(VarInt _), IntT(IntAdd (VarInt v, IntVal 1)))) ->
        (cs, TslExp.VarSet.add v ss)
      | Atom(Eq(IntT(IntAdd (VarInt v, IntVal 1)), IntT (VarInt _))) ->
        (cs, TslExp.VarSet.add v ss)
      | _ -> (cs, ss)
    ) (TslExp.VarSet.empty, TslExp.VarSet.empty) ls
  in
  match cf with
  | TslExp.FalseConj -> cf
  | TslExp.TrueConj  -> cf
  | TslExp.Conj ls   -> let vars = TslExp.get_varset_from_conj cf in
                        let (cs,ss) = find_candidates ls in
                        let needs_sanit = TslExp.VarSet.diff cs ss in
                        let ls' = TslExp.VarSet.fold (fun v xs ->
                                    let v_new = VarInt (gen_fresh_addr_var vars) in
                                    (Atom(Eq(IntT v_new, IntT(IntAdd(VarInt v, IntVal 1))))) :: ls
                                  ) needs_sanit ls
                        in
                          TslExp.Conj ls'


let guess_arrangements (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula list =
  let rec cons_var_eq_class (vs:TslExp.variable list) : TslExp.literal list =
    match vs with
    | v1::v2::xs -> Atom(Eq(IntT (VarInt v1), IntT (VarInt v2))) :: cons_var_eq_class (v2::xs)
    | _          -> []
  in
  let rec cons_var_ords (arr:TslExp.variable list list) : TslExp.literal list =
    match arr with
    | xs::ys::zs -> Atom(Less(VarInt(List.hd xs),
                              VarInt(List.hd ys))) :: cons_var_ords (ys::zs)
    | _          -> []
  in
  match cf with
  | TslExp.FalseConj -> []
  | TslExp.TrueConj  -> []
  | TslExp.Conj ls   -> let level_vars = TslExp.get_varset_from_conj cf in
                        let parts = Partition.gen_partitions
                                      (TslExp.VarSet.elements level_vars) [] in
                        let eqs = List.fold_left (fun xs p ->
                                    (Partition.to_list p) :: xs
                                  ) [] parts in
                        let arrgs = List.fold_left (fun xs eq_c ->
                                      (LeapLib.comb eq_c (List.length eq_c)) @ xs
                                    ) [] eqs in
                        let lv_arrs = List.fold_left (fun xs arr ->
                                        let eqs = List.fold_left (fun ys eq_c ->
                                                    (cons_var_eq_class eq_c) @ ys
                                                  ) [] arr in
                                        let ords = cons_var_ords arr
                                        in
                                          (TslExp.Conj (eqs @ ords)) :: xs
                                      ) [] arrgs
                        in
                          lv_arrs

let split (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula * TslExp.conjunctive_formula =
  match cf with
  | TslExp.TrueConj  -> (TslExp.TrueConj,  TslExp.TrueConj)
  | TslExp.FalseConj -> (TslExp.FalseConj, TslExp.FalseConj)
  | TslExp.Conj cf   ->
      let (pa,nc) = List.fold_left (fun (pas,ncs) l ->
                      match l with
                        (* l = q *)
                      | Atom(Eq(IntT(VarInt _),IntT(IntVal _)))
                      | Atom(Eq(IntT(IntVal _),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(VarInt _),IntT(IntVal _)))
                      | NegAtom(InEq(IntT(IntVal _),IntT(VarInt _))) -> (l::pas,ncs)
                        (* l1 = l2 *)
                      | Atom(InEq(IntT(VarInt _),IntT(VarInt _)))
                      | NegAtom(Eq(IntT(VarInt _),IntT(VarInt _)))
                        (* l1 = l2 + 1*)
                      | Atom(Eq(IntT(VarInt _),IntT (IntAdd (VarInt _, IntVal 1))))
                      | Atom(Eq(IntT(VarInt _),IntT (IntAdd (IntVal 1, VarInt _))))
                      | Atom(Eq(IntT(IntAdd(VarInt _,IntVal 1)),IntT(VarInt _)))
                      | Atom(Eq(IntT(IntAdd(IntVal 1,VarInt _)),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(VarInt _),IntT (IntAdd (VarInt _, IntVal 1))))
                      | NegAtom(InEq(IntT(VarInt _),IntT (IntAdd (IntVal 1, VarInt _))))
                      | NegAtom(InEq(IntT(IntAdd(VarInt _,IntVal 1)),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(IntAdd(IntVal 1,VarInt _)),IntT(VarInt _)))
                        (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
                      | Atom(Less(VarInt _,VarInt _))
                      | Atom(Greater(VarInt _,VarInt _))
                      | NegAtom(LessEq(VarInt _,VarInt _))
                      | NegAtom(GreaterEq(VarInt _,VarInt _)) -> (l::pas,l::ncs)
                      | _ -> (pas,l::ncs)
                    ) ([],[]) cf
      in
        (TslExp.Conj pa, TslExp.Conj nc)


let is_sat_plus_info (lines : int)
           (stac:Tactics.solve_tactic_t option)
           (co : Smp.cutoff_strategy)
           (phi : TslExp.formula) : (bool * int * int) =
  (* 0. Normalize the formula. In fact, I only convert it to DNF *)
  (* TODO: I really need a function to normalize literals!!! *)
  (* For example, I need to know literal of the form A = B{l <- a}
     but a modification of a node level (ie. c->next[0] = a is
     translated into c' = mkcell (c.data,c.next{0 <- a},c.level)).
     In this case I have an array modification, which is inside another
     literal, and thus, I would not be able to consider it. *)
  let phi_dnf = TslExp.dnf phi in
  (* 1. Sanitize the formula *)
  let phi_san = List.map sanitize phi_dnf in
  (* 2. Guess arrangements of level variables *)
  let arrgs = List.map guess_arrangements phi_san in
  (* 3. Split each conjunction into PA y NC *)
  let splits = List.map split phi_san in
  (* 4. Check satisfiability of NC /\ alpha in arrgs *)
  let numSolv_id = BackendSolvers.Yices.identifier in
  let module NumSol = (val NumSolver.choose numSolv_id : NumSolver.S) in
  (* Here goes the code for satisfiability from the paper *)
  (true, 1, 2)


let is_sat (lines : int)
           (stac:Tactics.solve_tactic_t option)
           (co : Smp.cutoff_strategy)
           (phi : TslExp.formula) : bool =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = is_sat_plus_info lines stac co phi in s


let is_valid_plus_info (prog_lines:int)
                       (stac:Tactics.solve_tactic_t option)
                       (co:Smp.cutoff_strategy)
                       (phi:TslExp.formula) : (bool * int * int) =
  let (s,tsl_count,tslk_count) = is_sat_plus_info prog_lines stac co
                                   (TslExp.Not phi) in
    (not s, tsl_count, tslk_count)


let is_valid (prog_lines:int)
             (stac:Tactics.solve_tactic_t option)
             (co:Smp.cutoff_strategy)
             (phi:TslExp.formula) : bool =
  not (is_sat prog_lines stac co phi)


let compute_model (b:bool) : unit =
  let _ = comp_model := b
  in ()
    (* Should I enable which solver? *)
    (* Solver.compute_model b *)
    (* Perhaps I should only set the flag and set activate the compute_model
       on the Solver when it is about to be called in is_sat *)


let model_to_str () : string =
  ""


let print_model () : unit =
  if !comp_model then
    print_endline (model_to_str())
  else
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
