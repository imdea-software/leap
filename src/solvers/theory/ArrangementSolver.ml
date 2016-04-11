open LeapVerbose

module Arr    = Arrangements
module E      = Expression
module F      = Formula
module GenSet = LeapGenericSet

module type S =
  sig

    val try_sat_with_pa : Expression.formula -> Sat.t

    val dnf_sat : int ->
                  Smp.cutoff_strategy_t ->
                  Expression.conjunctive_formula ->
                  Sat.t

  end
  

module Make (AS : ArrangementSolverSpec.S) =
  struct

    type alpha_pair_t = (E.integer list * E.integer option)

    let arr_table = Hashtbl.create 8

    (* Table containing arrangement satisfiability *)
    let alpha_sat_table : (E.conjunctive_formula, Sat.t) Hashtbl.t = Hashtbl.create 8

    let this_call_tbl : DP.call_tbl_t = DP.new_call_tbl()



    let try_sat_with_pa (phi:E.formula) : Sat.t =
      DP.add_dp_calls this_call_tbl DP.Num 1;
      NumSolver.try_sat phi


    let split_into_pa_nc (cf:E.conjunctive_formula)
          : E.conjunctive_formula *
            E.conjunctive_formula *
            E.conjunctive_formula =
      let conj (ls:E.literal list) : E.conjunctive_formula =
        match ls with
        | [] -> F.TrueConj
        | _ -> F.Conj ls
      in
      match cf with
      | F.TrueConj  -> (F.TrueConj,  F.TrueConj,  F.TrueConj)
      | F.FalseConj -> (F.FalseConj, F.FalseConj, F.FalseConj)
      | F.Conj cf   ->
          let (pa,panc,nc) =
            List.fold_left (fun (pas,pancs,ncs) l ->
              match l with
              (* l = q *)
              | F.Atom(E.Eq(E.IntT(E.VarInt _),E.IntT(E.IntVal _)))
              | F.Atom(E.Eq(E.IntT(E.IntVal _),E.IntT(E.VarInt _)))
              | F.NegAtom(E.InEq(E.IntT(E.VarInt _),E.IntT(E.IntVal _)))
              | F.NegAtom(E.InEq(E.IntT(E.IntVal _),E.IntT(E.VarInt _))) -> (l::pas,pancs,ncs)
                (* l1 = l2 *)
              | F.Atom(E.Eq(E.IntT(E.VarInt _),E.IntT(E.VarInt _)))
              | F.NegAtom(E.InEq(E.IntT(E.VarInt _),E.IntT(E.VarInt _)))
                (* l1 != l2 *)
              | F.Atom(E.InEq(E.IntT(E.VarInt _),E.IntT(E.VarInt _)))
              | F.NegAtom(E.Eq(E.IntT(E.VarInt _),E.IntT(E.VarInt _)))
                (* l1 = l2 + q *)
              | F.Atom(E.Eq(E.IntT(E.VarInt _),E.IntT (E.IntAdd (E.VarInt _, E.IntVal _))))
              | F.Atom(E.Eq(E.IntT(E.VarInt _),E.IntT (E.IntAdd (E.IntVal _, E.VarInt _))))
              | F.Atom(E.Eq(E.IntT(E.IntAdd(E.VarInt _,E.IntVal _)),E.IntT(E.VarInt _)))
              | F.Atom(E.Eq(E.IntT(E.IntAdd(E.IntVal _,E.VarInt _)),E.IntT(E.VarInt _)))
              | F.NegAtom(E.InEq(E.IntT(E.VarInt _),E.IntT (E.IntAdd (E.VarInt _, E.IntVal _))))
              | F.NegAtom(E.InEq(E.IntT(E.VarInt _),E.IntT (E.IntAdd (E.IntVal _, E.VarInt _))))
              | F.NegAtom(E.InEq(E.IntT(E.IntAdd(E.VarInt _,E.IntVal _)),E.IntT(E.VarInt _)))
              | F.NegAtom(E.InEq(E.IntT(E.IntAdd(E.IntVal _,E.VarInt _)),E.IntT(E.VarInt _)))
                (* l1 = l2 - q *)
              | F.Atom(E.Eq(E.IntT(E.VarInt _),E.IntT (E.IntSub (E.VarInt _, E.IntVal _))))
              | F.Atom(E.Eq(E.IntT(E.VarInt _),E.IntT (E.IntSub (E.IntVal _, E.VarInt _))))
              | F.Atom(E.Eq(E.IntT(E.IntSub(E.VarInt _,E.IntVal _)),E.IntT(E.VarInt _)))
              | F.Atom(E.Eq(E.IntT(E.IntSub(E.IntVal _,E.VarInt _)),E.IntT(E.VarInt _)))
              | F.NegAtom(E.InEq(E.IntT(E.VarInt _),E.IntT (E.IntSub (E.VarInt _, E.IntVal _))))
              | F.NegAtom(E.InEq(E.IntT(E.VarInt _),E.IntT (E.IntSub (E.IntVal _, E.VarInt _))))
              | F.NegAtom(E.InEq(E.IntT(E.IntSub(E.VarInt _,E.IntVal _)),E.IntT(E.VarInt _)))
              | F.NegAtom(E.InEq(E.IntT(E.IntSub(E.IntVal _,E.VarInt _)),E.IntT(E.VarInt _)))
                (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
              | F.Atom(E.Less(E.VarInt _,E.VarInt _))
              | F.Atom(E.Greater(E.VarInt _,E.VarInt _))
              | F.NegAtom(E.LessEq(E.VarInt _,E.VarInt _))
              | F.NegAtom(E.GreaterEq(E.VarInt _,E.VarInt _))
                (* But l1 <= l2 literals appear, as well as they are not compared to constants *)
              | F.Atom(E.LessEq(E.VarInt _,E.VarInt _))
              | F.Atom(E.GreaterEq(E.VarInt _,E.VarInt _))
              | F.NegAtom(E.Less(E.VarInt _,E.VarInt _))
              | F.NegAtom(E.Greater(E.VarInt _,E.VarInt _)) -> (pas,l::pancs,ncs)
                (* Cases that should not appear at this point after normalization *)
              | F.Atom(E.Less(E.IntVal _,_))          | F.Atom(E.Less(_,E.IntVal _))
              | F.Atom(E.Greater(E.IntVal _,_))       | F.Atom(E.Greater(_,E.IntVal _))
              | F.NegAtom(E.LessEq(E.IntVal _,_))     | F.NegAtom(E.LessEq(_,E.IntVal _))
              | F.NegAtom(E.GreaterEq(E.IntVal _,_))  | F.NegAtom(E.GreaterEq(_,E.IntVal _))
              | F.Atom(E.LessEq(E.IntVal _,_))        | F.Atom(E.LessEq(_,E.IntVal _))
              | F.Atom(E.GreaterEq(E.IntVal _,_))     | F.Atom(E.GreaterEq(_,E.IntVal _))
              | F.NegAtom(E.Less(E.IntVal _,_))       | F.NegAtom(E.Less(_,E.IntVal _))
              | F.NegAtom(E.Greater(E.IntVal _,_))    | F.NegAtom(E.Greater(_,E.IntVal _)) ->
                  assert false
                (* Remaining cases *)
              | _ -> (pas,pancs,l::ncs)
            ) ([],[],[]) cf
          in
            (conj pa, conj panc, conj nc)



    let guess_arrangements (cf:E.conjunctive_formula) : (E.integer list list) GenSet.t option =
      Log.print "Will guess arrangement for: " (E.conjunctive_formula_to_str cf);
      let arr = Arr.empty true in
        match cf with
        | F.FalseConj -> Some (GenSet.empty ())
        | F.TrueConj  -> Some (GenSet.empty ())
        | F.Conj ls   -> begin
                            let level_vars = E.varset_of_sort_from_conj cf (E.Int) in
                            if E.V.VarSet.cardinal level_vars = 0 then
                              None
                            else begin
                              verbl _LONG_INFO "**** TSL Solver: variables for arrangement...\n{ %s }\n"
                                      (E.V.VarSet.fold (fun v str ->
                                        str ^ E.V.to_str v ^ "; "
                                      ) level_vars "");
                              E.V.VarSet.iter (fun v -> Arr.add_elem arr (E.VarInt v)) level_vars;
                              List.iter (fun l ->
(*                                print_endline ("LITERAL TO ANALYZE: " ^ (E.literal_to_str l)); *)
                                match l with
                                | F.Atom(E.Less(i1,i2)) -> Arr.add_less arr i1 i2
                                | F.Atom(E.Greater(i1,i2)) -> Arr.add_greater arr i1 i2
                                | F.Atom(E.LessEq(i1,i2)) -> Arr.add_lesseq arr i1 i2
                                | F.Atom(E.GreaterEq(i1,i2)) -> Arr.add_greatereq arr i1 i2
                                | F.Atom(E.Eq(E.IntT (E.VarInt v1),E.IntT (E.IntAdd(E.VarInt v2,E.IntVal i))))
                                | F.Atom(E.Eq(E.IntT (E.VarInt v1),E.IntT (E.IntAdd(E.IntVal i,E.VarInt v2))))
                                | F.Atom(E.Eq(E.IntT (E.IntAdd(E.VarInt v2,E.IntVal i)),E.IntT (E.VarInt v1)))
                                | F.Atom(E.Eq(E.IntT (E.IntAdd(E.IntVal i,E.VarInt v2)),E.IntT (E.VarInt v1))) ->
                                    if i = 1 then Arr.add_followed_by arr (E.VarInt v2) (E.VarInt v1)
                                    else if i = -1 then Arr.add_followed_by arr (E.VarInt v1) (E.VarInt v2)
                                    else if i > 0 then Arr.add_greater arr (E.VarInt v1) (E.VarInt v2)
                                    else if i < 0 then Arr.add_less arr (E.VarInt v1) (E.VarInt v2)
                                    else Arr.add_eq arr (E.VarInt v1) (E.VarInt v2)
                                | F.Atom(E.Eq(E.IntT (E.VarInt v1),E.IntT (E.IntSub(E.VarInt v2,E.IntVal i))))
                                | F.Atom(E.Eq(E.IntT (E.VarInt v1),E.IntT (E.IntSub(E.IntVal i,E.VarInt v2))))
                                | F.Atom(E.Eq(E.IntT (E.IntSub(E.VarInt v2,E.IntVal i)),E.IntT (E.VarInt v1)))
                                | F.Atom(E.Eq(E.IntT (E.IntSub(E.IntVal i,E.VarInt v2)),E.IntT (E.VarInt v1))) ->
                                    if i = 1 then Arr.add_followed_by arr (E.VarInt v1) (E.VarInt v2)
                                    else if i = -1 then Arr.add_followed_by arr (E.VarInt v2) (E.VarInt v1)
                                    else if i > 0 then Arr.add_less arr (E.VarInt v1) (E.VarInt v2)
                                    else if i < 0 then Arr.add_greater arr (E.VarInt v1) (E.VarInt v2)
                                    else Arr.add_eq arr (E.VarInt v1) (E.VarInt v2)
                                | F.Atom(E.Eq(E.IntT (E.VarInt varr),E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.VarInt v2,E.IntVal i)))))))
                                | F.Atom(E.Eq(E.IntT (E.VarInt varr),E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.IntVal i,E.VarInt v2)))))))
                                | F.Atom(E.Eq(E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.VarInt v2,E.IntVal i))))),E.IntT (E.VarInt varr)))
                                | F.Atom(E.Eq(E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.IntVal i,E.VarInt v2))))),E.IntT (E.VarInt varr))) ->
                                    let v1 = E.V.set_param varr (E.V.Local (E.voc_to_var th)) in
                                    if i = 1 then Arr.add_followed_by arr (E.VarInt v2) (E.VarInt v1)
                                    else if i = -1 then Arr.add_followed_by arr (E.VarInt v1) (E.VarInt v2)
                                    else if i > 0 then Arr.add_greater arr (E.VarInt v1) (E.VarInt v2)
                                    else if i < 0 then Arr.add_less arr (E.VarInt v1) (E.VarInt v2)
                                    else Arr.add_eq arr (E.VarInt v1) (E.VarInt v2)
                                | F.Atom(E.Eq(E.IntT (E.VarInt varr),E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntSub(E.VarInt v2,E.IntVal i)))))))
                                | F.Atom(E.Eq(E.IntT (E.VarInt varr),E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntSub(E.IntVal i,E.VarInt v2)))))))
                                | F.Atom(E.Eq(E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntSub(E.VarInt v2,E.IntVal i))))),E.IntT (E.VarInt varr)))
                                | F.Atom(E.Eq(E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntSub(E.IntVal i,E.VarInt v2))))),E.IntT (E.VarInt varr))) ->
                                    let v1 = E.V.set_param varr (E.V.Local (E.voc_to_var th)) in
                                    if i = 1 then Arr.add_followed_by arr (E.VarInt v1) (E.VarInt v2)
                                    else if i = -1 then Arr.add_followed_by arr (E.VarInt v2) (E.VarInt v1)
                                    else if i > 0 then Arr.add_less arr (E.VarInt v1) (E.VarInt v2)
                                    else if i < 0 then Arr.add_greater arr (E.VarInt v1) (E.VarInt v2)
                                    else Arr.add_eq arr (E.VarInt v1) (E.VarInt v2)
                                | F.Atom(E.Eq(E.IntT(E.VarInt v),E.IntT(E.IntVal 0)))
                                | F.Atom(E.Eq(E.IntT(E.IntVal 0),E.IntT(E.VarInt v))) ->
                                    Arr.set_minimum arr (E.VarInt v)
                                | F.Atom(E.Eq(E.IntT i1,E.IntT i2)) -> ((*print_endline "THIS MATCH";*) Arr.add_eq arr i1 i2(*; print_endline ("NOW THE ARR CONTAINS: " ^ (Arr.to_str arr E.integer_to_str))*))
                                | F.Atom(E.InEq(E.IntT i1,E.IntT i2)) -> Arr.add_ineq arr i1 i2
                                | F.NegAtom(E.Less(i1,i2)) -> Arr.add_greatereq arr i1 i2
                                | F.NegAtom(E.Greater(i1,i2)) -> Arr.add_lesseq arr i1 i2
                                | F.NegAtom(E.LessEq(i1,i2)) -> Arr.add_greater arr i1 i2
                                | F.NegAtom(E.GreaterEq(i1,i2)) -> Arr.add_less arr i1 i2
                                | F.NegAtom(E.Eq(E.IntT i1,E.IntT i2)) -> Arr.add_ineq arr i1 i2
                                | F.NegAtom(E.InEq(E.IntT (E.VarInt v1),E.IntT (E.IntAdd(E.VarInt v2,E.IntVal i))))
                                | F.NegAtom(E.InEq(E.IntT (E.VarInt v1),E.IntT (E.IntAdd(E.IntVal i,E.VarInt v2))))
                                | F.NegAtom(E.InEq(E.IntT (E.IntAdd(E.VarInt v2,E.IntVal i)),E.IntT (E.VarInt v1)))
                                | F.NegAtom(E.InEq(E.IntT (E.IntAdd(E.IntVal i,E.VarInt v2)),E.IntT (E.VarInt v1))) ->
                                    if i > 0 then Arr.add_greater arr (E.VarInt v1) (E.VarInt v2)
                                    else if i < 0 then Arr.add_less arr (E.VarInt v1) (E.VarInt v2)
                                    else Arr.add_eq arr (E.VarInt v1) (E.VarInt v2)
                                | F.NegAtom(E.InEq(E.IntT (E.VarInt varr),E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.VarInt v2,E.IntVal i)))))))
                                | F.NegAtom(E.InEq(E.IntT (E.VarInt varr),E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.IntVal i,E.VarInt v2)))))))
                                | F.NegAtom(E.InEq(E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.VarInt v2,E.IntVal i))))),E.IntT (E.VarInt varr)))
                                | F.NegAtom(E.InEq(E.ArrayT(E.ArrayUp(_,th,E.Term(E.IntT(E.IntAdd(E.IntVal i,E.VarInt v2))))),E.IntT (E.VarInt varr))) ->
                                    let v1 = E.V.set_param varr (E.V.Local (E.voc_to_var th)) in
                                    if i > 0 then Arr.add_greater arr (E.VarInt v1) (E.VarInt v2)
                                    else if i < 0 then Arr.add_less arr (E.VarInt v1) (E.VarInt v2)
                                    else Arr.add_eq arr (E.VarInt v1) (E.VarInt v2)
                                | F.NegAtom(E.InEq(E.IntT(E.VarInt v),E.IntT(E.IntVal 0)))
                                | F.NegAtom(E.InEq(E.IntT(E.IntVal 0),E.IntT(E.VarInt v))) ->
                                    Arr.set_minimum arr (E.VarInt v)
                                | F.NegAtom(E.InEq(E.IntT i1,E.IntT i2)) -> Arr.add_eq arr i1 i2
                                | _ -> ()
                              ) ls;
                              Log.print "TSL Solver known information for arrangements"
                                    (Arr.to_str arr E.integer_to_str);
                              let arrgs = try
                                            Log.print "A" "1";
                                            Hashtbl.find arr_table arr
                                          with
                                            _ -> begin
                                                   let a = Arr.gen_arrs arr in
                                                   Hashtbl.add arr_table arr a;
                                                   a
                                                 end
                              in
                              verbl _LONG_INFO "**** TSL Solver: generated %i arrangements\n" (GenSet.size arrgs);
                              Log.print "Arrgs size: " (string_of_int (GenSet.size arrgs));
                              Some arrgs
                            end
                          end


    let alpha_to_conjunctive_formula (alpha:E.integer list list)
        : E.conjunctive_formula =
      let rec cons_eq_class (is:E.integer list) : E.literal list =
        match is with
        | i1::i2::xs -> F.Atom(E.Eq(E.IntT i1, E.IntT i2)) :: cons_eq_class (i2::xs)
        | _          -> []
      in
      let rec cons_ords (arr:E.integer list list) : E.literal list =
        match arr with
        | xs::ys::zs -> F.Atom(E.Less(List.hd ys,
                                  List.hd xs)) :: cons_ords (ys::zs)
        | _          -> []
      in
      let eqs = List.fold_left (fun ys eq_c ->
                  (cons_eq_class eq_c) @ ys
                ) [] alpha in
      let ords = cons_ords alpha in
        (F.Conj (eqs @ ords))


    let pumping (cf:E.conjunctive_formula) : unit =
      match cf with
      | F.TrueConj  -> ()
      | F.FalseConj -> ()
      | F.Conj ls   -> begin
                          let no_arr_updates = ref true in
                          List.iter (fun l ->
                            match l with
                            (* A = B{l <- a} *)
                            | F.Atom(E.Eq(_,E.AddrArrayT(E.AddrArrayUp(_,_,_))))
                            | F.Atom(E.Eq(E.AddrArrayT (E.AddrArrayUp(_,_,_)),_))
                            | F.NegAtom(E.InEq(_,E.AddrArrayT(E.AddrArrayUp(_,_,_))))
                            | F.NegAtom(E.InEq(E.AddrArrayT(E.AddrArrayUp(_,_,_)),_)) ->
                                assert (!no_arr_updates); no_arr_updates := false
                            | _ -> ()
                          ) ls
                        end


    let relevant_levels (cf:E.conjunctive_formula) : E.integer GenSet.t =
      let relevant_set = GenSet.empty() in
      match cf with
      | F.TrueConj  -> relevant_set
      | F.FalseConj -> relevant_set
      | F.Conj ls   -> begin
                          E.TermSet.iter (fun t ->
                            match t with
                              (* r = addr2set(m,a,l) *)
                            | E.SetT (E.AddrToSetAt(_,_,i))
                              (* p = getp(m,a1,a2,l) *)
                            | E.PathT (E.GetPathAt(_,_,_,i))
                              (* A = B{l <- a} *)
                            | E.AddrArrayT (E.AddrArrayUp(_,i,_))
                              (* A = B{l <- t} *)
                            | E.TidArrayT (E.TidArrayUp(_,i,_))
                              (* A = B{l <- l} *)
                            | E.LockArrayT (E.LockArrayUp(_,i,_))
                              (* A = B{l <- b} *)
                            | E.BucketArrayT (E.BucketArrayUp(_,i,_))
                              (* a = A[i] *)
                            | E.AddrT (E.AddrArrRd(_,i))
                              (* t = A[i] *)
                            | E.TidT (E.TidArrRd(_,i))
                              (* l = A[i] *)
                            | E.LockT (E.LockArrRd(_,i))
                              (* b = A[i] *)
                            | E.BucketT (E.BucketArrRd(_,i)) -> GenSet.add relevant_set i
                              (* Remaining cases *)
                            | _ -> ()
                          ) (E.termset_from_conj cf);
                          List.iter (fun l ->
                            match l with
                              (* reach(m,a,b,i,p) *)
                            | F.Atom (E.ReachAt(_,_,_,i,_))
                            | F.NegAtom (E.ReachAt(_,_,_,i,_)) -> GenSet.add relevant_set i
                              (* Remaining cases *)
                            | _ -> ()
                          ) ls;
                          relevant_set
                        end


    let propagate_levels (alpha_pairs:alpha_pair_t list)
                         (panc:E.conjunctive_formula)
                         (nc:E.conjunctive_formula)
          : (E.conjunctive_formula * (* Updated panc         *)
             E.conjunctive_formula * (* Updated nc           *)
             alpha_pair_t list) =     (* Updated alpha_pairs    *)
      (* A couple of auxiliary functions *)
      (* Given an integer and a alpha_pair_t list, returns the alpha_pair_t list
         section from the eqclass where i was found in decreasing order *)
      let rec keep_lower_or_equals (i:E.integer) (ps:alpha_pair_t list) : alpha_pair_t list =
        match ps with
        | [] -> []
        | (eqc,_)::xs -> if List.mem i eqc then ps else keep_lower_or_equals i xs in
      let rec find_highest_lower_bound (i:E.integer) (ps:alpha_pair_t list) : E.integer option =
        match ps with
        | [] -> None
        | (_,r)::xs -> if r = None then find_highest_lower_bound i xs else r in
      let filter_non_relevant (cf:E.conjunctive_formula)
                              (relset:E.integer GenSet.t) : E.conjunctive_formula =
        match cf with
        | F.TrueConj  -> F.TrueConj
        | F.FalseConj -> F.FalseConj
        | F.Conj ls   -> begin
                            F.Conj (List.fold_left (fun xs lit ->
                              let v_set = E.varset_of_sort_from_literal lit E.Int in
                              if E.V.VarSet.for_all (fun v -> GenSet.mem relset (E.VarInt v)) v_set then
                                lit :: xs
                              else
                                xs
                            ) [] ls)
                          end in

      (* Main function body *)
      let add_zero = ref false in
      let elems_to_zero = ref [] in
      let replacements = Hashtbl.create 10 in
      let alpha_relevant = GenSet.empty() in
      List.iter (fun (eqclass,r) ->
        match r with
        | None   -> ()
        | Some l -> GenSet.add alpha_relevant l;
                    List.iter (fun e ->
                      Hashtbl.add replacements (E.IntT e) (E.IntT l)
                    ) eqclass
      ) alpha_pairs;
      let propagate_levels_in_conj_formula (cf:E.conjunctive_formula) : E.conjunctive_formula =
        match cf with
        | F.TrueConj -> F.TrueConj
        | F.FalseConj -> F.FalseConj
        | F.Conj ls -> begin
                          let result =
                            F.Conj (List.map (fun lit ->
                              begin
                                match lit with
                                | F.Atom(E.Hashmap(_,_,_,_,l))
                                | F.NegAtom(E.Hashmap(_,_,_,_,l))
                                | F.Atom(E.Skiplist(_,_,l,_,_,_))
                                | F.Atom(E.Eq(_,E.CellT(E.MkSLCell(_,_,_,l))))
                                | F.Atom(E.Eq(E.CellT(E.MkSLCell(_,_,_,l)),_))
                                | F.NegAtom(E.InEq(_,E.CellT(E.MkSLCell(_,_,_,l))))
                                | F.NegAtom(E.InEq(E.CellT(E.MkSLCell(_,_,_,l)),_)) ->
                                    if not (Hashtbl.mem replacements (E.IntT l)) then
                                      let lowers = keep_lower_or_equals l alpha_pairs in
                                      let lower_l = match find_highest_lower_bound l lowers with
                                                    | None   -> (add_zero := true;
                                                                 Log.print "Padding" "adding zero as relevant";
                                                                 Log.print "Padding" ("Integer " ^(E.integer_to_str l)^ " will be mapped to zero");
                                                                 elems_to_zero := l :: !elems_to_zero;
                                                                 E.IntVal 0)
                                                    | Some i -> i in
                                      Hashtbl.add replacements (E.IntT l) (E.IntT lower_l)
                                | _ -> ()
                              end;
                              E.replace_terms_literal replacements lit
                            ) ls) in
                            Log.print "Elements to be mapped to zero" (String.concat ";" (List.map E.integer_to_str !elems_to_zero));
                            result
                          end in
      let new_panc = filter_non_relevant (propagate_levels_in_conj_formula panc) alpha_relevant in
      let new_nc = propagate_levels_in_conj_formula nc in
      let alpha_pairs_with_zero = if !add_zero then
                                    alpha_pairs @ [(!elems_to_zero, Some (E.IntVal 0))]
                                  else
                                    alpha_pairs
      in
        (new_panc, new_nc, alpha_pairs_with_zero)



    let update_arrangement (alpha:E.integer list list) (rel_set:E.integer GenSet.t)
          : (E.integer list * E.integer option) list =
      List.map (fun eqclass ->
        let r = match List.filter (GenSet.mem rel_set) eqclass with
                | [] -> None
                | x::_ -> Some x in
        (eqclass,r)
      ) alpha


    let dnf_sat (lines:int) (co:Smp.cutoff_strategy_t) (cf:E.conjunctive_formula) : Sat.t =
      Log.print_ocaml "entering TSLSolver dnf_sat";
      Log.print "TSLSolver dnf_sat conjunctive formula" (E.conjunctive_formula_to_str cf);
      let arrg_sat_table : (E.integer list list, Sat.t) Hashtbl.t = Hashtbl.create 8 in

      let check_pa (cf:E.conjunctive_formula) : Sat.t =
    (*    print_endline ("PA: " ^ (E.conjunctive_formula_to_str cf)); *)
        try
          Hashtbl.find alpha_sat_table cf
        with Not_found ->
          begin
            match cf with
            | F.TrueConj  -> begin
                               verbl _LONG_INFO "**** check_pa: true\n";
                               Hashtbl.add alpha_sat_table cf Sat.Sat;
                               Sat.Sat
                             end
            | F.FalseConj -> begin
                               verbl _LONG_INFO "**** check_pa: false\n";
                               Hashtbl.add alpha_sat_table cf Sat.Unsat;
                               Sat.Unsat
                             end
            | F.Conj _    -> begin
                               let res = try_sat_with_pa
                                          (F.conjunctive_to_formula cf) in
                               Hashtbl.add alpha_sat_table cf res;
                               res
                             end
          end in


      (* Main verification function *)
      let check (pa:E.conjunctive_formula)
                (panc:E.conjunctive_formula)
                (nc:E.conjunctive_formula)
                (alpha:E.integer list list) : Sat.t =

(*        print_endline ("NC: " ^ (E.conjunctive_formula_to_str nc)); *)

        Log.print_ocaml "entering TSLSolver check";
        Log.print "PA formula" (E.conjunctive_formula_to_str pa);
        Log.print "PANC formula" (E.conjunctive_formula_to_str panc);
        Log.print "NC formula" (E.conjunctive_formula_to_str nc);
        Log.print "Alpha arrangement" (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map E.integer_to_str xs)) ^ "]") alpha));

        Pervasives.flush (Pervasives.stdout);
        let alpha_phi = alpha_to_conjunctive_formula alpha in
        (*
        print_endline ("== PA   : " ^ (E.conjunctive_formula_to_str pa));
        print_endline ("== PANC : " ^ (E.conjunctive_formula_to_str panc));
        print_endline ("== ALPHA: " ^ (E.conjunctive_formula_to_str alpha_phi));
        *)
        let pa_sat = check_pa (F.combine_conjunctive (F.combine_conjunctive pa panc) alpha_phi) in
        (* TODO: Some arrangements are invalid, as I am not considering literals of the
                 form "l2 = l1 + 1" to enforce that l2 should be in the immediately consecutive
                 equivalence class of l1
        assert pa_sat;
        *)
        if Sat.is_sat pa_sat then begin
          (* We have an arrangement candidate *)
          pumping nc;

(*          print_endline ("NC FORMULA: " ^ (E.conjunctive_formula_to_str nc)); *)

          let rel_set = relevant_levels nc in
          Log.print "Relevant levels" (GenSet.to_str E.integer_to_str rel_set);

(*          print_endline ("REL_SET: " ^ (GenSet.to_str E.integer_to_str rel_set)); *)
         

(*
          print_endline ("ALPHA ARRANGEMENT: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map E.integer_to_str xs)) ^ "]") alpha)));
          print_endline ("RELEVANT SET: " ^ (GenSet.to_str E.integer_to_str rel_set));
*)

          let alpha_pairs = update_arrangement alpha rel_set in
          let (panc_r, nc_r, alpha_pairs_r) = propagate_levels alpha_pairs panc nc in


          let alpha_pairs_str =
            String.concat ";" (List.map (fun (xs,mi) ->
              (String.concat "," (List.map E.integer_to_str xs)) ^":"^ (match mi with
                                                                     | Some i -> E.integer_to_str i
                                                                     | None -> "None")
            ) alpha_pairs_r) in

(*          print_endline ("ALPHA_PAIRS: " ^ alpha_pairs_str); *)

          Log.print "ALPHA_PAIRS_R" alpha_pairs_str;
          Log.print "PANC_R" (E.conjunctive_formula_to_str panc_r);
          Log.print "NC_R" (E.conjunctive_formula_to_str nc_r);

(*
          print_endline ("ALPHA_PAIRS_R: " ^ alpha_pairs_str);
          print_endline ("PANC_R: " ^ (E.conjunctive_formula_to_str panc_r));
          print_endline ("NC_R: " ^ (E.conjunctive_formula_to_str nc_r));
*)

          let alpha_r = List.rev (List.fold_left (fun xs (_,r) ->
                                    match r with
                                    | None -> xs
                                    | Some relev -> [relev] :: xs
                                  ) [] alpha_pairs_r) in

          (* Assertions only *)
          let alpha_relev = GenSet.empty () in
(*
          print_endline ("GOING TO PROCESS");
          print_endline ("ALPHA_R SIZE: " ^ (string_of_int (List.length alpha_r)));
*)
          List.iter (fun eqclass ->
(*            print_endline ("CLASS ######################"); *)
            List.iter (fun e -> GenSet.add alpha_relev e) eqclass
          ) alpha_r;

          let rel_set_plus_zero = GenSet.copy rel_set in
          GenSet.add rel_set_plus_zero (E.IntVal 0);
          assert (GenSet.subseteq alpha_relev rel_set_plus_zero);
          let panc_r_level_vars = E.varset_of_sort_from_conj panc_r E.Int in
          let nc_r_level_vars = E.varset_of_sort_from_conj nc_r E.Int in

          Log.print "Alpha relevant" (GenSet.to_str E.integer_to_str alpha_relev);

          if not (E.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (E.VarInt v)) panc_r_level_vars) then begin
            print_endline ("PANC_R_LEVEL_VARS: " ^ (String.concat ";" (List.map E.V.to_str (E.V.VarSet.elements panc_r_level_vars))));
            print_endline ("ALPHA_RELEV: " ^ (GenSet.to_str E.integer_to_str alpha_relev));
            print_endline ("PANC_R: " ^ (E.conjunctive_formula_to_str panc_r));
            print_endline ("ALPHA: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map E.integer_to_str xs)) ^ "]") alpha)));
            print_endline ("PA: " ^ (E.conjunctive_formula_to_str pa));
            print_endline ("PANC: " ^ (E.conjunctive_formula_to_str panc));
            print_endline ("NC: " ^ (E.conjunctive_formula_to_str nc))
          end;

          assert (E.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (E.VarInt v)) panc_r_level_vars);
          if not (E.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (E.VarInt v)) nc_r_level_vars) then begin
            print_endline ("NC_R_LEVEL_VARS: " ^ (String.concat ";" (List.map E.V.to_str (E.V.VarSet.elements nc_r_level_vars))));
            print_endline ("ALPHA_RELEV: " ^ (GenSet.to_str E.integer_to_str alpha_relev));
            print_endline ("NC_R: " ^ (E.conjunctive_formula_to_str nc_r));
            print_endline ("ALPHA: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map E.integer_to_str xs)) ^ "]") alpha)));
            print_endline ("PA: " ^ (E.conjunctive_formula_to_str pa));
            print_endline ("PANC: " ^ (E.conjunctive_formula_to_str panc));
            print_endline ("NC: " ^ (E.conjunctive_formula_to_str nc))
          end;
(*
          E.V.VarSet.iter (fun v -> print_endline ("NC_R_LEVEL: " ^ E.V.to_str v)) nc_r_level_vars;
          GenSet.iter (fun i -> print_endline ("ALPHA_RELEV: " ^ E.integer_to_str i)) alpha_relev;
*)
          assert (E.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (E.VarInt v)) nc_r_level_vars);



          (* Assertions only *)
(*
          print_endline "ALPHA_R";
          List.iter (fun xs -> print_endline (String.concat "," (List.map E.integer_to_str xs))) alpha_r;
*)

          try
            let res = Hashtbl.find arrg_sat_table alpha_r in
    (*        print_endline ("RA: " ^ (E.conjunctive_formula_to_str (alpha_to_conjunctive_formula alpha_r))); *)
            if (LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO)) then
              print_string (if Sat.is_sat res then "$" else "#");
            res
          with Not_found -> begin
            let alpha_r_formula = alpha_to_conjunctive_formula alpha_r in
            let final_formula = List.fold_left F.combine_conjunctive alpha_r_formula [panc_r;nc_r] in
            match final_formula with
            | F.TrueConj  -> (Hashtbl.add arrg_sat_table alpha_r Sat.Sat; Sat.Sat)
            | F.FalseConj -> (Hashtbl.add arrg_sat_table alpha_r Sat.Unsat; Sat.Unsat)
            | F.Conj _    -> AS.check_sp_dp (List.length alpha_r) lines co arrg_sat_table final_formula (Some alpha_r)
          end
        end else begin
          (* For this arrangement is UNSAT. Return UNSAT. *)
          if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
            print_string ".";
          Sat.Unsat
        end in


      (* Main body *)
      let (pa,panc,nc) = split_into_pa_nc cf in
      (* We clear the table of previously guessed arrangements *)
      Hashtbl.clear arr_table;
      (* Generate arrangements *)
      assert (Hashtbl.length arrg_sat_table = 0);
      let answer =
        (* If no interesting information in NC formula, then we just check PA and PANC *)
        if nc = F.TrueConj || nc = F.FalseConj then begin
          try_sat_with_pa
            (F.conjunctive_to_formula
              (F.combine_conjunctive pa panc))
        end else begin
          let arrgs_opt = guess_arrangements (F.combine_conjunctive_list [pa; panc; nc]) in

          Log.print "Guessed arrangement:"
            (match arrgs_opt with
             | None -> "None"
             | Some arr -> 

                GenSet.to_str (fun zs -> (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map E.integer_to_str xs)) ^ "]") zs))) arr);




          (* Verify if some arrangement makes the formula satisfiable *)
          match arrgs_opt with
          | None -> AS.check_sp_dp 1 lines co arrg_sat_table nc None
          | Some arrgs -> if GenSet.exists (fun alpha -> Sat.is_sat (check pa panc nc alpha)) arrgs then
                            Sat.Sat
                          else
                            Sat.Unsat
        end in
      answer
  end
