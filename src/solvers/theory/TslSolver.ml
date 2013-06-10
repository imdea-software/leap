
open LeapLib
open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module SL       = TSLExpression
module SLInterf = TSLInterface
(*module type SLK = TSLKExpression.S *)


exception UnexpectedLiteral of string


let solver_impl = ref ""


let choose (s:string) : unit =
  solver_impl := s


let comp_model : bool ref = ref false
(* Should we compute a model in case of courter example? *)

let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
(* The structure where we store the options for cutoff *)


(* Intermediate model information between TSL solver interface and
   TSLK solver interface *)
let tslk_sort_map = ref (GM.new_sort_map())
let tslk_model = ref (GM.new_model())


let gen_fresh_int_var (vs:SL.VarSet.t) : SL.variable =
  let rec find (n:int) : SL.variable =
    let v_cand_id = "fresh_int_" ^ (string_of_int n) in
    let v_cand = SL.build_var v_cand_id SL.Int false SL.Shared SL.GlobalScope
      in
      if SL.VarSet.mem v_cand vs then find (n+1) else v_cand
  in
    find 0


let sanitize (cf:SL.conjunctive_formula) : SL.conjunctive_formula =
  let find_candidates (ls:SL.literal list)
        : (SL.VarSet.t * SL.VarSet.t)  =
    List.fold_left (fun (cs,ss) l ->
      match l with
      | SL.Atom(SL.Eq(_,SL.CellT(SL.MkCell(_,SL.AddrArrayUp(_,SL.VarInt v1,_),SL.TidArrayUp(_,SL.VarInt v2,_),_)))) ->
          (SL.VarSet.add v1 (SL.VarSet.add v2 cs), ss)
      | SL.Atom(SL.Eq(_,SL.AddrArrayT(SL.AddrArrayUp(_,SL.VarInt v,_))))
      | SL.Atom(SL.Eq(SL.AddrArrayT(SL.AddrArrayUp(_,SL.VarInt v,_)),_))
      | SL.Atom(SL.Eq(_,SL.TidArrayT(SL.TidArrayUp(_,SL.VarInt v,_))))
      | SL.Atom(SL.Eq(SL.TidArrayT(SL.TidArrayUp(_,SL.VarInt v,_)),_))
      | SL.Atom(SL.Eq(_,SL.CellT(SL.MkCell(_,SL.AddrArrayUp(_,SL.VarInt v,_),_,_))))
      | SL.Atom(SL.Eq(_,SL.CellT(SL.MkCell(_,_,SL.TidArrayUp(_,SL.VarInt v,_),_)))) ->
        (SL.VarSet.add v cs, ss)
      | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _), SL.IntT(SL.IntAdd (SL.VarInt v, SL.IntVal 1))))
      | SL.Atom(SL.Eq(SL.IntT(SL.IntAdd (SL.VarInt v, SL.IntVal 1)), SL.IntT (SL.VarInt _))) ->
        (cs, SL.VarSet.add v ss)
      | _ -> (cs, ss)
    ) (SL.VarSet.empty, SL.VarSet.empty) ls
  in
  let fresh_vargen = SL.new_fresh_gen_from_conjformula cf in
  match cf with
  | SL.FalseConj -> cf
  | SL.TrueConj  -> cf
  | SL.Conj ls   -> let (cs,ss) = find_candidates ls in
                        let needs_sanit = SL.VarSet.diff cs ss in
                        let ls' = SL.VarSet.fold (fun v xs ->
                                    let v_new = SL.VarInt (SL.gen_fresh_var fresh_vargen SL.Int) in
                                    (SL.Atom(SL.Eq(SL.IntT v_new, SL.IntT(SL.IntAdd(SL.VarInt v, SL.IntVal 1))))) :: ls
                                  ) needs_sanit ls
                        in
                          SL.Conj ls'


let guess_arrangements_by_brute_force (cf:SL.conjunctive_formula)
      : SL.conjunctive_formula list =
(*  LOG "Entering guess_arrangements..." LEVEL TRACE; *)
  let rec cons_var_eq_class (vs:SL.variable list) : SL.literal list =
    match vs with
    | v1::v2::xs -> SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1), SL.IntT (SL.VarInt v2))) :: cons_var_eq_class (v2::xs)
    | _          -> []
  in
  let rec cons_var_ords (arr:SL.variable list list) : SL.literal list =
    match arr with
    | xs::ys::zs -> SL.Atom(SL.Less(SL.VarInt(List.hd xs),
                              SL.VarInt(List.hd ys))) :: cons_var_ords (ys::zs)
    | _          -> []
  in
  match cf with
  | SL.FalseConj -> []
  | SL.TrueConj  -> []
  | SL.Conj ls   -> verb "**** TSL Solver. Computing level vars from: %s\n"
                              (SL.conjunctive_formula_to_str cf);
                        let level_vars = SL.varset_of_sort_from_conj cf SL.Int in
                        verb "**** TSL Solver. Extracted level vars: %s\n"
                              (String.concat ", " $
                                SL.VarSet.fold (fun v xs ->
                                  (SL.variable_to_str v) :: xs
                                ) level_vars []);
                        verb "**** TSL Solver. Computing partitions...\n";
                        let parts = Partition.gen_partitions
                                      (SL.VarSet.elements level_vars) [] in
                        verb "**** TSL Solver. Computing equalities...\n";
                        let eqs = List.fold_left (fun xs p ->
                                    (Partition.to_list p) :: xs
                                  ) [] parts in
                        verb "**** TSL Solver. Level vars: %i\n"
                              (SL.VarSet.cardinal level_vars);
                        verb "**** TSL Solver. Computing arrangements...\n";
                        let arrgs = List.fold_left (fun xs eq_c ->
                                      (LeapLib.comb eq_c (List.length eq_c)) @ xs
                                    ) [] eqs in
                        verb "**** TSL Solver. Computing level arrangements...\n";
                        let lv_arrs = List.fold_left (fun xs arr ->
                                        let eqs = List.fold_left (fun ys eq_c ->
                                                    (cons_var_eq_class eq_c) @ ys
                                                  ) [] arr in
                                        let ords = cons_var_ords arr
                                        in
                                          (SL.Conj (eqs @ ords)) :: xs
                                      ) [] arrgs
                        in
                          lv_arrs


let alpha_to_conjunctive_formula (alpha:SL.integer list list)
    : SL.conjunctive_formula =
  let rec cons_eq_class (is:SL.integer list) : SL.literal list =
    match is with
    | i1::i2::xs -> SL.Atom(SL.Eq(SL.IntT i1, SL.IntT i2)) :: cons_eq_class (i2::xs)
    | _          -> []
  in
  let rec cons_ords (arr:SL.integer list list) : SL.literal list =
    match arr with
    | xs::ys::zs -> SL.Atom(SL.Less(List.hd ys,
                              List.hd xs)) :: cons_ords (ys::zs)
    | _          -> []
  in
  let eqs = List.fold_left (fun ys eq_c ->
              (cons_eq_class eq_c) @ ys
            ) [] alpha in
  let ords = cons_ords alpha in
    (SL.Conj (eqs @ ords))


let guess_arrangements (cf:SL.conjunctive_formula) : (SL.integer list list) GenSet.t =
  let arr = Arr.empty true in
    match cf with
    | SL.FalseConj -> GenSet.empty ()
    | SL.TrueConj  -> GenSet.empty ()
    | SL.Conj ls   -> begin
                            let level_vars = SL.varset_instances_of_sort_from_conj cf (SL.Int) in
                             verb "**** TSL Solver: variables for arrangement...\n{ %s }\n"
                                    (SL.VarSet.fold (fun v str ->
                                      str ^ SL.variable_to_str v ^ "; "
                                    ) level_vars "");
                            SL.VarSet.iter (fun v -> Arr.add_elem arr (SL.VarInt v)) level_vars;
                            List.iter (fun l ->
                              match l with
                              | SL.Atom(SL.Less(i1,i2)) -> Arr.add_less arr i1 i2
                              | SL.Atom(SL.Greater(i1,i2)) -> Arr.add_greater arr i1 i2
                              | SL.Atom(SL.LessEq(i1,i2)) -> Arr.add_lesseq arr i1 i2
                              | SL.Atom(SL.GreaterEq(i1,i2)) -> Arr.add_greatereq arr i1 i2
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                              | SL.Atom(SL.Eq(SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                  if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i)))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2)))))
                              | SL.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                              | SL.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                  let v1 = SL.var_set_param (SL.Local th) varr in
                                  if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.Atom(SL.Eq(SL.IntT(SL.VarInt v),SL.IntT(SL.IntVal 0)))
                              | SL.Atom(SL.Eq(SL.IntT(SL.IntVal 0),SL.IntT(SL.VarInt v))) ->
                                  Arr.set_minimum arr (SL.VarInt v)
                              | SL.Atom(SL.Eq(SL.IntT i1,SL.IntT i2)) -> Arr.add_eq arr i1 i2
                              | SL.Atom(SL.InEq(SL.IntT i1,SL.IntT i2)) -> Arr.add_ineq arr i1 i2
                              | SL.NegAtom(SL.Less(i1,i2)) -> Arr.add_greatereq arr i1 i2
                              | SL.NegAtom(SL.Greater(i1,i2)) -> Arr.add_lesseq arr i1 i2
                              | SL.NegAtom(SL.LessEq(i1,i2)) -> Arr.add_greater arr i1 i2
                              | SL.NegAtom(SL.GreaterEq(i1,i2)) -> Arr.add_less arr i1 i2
                              | SL.NegAtom(SL.Eq(SL.IntT i1,SL.IntT i2)) -> Arr.add_ineq arr i1 i2
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i))))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2))))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                  if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i)))))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2)))))
                              | SL.NegAtom(SL.InEq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                              | SL.NegAtom(SL.InEq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                  let v1 = SL.var_set_param (SL.Local th) varr in
                                  if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt v),SL.IntT(SL.IntVal 0)))
                              | SL.NegAtom(SL.InEq(SL.IntT(SL.IntVal 0),SL.IntT(SL.VarInt v))) ->
                                  Arr.set_minimum arr (SL.VarInt v)
                              | SL.NegAtom(SL.InEq(SL.IntT i1,SL.IntT i2)) -> Arr.add_eq arr i1 i2
                              | _ -> ()
                            ) ls;
                            verb "**** TSL Solver: known information for arrangments:\n%s\n"
                                  (Arr.to_str arr SL.int_to_str);
                            let arrgs = Arr.gen_arrs arr in
                            verb "**** TSL Solver: generated %i arragements\n" (GenSet.size arrgs);
                            arrgs
                          end


let split (cf:SL.conjunctive_formula)
      : SL.conjunctive_formula * SL.conjunctive_formula =
  match cf with
  | SL.TrueConj  -> (SL.TrueConj,  SL.TrueConj)
  | SL.FalseConj -> (SL.FalseConj, SL.FalseConj)
  | SL.Conj cf   ->
      let (pa,nc) = List.fold_left (fun (pas,ncs) l ->
                      match l with
                        (* l = q *)
                      | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.IntVal _)))
                      | SL.Atom(SL.Eq(SL.IntT(SL.IntVal _),SL.IntT(SL.VarInt _)))
                      | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.IntVal _)))
                      | SL.NegAtom(SL.InEq(SL.IntT(SL.IntVal _),SL.IntT(SL.VarInt _))) -> (l::pas,ncs)
                        (* l1 = l2 *)
                      | SL.Atom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
                      | SL.NegAtom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
                        (* l1 = l2 + 1*)
                      | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.VarInt _, SL.IntVal 1))))
                      | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.IntVal 1, SL.VarInt _))))
                      | SL.Atom(SL.Eq(SL.IntT(SL.IntAdd(SL.VarInt _,SL.IntVal 1)),SL.IntT(SL.VarInt _)))
                      | SL.Atom(SL.Eq(SL.IntT(SL.IntAdd(SL.IntVal 1,SL.VarInt _)),SL.IntT(SL.VarInt _)))
                      | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.VarInt _, SL.IntVal 1))))
                      | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.IntVal 1, SL.VarInt _))))
                      | SL.NegAtom(SL.InEq(SL.IntT(SL.IntAdd(SL.VarInt _,SL.IntVal 1)),SL.IntT(SL.VarInt _)))
                      | SL.NegAtom(SL.InEq(SL.IntT(SL.IntAdd(SL.IntVal 1,SL.VarInt _)),SL.IntT(SL.VarInt _)))
                        (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
                      | SL.Atom(SL.Less(SL.VarInt _,SL.VarInt _))
                      | SL.Atom(SL.Greater(SL.VarInt _,SL.VarInt _))
                      | SL.NegAtom(SL.LessEq(SL.VarInt _,SL.VarInt _))
                      | SL.NegAtom(SL.GreaterEq(SL.VarInt _,SL.VarInt _))
                        (* But l1 <= l2 literals appear, as well as they are not compared to constants *)
                      | SL.Atom(SL.LessEq(SL.VarInt _,SL.VarInt _))
                      | SL.Atom(SL.GreaterEq(SL.VarInt _,SL.VarInt _))
                      | SL.NegAtom(SL.Less(SL.VarInt _,SL.VarInt _))
                      | SL.NegAtom(SL.Greater(SL.VarInt _,SL.VarInt _)) -> (l::pas,l::ncs)
                        (* Cases that should not appear at this point after normalization *)
                      | SL.Atom(SL.Less(SL.IntVal _,_))          | SL.Atom(SL.Less(_,SL.IntVal _))
                      | SL.Atom(SL.Greater(SL.IntVal _,_))       | SL.Atom(SL.Greater(_,SL.IntVal _))
                      | SL.NegAtom(SL.LessEq(SL.IntVal _,_))     | SL.NegAtom(SL.LessEq(_,SL.IntVal _))
                      | SL.NegAtom(SL.GreaterEq(SL.IntVal _,_))  | SL.NegAtom(SL.GreaterEq(_,SL.IntVal _))
                      | SL.Atom(SL.LessEq(SL.IntVal _,_))        | SL.Atom(SL.LessEq(_,SL.IntVal _))
                      | SL.Atom(SL.GreaterEq(SL.IntVal _,_))     | SL.Atom(SL.GreaterEq(_,SL.IntVal _))
                      | SL.NegAtom(SL.Less(SL.IntVal _,_))       | SL.NegAtom(SL.Less(_,SL.IntVal _))
                      | SL.NegAtom(SL.Greater(SL.IntVal _,_))    | SL.NegAtom(SL.Greater(_,SL.IntVal _)) ->
                          assert false
                        (* Remaining cases *)
                      | _ -> (pas,l::ncs)
                    ) ([],[]) cf
      in
        (SL.Conj pa, SL.Conj nc)


module TranslateTsl (SLK : TSLKExpression.S) =
  struct

    module SLKInterf = TSLKInterface.Make(SLK)


    (* The tables containing addresses and thread identifiers variables
       representing arrays *)
    let addrarr_tbl : (SL.addrarr, SLK.addr list) Hashtbl.t =
      Hashtbl.create 10
    let tidarr_tbl : (SL.tidarr, SLK.tid list) Hashtbl.t =
      Hashtbl.create 10


    let tid_tsl_to_tslk (t:SL.tid) : SLK.tid =
      SLKInterf.tid_to_tslk_tid(SLInterf.tid_to_expr_tid t)

    let term_tsl_to_term (t:SL.term) : SLK.term =
      SLKInterf.term_to_tslk_term(SLInterf.term_to_expr_term t)

    let set_tsl_to_tslk (s:SL.set) : SLK.set =
      SLKInterf.set_to_tslk_set(SLInterf.set_to_expr_set s)

    let elem_tsl_to_tslk (e:SL.elem) : SLK.elem =
      SLKInterf.elem_to_tslk_elem(SLInterf.elem_to_expr_elem e)

    let addr_tsl_to_tslk (a:SL.addr) : SLK.addr =
      SLKInterf.addr_to_tslk_addr(SLInterf.addr_to_expr_addr a)

    let cell_tsl_to_tslk (c:SL.cell) : SLK.cell =
      SLKInterf.cell_to_tslk_cell(SLInterf.cell_to_expr_cell c)

    let setth_tsl_to_tslk (s:SL.setth) : SLK.setth =
      SLKInterf.setth_to_tslk_setth(SLInterf.setth_to_expr_setth s)

    let setelem_tsl_to_tslk (s:SL.setelem) : SLK.setelem =
      SLKInterf.setelem_to_tslk_setelem(SLInterf.setelem_to_expr_setelem s)

    let path_tsl_to_tslk (p:SL.path) : SLK.path =
      SLKInterf.path_to_tslk_path(SLInterf.path_to_expr_path p)

    let mem_tsl_to_tslk (m:SL.mem) : SLK.mem =
      SLKInterf.mem_to_tslk_mem(SLInterf.mem_to_expr_mem m)

    let int_tsl_to_tslk (i:SL.integer) : SLK.level =
      SLKInterf.int_to_tslk_level(SLInterf.int_to_expr_int i)

    let literal_tsl_to_tslk (l:SL.literal) : SLK.literal =
      SLKInterf.literal_to_tslk_literal(SLInterf.literal_to_expr_literal l)


    let expand_array_to_var (v:SL.variable)
                            (s:SLK.sort)
                            (n:int) : SLK.variable =
      let id_str = SL.var_id v in
      let pr_str = if SL.var_is_primed v then "_prime" else "" in
      let th_str = match SL.var_parameter v with
                   | SL.Shared -> ""
                   | SL.Local tid -> "_" ^ (SL.tid_to_str tid) in
      let p_str = match SL.var_scope v with
                  | SL.GlobalScope -> ""
                  | SL.Scope p -> p ^ "_" in
      let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
      let v_fresh = SLK.build_var new_id s false SLK.Shared SLK.GlobalScope in
      verb "FRESH VAR: %s\n" new_id;
      SLK.variable_mark_fresh v_fresh true;
      v_fresh


    let gen_addr_list (aa:SL.addrarr) : SLK.addr list =
      let xs = ref [] in
      for n = (SLK.k - 1) downto 0 do
        let v = match aa with
                | SL.VarAddrArray v ->
                    SLK.VarAddr (expand_array_to_var v SLK.Addr n)
                | SL.CellArr c ->
                    let l = SLK.LevelVal n in
                    SLK.NextAt(cell_tsl_to_tslk c, l)
                | _ -> SLK.Null in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated address list for %s: [%s]\n"
              (SL.addrarr_to_str aa)
              (String.concat ";" (List.map SLK.addr_to_str !xs));
      !xs


    let gen_tid_list (tt:SL.tidarr) : SLK.tid list =
      let xs = ref [] in
      for n = (SLK.k - 1) downto 0 do
        let v = match tt with
                | SL.VarTidArray v ->
                    SLK.VarTh (expand_array_to_var v SLK.Thid n)
                | SL.CellTids c ->
                    let l = SLK.LevelVal n in
                    SLK.CellLockIdAt(cell_tsl_to_tslk c, l)
                | _ -> SLK.NoThid in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated thread id list for %s: [%s]\n"
              (SL.tidarr_to_str tt)
              (String.concat ";" (List.map SLK.tid_to_str !xs));
      !xs



    let get_addr_list (aa:SL.addrarr) : SLK.addr list =
      try
        Hashtbl.find addrarr_tbl aa
      with _ -> begin
        let aa' = gen_addr_list aa in
        Hashtbl.add addrarr_tbl aa aa'; aa'
      end


    let get_tid_list (tt:SL.tidarr) : SLK.tid list =
      try
        Hashtbl.find tidarr_tbl tt
      with _ -> begin
        let tt' = gen_tid_list tt in
        Hashtbl.add tidarr_tbl tt tt'; tt'
      end


    let rec trans_literal (l:SL.literal) : SLK.formula =
      verb "**** TSL Solver. Literal to be translated: %s\n"
            (SL.literal_to_str l);
      match l with
      (* c = mkcell(e,k,A,l) *)
      | SL.Atom(SL.Eq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.Atom(SL.Eq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c)))
      | SL.NegAtom(SL.InEq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.NegAtom(SL.InEq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c))) ->
          let c' = cell_tsl_to_tslk (SL.VarCell c) in
          let e' = elem_tsl_to_tslk e in
          let aa' = get_addr_list aa in
          let tt' = get_tid_list tt in
            SLK.eq_cell (c') (SLK.MkCell(e',aa',tt'))
      (* c != mkcell(e,k,A,l) *)
      | SL.NegAtom(SL.Eq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.NegAtom(SL.Eq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c)))
      | SL.Atom(SL.InEq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.Atom(SL.InEq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c))) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.CellT(SL.VarCell c), SL.CellT(SL.MkCell(e,aa,tt,i))))))
      (* a = c.arr[l] *)
      | SL.Atom(SL.Eq(SL.AddrT a, SL.AddrT(SL.AddrArrRd(SL.CellArr c,l))))
      | SL.Atom(SL.Eq(SL.AddrT(SL.AddrArrRd(SL.CellArr c,l)), SL.AddrT a))
      | SL.NegAtom(SL.InEq(SL.AddrT a, SL.AddrT(SL.AddrArrRd(SL.CellArr c,l))))
      | SL.NegAtom(SL.InEq(SL.AddrT(SL.AddrArrRd(SL.CellArr c,l)), SL.AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          SLK.addr_mark_smp_interesting a' true;
          SLK.eq_addr a' (SLK.NextAt(c',l'))
      (* t = c.tids[l] *)
      | SL.Atom(SL.Eq(SL.ThidT t, SL.ThidT(SL.ThidArrRd(SL.CellTids c,l))))
      | SL.Atom(SL.Eq(SL.ThidT(SL.ThidArrRd(SL.CellTids c,l)), SL.ThidT t))
      | SL.NegAtom(SL.InEq(SL.ThidT t, SL.ThidT(SL.ThidArrRd(SL.CellTids c,l))))
      | SL.NegAtom(SL.InEq(SL.ThidT(SL.ThidArrRd(SL.CellTids c,l)), SL.ThidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          SLK.tid_mark_smp_interesting t' true;
          SLK.eq_tid t' (SLK.CellLockIdAt(c',l'))
      (* A != B (addresses) *)
      | SL.NegAtom(SL.Eq(SL.AddrArrayT(SL.VarAddrArray _ as aa),
                   SL.AddrArrayT(SL.VarAddrArray _ as bb)))
      | SL.Atom(SL.InEq(SL.AddrArrayT(SL.VarAddrArray _ as aa),
                  SL.AddrArrayT(SL.VarAddrArray _ as bb))) ->
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for i = 0 to (SLK.k - 1) do
            xs := (SLK.ineq_addr (List.nth aa' i) (List.nth bb' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          SLK.addr_mark_smp_interesting (List.hd aa') true;
          SLK.disj_list (!xs)
      (* A != B (thread identifiers) *)
      | SL.NegAtom(SL.Eq(SL.TidArrayT(SL.VarTidArray _ as tt),
                   SL.TidArrayT(SL.VarTidArray _ as uu)))
      | SL.Atom(SL.InEq(SL.TidArrayT(SL.VarTidArray _ as tt),
                  SL.TidArrayT(SL.VarTidArray _ as uu))) ->
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for i = 0 to (SLK.k - 1) do
            xs := (SLK.ineq_tid (List.nth tt' i) (List.nth uu' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          SLK.tid_mark_smp_interesting (List.hd tt') true;
          SLK.disj_list (!xs)
      (* a = A[i] *)
      | SL.Atom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.Atom(SL.Eq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a))
      | SL.NegAtom(SL.InEq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.NegAtom(SL.InEq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let aa' = get_addr_list aa in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          SLK.conj_list (!xs)
      (* a != A[i] *)
      | SL.NegAtom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.NegAtom(SL.Eq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a))
      | SL.Atom(SL.InEq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.Atom(SL.InEq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))))
      (* t = A[i] *)
      | SL.Atom(SL.Eq(SL.ThidT t, SL.ThidT (SL.ThidArrRd (tt,i))))
      | SL.Atom(SL.Eq(SL.ThidT (SL.ThidArrRd (tt,i)), SL.ThidT t))
      | SL.NegAtom(SL.InEq(SL.ThidT t, SL.ThidT (SL.ThidArrRd (tt,i))))
      | SL.NegAtom(SL.InEq(SL.ThidT (SL.ThidArrRd (tt,i)), SL.ThidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let tt' = get_tid_list tt in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_tid t' (List.nth tt' n))) :: (!xs)
          done;
          SLK.tid_mark_smp_interesting t' true;
          SLK.conj_list (!xs)
      (* t != A[i] *)
      | SL.NegAtom(SL.Eq(SL.ThidT t, SL.ThidT (SL.ThidArrRd (tt,i))))
      | SL.NegAtom(SL.Eq(SL.ThidT (SL.ThidArrRd (tt,i)), SL.ThidT t))
      | SL.Atom(SL.InEq(SL.ThidT t, SL.ThidT (SL.ThidArrRd (tt,i))))
      | SL.Atom(SL.InEq(SL.ThidT (SL.ThidArrRd (tt,i)), SL.ThidT t)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.ThidT t, SL.ThidT (SL.ThidArrRd (tt,i))))))
      (* B = A {l <- a} *)
      | SL.Atom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.Atom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb))
      | SL.NegAtom(SL.InEq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.NegAtom(SL.InEq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb)) ->
          let a' = addr_tsl_to_tslk a in
          let i' = int_tsl_to_tslk i in
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth bb' n))) ::
                  (SLK.Implies
                    (SLK.ineq_level i' n',
                     SLK.eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                  (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          SLK.conj_list (!xs)
      (* B != A {l <- a} *)
      | SL.NegAtom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.NegAtom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb))
      | SL.Atom(SL.InEq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.Atom(SL.InEq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))))
      (* U = T {l <- t} *)
      | SL.Atom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.Atom(SL.Eq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu))
      | SL.NegAtom(SL.InEq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.NegAtom(SL.InEq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu)) ->
          let t' = tid_tsl_to_tslk t in
          let i' = int_tsl_to_tslk i in
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_tid t' (List.nth uu' n))) ::
                  (SLK.Implies
                    (SLK.ineq_level i' n',
                     SLK.eq_tid (List.nth tt' n) (List.nth uu' n))) ::
                  (!xs)
          done;
          SLK.tid_mark_smp_interesting t' true;
          SLK.conj_list (!xs)
      (* U != T {l <- t} *)
      | SL.NegAtom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.NegAtom(SL.Eq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu))
      | SL.Atom(SL.InEq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.Atom(SL.InEq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))))
      (* Skiplist (m,s,l,s1,s2) *)
      | SL.Atom(SL.Skiplist(m,s,l,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in
          let xs = ref
                    [SLK.Literal(SLK.Atom(
                      SLK.OrderList(m',a1',a2')));
                     SLK.eq_set
                      (s')
                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in
(*                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in *)
(*
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0),
                                          SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in
*)
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := SLK.Implies
                    (SLK.lesseq_level n' l',
                     SLK.And (SLK.atomlit 
                                  (SLK.In(a2',SLK.AddrToSet(m',a1',n'))),
                                  SLK.eq_addr (SLK.NextAt(SLK.CellAt(m',a2'),n'))
                                                   SLK.Null)) :: (!xs);
          done;
          for n = 0 to (SLK.k - 2) do
            let n' = SLK.LevelVal n in
            xs := SLK.Implies
                    (SLK.less_level n' l',
                     SLK.subseteq
                       (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                       (SLK.AddrToSet(m',a1',n'))) :: (!xs)
(*
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelSucc n')))
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',n')))) :: (!xs)*)
(*
                       (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelSucc n'), SLK.AddrToSet(m',a2',SLK.LevelSucc n')))
                       (SLK.Setdiff (SLK.AddrToSet(m',a1',n'), SLK.AddrToSet(m',a2',n')))) :: (!xs)
*)

          done;
          SLK.addr_mark_smp_interesting a1' true;
          SLK.addr_mark_smp_interesting a2' true;
          SLK.conj_list (!xs)
      (* ~ Skiplist(m,s,l,a1,a2) *)
      | SL.NegAtom(SL.Skiplist(m,s,l,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in


          let xs = ref
                    [SLK.Literal(SLK.NegAtom(
                      SLK.OrderList(m',a1',a2')));
                     SLK.ineq_set
                      (s')
                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in
(*                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in *)
(*                      (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0), SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in *)
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := SLK.And
                    (SLK.lesseq_level n' l',
                     SLK.Or (SLK.Not (SLK.atomlit (SLK.In (a2', SLK.AddrToSet(m',a1',n')))),
                                 SLK.ineq_addr (SLK.NextAt(SLK.CellAt(m',a2'),n'))
                                                    SLK.Null)) :: (!xs)
          done;
          for n = 0 to (SLK.k - 2) do
            let n' = SLK.LevelVal n in
            xs := SLK.And
                    (SLK.less_level n' l',
                     SLK.Not
                      (SLK.subseteq
                        (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                        (SLK.AddrToSet(m',a1',n')))) :: (!xs)

(*
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelSucc n')))
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',n'))))) :: (!xs)
*)
(*
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelSucc n'), SLK.AddrToSet(m',a2',SLK.LevelSucc n')))
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',n'), SLK.AddrToSet(m',a2',n'))))) :: (!xs)
*)
          done;
          SLK.addr_mark_smp_interesting a1' true;
          SLK.addr_mark_smp_interesting a2' true;
          SLK.disj_list (!xs)
      | _ -> SLK.Literal (literal_tsl_to_tslk l)


    let to_tslk (tsl_ls:SL.literal list) : SLK.formula =
      verbstr (Interface.Msg.info "TSL CONJUNCTIVE FORMULA TO TRANSLATE"
        (String.concat "\n" (List.map SL.literal_to_str tsl_ls)));
      Hashtbl.clear addrarr_tbl;
      Hashtbl.clear tidarr_tbl;
      let tslk_ps = List.map trans_literal tsl_ls in
      let tslk_phi = SLK.conj_list tslk_ps in
      verbstr (Interface.Msg.info "OBTAINED TSLK TRANSLATED FORMULA"
        (SLK.formula_to_str tslk_phi));
      tslk_phi
  end



let check_sat_by_cases (lines:int)
                       (co : Smp.cutoff_strategy_t)
                       (cases:(SL.conjunctive_formula *                   (* PA formula  *)
                               SL.conjunctive_formula *                   (* NC formula  *)
                               (SL.integer list list) GenSet.t) list)     (* Arrangements *)
      : (bool * int * int) =

  (* PA satisfiability check function *)
  let check_pa (cf:SL.conjunctive_formula) : bool =
    match cf with
    | SL.TrueConj  -> (verb "**** check_pa: true\n"; true)
    | SL.FalseConj -> (verb "**** check_pa: false\n"; false)
    | SL.Conj ls   ->
        let numSolv_id = BackendSolvers.Yices.identifier in
        let module NumSol = (val NumSolver.choose numSolv_id : NumSolver.S) in
        let phi_num = NumInterface.formula_to_int_formula
                        (SLInterf.formula_to_expr_formula
                          (SL.from_conjformula_to_formula
                            cf))
        in
        verb "**** TSL Solver will check satisfiability for:\n%s\n"
                  (NumExpression.formula_to_str phi_num);
        NumSol.is_sat phi_num in


  (* NC satisfiability check function *)
  let check_nc (cf:SL.conjunctive_formula) (i:int) : bool =
    match cf with
    | SL.TrueConj  -> true
    | SL.FalseConj -> false
    | SL.Conj ls ->
        (* A more efficient way of computing the K is to count the number
           of equivalence classes in the guessed arrangement. Note that we
           have previously added as many level variables as we require.
           Then, if the arrangement contains an assertion of the form
           "l1 = l2" there is no need to add both variables when computing
           K, as they will remain to be equal when the SMT will try to
           compute the model. *)
        (*
           let l_vs = varset_of_sort_from_conj cf Int in
           let k = VarSet.cardinal l_vs in
         *)
        let k = if i = -1 then
                  SL.VarSet.cardinal (SL.varset_of_sort_from_conj cf SL.Int)
                else
                  i in
(*
        let module TslkSol = (val TslkSolver.choose "Z3" k
*)
        let module TslkSol = (val TslkSolver.choose !solver_impl k
                                         : TslkSolver.S) in
        TslkSol.compute_model (!comp_model);
        let module Trans = TranslateTsl (TslkSol.TslkExp) in
        verb "**** TSL Solver, about to translate TSL to TSLK...\n";
        let phi_tslk = Trans.to_tslk ls in
        verb "**** TSL Solver, TSL to TSLK translation done...\n";
        let res = TslkSol.is_sat lines co phi_tslk in
        tslk_sort_map := TslkSol.get_sort_map ();
        tslk_model := TslkSol.get_model ();
        res in


  (* General satisfiability function *)
  let rec check (pa:SL.conjunctive_formula)
                (nc:SL.conjunctive_formula)
                (alpha:SL.integer list list) : bool =
    verb "BEGIN CHECK\n";
    let alpha_phi = alpha_to_conjunctive_formula alpha in
    verb "CONJUNCTIVE CREATED\n";
    verb "**** TSL Solver. Check PA formula\n%s\nand NC formula\n%s\nwith arrangement\n%s\n"
          (SL.conjunctive_formula_to_str pa)
          (SL.conjunctive_formula_to_str nc)
          (SL.conjunctive_formula_to_str alpha_phi);
    let pa_sat = check_pa (SL.combine_conj_formula pa alpha_phi) in
    verb "**** TSL Solver, PA sat?: %b\n" pa_sat;
    if pa_sat then
      (* Check NC /\ alpha satisfiability *)
      let i = ref (List.length alpha) in
      let explicit_levels = List.fold_left (fun xs eqclass ->
                              decr i;
                              (List.map (fun e -> SL.Atom(SL.Eq(SL.IntT e,SL.IntT(SL.IntVal !i)))) eqclass) @ xs
                            ) [] alpha in
      let explicit_levels_phi = match explicit_levels with
                                | [] -> SL.TrueConj
                                | _  -> SL.Conj explicit_levels in
      (* HERE PUT THE LEVEL ENUMERATION *)
      let levels = List.length alpha in
      let _ = verb "**** TSL Solver will combine candidate arrangement wit NC.\n" in
      check_nc (SL.combine_conj_formula (SL.combine_conj_formula nc alpha_phi) explicit_levels_phi) levels
    else
      false in

  (* Main call *)
  let tslk_calls = ref 0 in
  Printf.printf "CASES SIZE: %i\n" (List.length cases);
  let rec check_aux cs =
    verb "CHECK_AUX WITH CASES: %i\n" (List.length cases);
    match cs with
    | [] -> (false, 1, !tslk_calls)
    | (pa,nc,arrgs)::xs -> begin
                             let this_case = if GenSet.size arrgs = 0 then
                                               check pa nc []
                                             else
                                               GenSet.exists (check pa nc) arrgs in
                             if this_case then
                               (true, 1, !tslk_calls)
                             else
                               check_aux xs
                           end
  in
    check_aux cases


let rec combine_splits_arrgs (sp:(SL.conjunctive_formula * SL.conjunctive_formula) list)
                             (arrgs:((SL.integer list list) GenSet.t) list) :
            (SL.conjunctive_formula *
             SL.conjunctive_formula *
             (SL.integer list list) GenSet.t) list =
  verb "SP SIZE: %i\n" (List.length sp);
  verb "ARRGS SIZE: %i\n" (List.length arrgs);
  match (sp,arrgs) with
  | ([],[])                -> []
  | ((pa,nc)::xs,arrg::ys) -> (pa,nc,arrg)::(combine_splits_arrgs xs ys)
  | _ -> assert false


let is_sat_plus_info (lines : int)
           (co : Smp.cutoff_strategy_t)
           (phi : SL.formula) : (bool * int * int) =
  (* 0. Normalize the formula and rewrite it in DNF *)
  verb "**** Will normalize TSL formula...\n";
  let phi_norm = SL.normalize phi in
  verbstr (Interface.Msg.info "NORMALIZED FORMULA" (SL.formula_to_str phi_norm));
  verb "**** Will do DNF on TSL formula...\n";
  let phi_dnf = SL.dnf phi_norm in
  verbstr (Interface.Msg.info "DNF RESULT"
    (String.concat "\n" (List.map SL.conjunctive_formula_to_str phi_dnf)));
  (* 1. Sanitize the formula *)
  verb "**** Will sanitize TSL formula...\n";
  let phi_san = List.map sanitize phi_dnf in
  verbstr (Interface.Msg.info "SANITARIZED FORMULAS"
    (String.concat "\n" (List.map SL.conjunctive_formula_to_str phi_san)));
  (* 2. Guess arrangements *)
  let arrgs = List.map guess_arrangements phi_san in
  (* 3. Split each conjunction into PA y NC *)
  verb "**** Will split TSL formula in NC and PA...\n";
  let splits = List.map split phi_san in
  verbstr (Interface.Msg.info "SPLITED FORMULAS"
    (String.concat "\n" (List.map (fun (pa,nc) -> "PA:\n" ^ (SL.conjunctive_formula_to_str pa) ^
                                                  "NC:\n" ^ (SL.conjunctive_formula_to_str nc)) splits)));
  (* 4. Call the solver for each possible case *)
  verb "**** Will check TSL formula satisfiability...\n";
  let (sat,tsl_calls,tslk_calls) = check_sat_by_cases lines co
                                      (combine_splits_arrgs splits arrgs)
  in
    (sat, tsl_calls, tslk_calls)


let is_sat (lines : int)
           (co : Smp.cutoff_strategy_t)
           (phi : SL.formula) : bool =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = is_sat_plus_info lines co phi in s


let is_valid_plus_info (prog_lines:int)
                       (co:Smp.cutoff_strategy_t)
                       (phi:SL.formula) : (bool * int * int) =
  let (s,tsl_count,tslk_count) = is_sat_plus_info prog_lines co
                                   (SL.Not phi) in
    (not s, tsl_count, tslk_count)


let is_valid (prog_lines:int)
             (co:Smp.cutoff_strategy_t)
             (phi:SL.formula) : bool =
  not (is_sat prog_lines co (SL.Not phi))


let compute_model (b:bool) : unit =
  comp_model := b
    (* Should I enable which solver? *)
    (* Solver.compute_model b *)
    (* Perhaps I should only set the flag and set activate the compute_model
       on the Solver when it is about to be called in is_sat *)


let model_to_str () : string =
  let model = !tslk_model in
  let sort_map = !tslk_sort_map in
  let thid_str = GM.search_type_to_str model sort_map GM.tid_s in
  let pc_str   = GM.search_type_to_str model sort_map GM.loc_s in
  let addr_str = GM.search_type_to_str model sort_map GM.addr_s in
  let elem_str = GM.search_type_to_str model sort_map GM.elem_s in
  let cell_str = GM.search_type_to_str model sort_map GM.cell_s in
  let path_str = GM.search_type_to_str model sort_map GM.path_s in
  let level_str = GM.search_type_to_str model sort_map GM.level_s in
  (* Special description for sets *)
  let set_str = GM.search_sets_to_str model sort_map GM.set_s in
  let setth_str = GM.search_sets_to_str model sort_map GM.setth_s in
  let setelem_str = GM.search_sets_to_str model sort_map GM.setelem_s in
  (* Special description for sets *)
  let heap_str = GM.search_type_to_str model sort_map GM.heap_s
  in
    "\nThreads:\n" ^ thid_str ^
    "\nProgram counters:\n" ^ pc_str ^
    "\nAddresses:\n" ^ addr_str ^
    "\nElements:\n" ^ elem_str ^
    "\nCells:\n" ^ cell_str ^
    "\nPaths:\n" ^ path_str ^
    "\nLevels:\n" ^ level_str ^
    "\nSets:\n" ^ set_str ^
    "\nSets of tids:\n" ^ setth_str ^
    "\nSets of elements:\n" ^ setelem_str ^
    "\nHeap:\n" ^ heap_str


let print_model () : unit =
  if !comp_model then
    print_endline (model_to_str())
  else
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
