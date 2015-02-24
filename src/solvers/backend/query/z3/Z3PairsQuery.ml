open PairsQuery
open LeapLib


module Z3PairsQuery : PAIRS_QUERY =

struct
  module E=Expression
  module PE=PairsExpression
  module PI=PairsInterface
  module B = Buffer
  module GM = GenericModel
  module F = Formula


  exception NotSupportedInZ3 of string
  exception UntypedVariable of string
  exception Not_implemented of string


  (* Configuration *)
  let pc_prime_name : string = Conf.pc_name ^ "_prime"
  let aux_int       : string = "ai_"
  let undefInt      : string = "undefined_int"


  (* Program lines *)
  let prog_lines : int ref = ref 0


  (* Sort names *)
  let int_s     : string = "Int"
  let pair_s    : string = "Pair"
  let tid_s     : string = "Tid"
  let set_s     : string = "Set"
  let setpair_s : string = "SetPair"
  let bool_s    : string = "Bool"
  let loc_s     : string = "Loc"


  (* Information storage *)
  let sort_map : GM.sort_map_t = GM.new_sort_map()


  (* Program lines manipulation *)
  let set_prog_lines (n:int) : unit =
    prog_lines := n


  (* Translation funtions *)
  let pairs_varid_to_str (v:E.V.id) : string =
    let _ = GM.sm_decl_const sort_map v GM.int_s
    in
      Printf.sprintf "(declare-const %s %s)\n" v int_s


  let pairs_local_varid_to_str (v:E.V.id) : string =
    let _ = GM.sm_decl_fun sort_map v [GM.tid_s] [GM.int_s]
    in
      Printf.sprintf "(declare-const %s (Array %s %s))\n" v tid_s int_s


  let pairs_var_to_str (v:PE.V.t) : string =
    let pr_str = if (PE.V.is_primed v) then "_prime" else ""
    in
      match PE.V.scope v with
      | PE.V.GlobalScope -> pairs_varid_to_str ((PE.V.id v) ^ pr_str)
      | PE.V.Scope ""    -> pairs_varid_to_str ((PE.V.id v) ^ pr_str)
      | PE.V.Scope p     -> pairs_local_varid_to_str (p^"_"^(PE.V.id v)^pr_str)


  let rec pairs_varlist_to_str (vl:PE.V.t list) : string =
    let add_th th set = match th with
                        | PE.V.Shared  -> set
                        | PE.V.Local t -> PE.ThreadSet.add (PE.VarTh t) set in
    let (t_set,v_set) = List.fold_left (fun (ts,vs) v ->
                          (add_th (PE.V.parameter v) ts,
                           PE.V.VarSet.add (PE.V.unparam v) vs)
                        ) (PE.ThreadSet.empty, PE.V.VarSet.empty) vl in
    let th_str = if PE.ThreadSet.cardinal t_set <> 0 then
                   "(declare-sort " ^tid_s^ ")\n" ^
                      PE.ThreadSet.fold (fun t str ->
                        let t_str = tid_to_str t in
                        let _ = GM.sm_decl_const sort_map t_str GM.tid_s
                        in
                          str ^ (Printf.sprintf "(declare-const %s %s)\n" t_str tid_s)
                   ) t_set ""
                 else
                   ""
    in
      List.fold_left (fun str v ->
        str ^ (pairs_var_to_str v)
      ) th_str (PE.V.VarSet.elements v_set)


  and procedure_name_to_append (proc:PE.V.procedure_name) : string =
    match proc with
    | PE.V.GlobalScope -> ""
    | PE.V.Scope "" -> ""
    | PE.V.Scope p  -> p ^ "_"


  and variable_to_str (v:PE.V.t) : string =
    let pr_str = if (PE.V.is_primed v) then "_prime" else "" in
    let th_str = match (PE.V.parameter v) with
                 | PE.V.Shared  -> ""
                 | PE.V.Local t -> "_" ^ (PE.V.to_str t) in
    let p_str = procedure_name_to_append (PE.V.scope v)
    in
      Printf.sprintf "%s%s%s%s" p_str (PE.V.id v) th_str pr_str


  and var_sort_to_str (v:PE.V.t) : string =
    match (PE.V.sort v) with
    | PE.Int     -> int_s
    | PE.Pair    -> pair_s
    | PE.Set     -> set_s
    | PE.SetPair -> setpair_s
    | PE.Tid     -> tid_s


  and var_sort_to_gmsort_str (v:PE.V.t) : string =
    match (PE.V.sort v) with
      PE.Int     -> GM.int_s
    | PE.Pair    -> GM.pair_s
    | PE.Set     -> GM.set_s
    | PE.SetPair -> GM.setpair_s
    | PE.Tid     -> GM.tid_s


  and var_to_str (v:PE.V.t) : string =
    let v_str = variable_to_str v in
    let sort_str = var_sort_to_str v in
    let gm_sort_str = var_sort_to_gmsort_str v in
    let _ = GM.sm_decl_const sort_map v_str gm_sort_str
    in
      Printf.sprintf "(declare-const %s %s)\n" v_str sort_str


  and tid_to_str (t:PE.tid) : string =
    let pair_str = z3_string_of_pair in
    match t with
    | PE.VarTh v       -> variable_to_str v
    | PE.PairTid p     -> "(tid_of " ^pair_str p^ ")"
    | PE.NoTid         -> "NoTid"


  and shared_or_local_to_str (th:PE.V.shared_or_local) : string =
    match th with
    | PE.V.Shared  -> ""
    | PE.V.Local t -> PE.V.to_str t


  and fun_to_str (f:PE.fun_term) : string =
    match f with
      PE.FunVar v ->
        if (PE.V.parameter v) = PE.V.Shared then
          variable_to_str v
        else
          let v_str  = variable_to_str (PE.V.unparam v) in
          let th_str = shared_or_local_to_str (PE.V.parameter v)
          in
            Printf.sprintf "(%s %s)" v_str th_str
    | PE.FunUpd (f,th,i) ->
        let f_str = fun_to_str f in
        let th_str = tid_to_str th in
        let i_str = z3_string_of_term i
        in
          Printf.sprintf "(store %s %s %s)" f_str th_str i_str


  and z3_string_of_integer (t:PE.integer) : string =
    let constanttostr t =
      match t with
          PE.Val(n) -> string_of_int n
        | _ -> raise(NotSupportedInZ3(PE.integer_to_str t)) in
    let tostr = z3_string_of_integer in
      match t with
        PE.Val(n)       -> " " ^ string_of_int n
      | PE.Var(v)       -> variable_invocation_to_str v
      | PE.Neg(x)       -> " -" ^  (constanttostr x)
      | PE.Add(x,y)     -> " (+ " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.Sub(x,y)     -> " (- " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.Mul(x,y)     -> " (* " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.Div(x,y)     -> " (/ " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.ArrayRd(_,_) -> raise(NotSupportedInZ3(PE.integer_to_str t))
      | PE.SetMin(s)    -> " (setmin " ^ z3_string_of_set s ^ ")"
      | PE.SetMax(s)    -> " (setmax " ^ z3_string_of_set s ^ ")"
      | PE.PairInt(p)   -> " (int_of " ^ z3_string_of_pair p ^ ")"


  and z3_string_of_pair (p:PE.pair) : string =
    let z3_int = z3_string_of_integer in
    let z3_setpair = z3_string_of_setpair in
    match p with
      PE.VarPair (v)      -> variable_invocation_to_str v
    | PE.IntTidPair (i,t) -> "(mk-pair " ^ z3_int i^ " " ^ tid_to_str t^ ")"
    | PE.SetPairMin (ps)  -> "(spmin " ^ z3_setpair ps ^ ")"
    | PE.SetPairMax (ps)  -> "(spmax " ^ z3_setpair ps ^ ")"


  and z3_string_of_set (s:PE.set) : string =
    let z3_int = z3_string_of_integer in
    let z3_set = z3_string_of_set in
    match s with
      PE.VarSet (v)   -> variable_invocation_to_str v
    | PE.EmptySet     -> " emp"
    | PE.Singl i      -> Printf.sprintf "(singleton %s)" (z3_int i)
    | PE.Union(s1,s2) -> Printf.sprintf "(unionset %s %s)" (z3_set s1) (z3_set s2)
    | PE.Intr(s1,s2)  -> Printf.sprintf "(intersection %s %s)" (z3_set s1) (z3_set s2)
    | PE.Diff(s1,s2)  -> Printf.sprintf "(setdiff %s %s)" (z3_set s1) (z3_set s2)
    | PE.Lower(s,i)   -> Printf.sprintf "(subsetLowerThan %s %s)" (z3_set s) (z3_int i)


  and z3_string_of_setpair (s:PE.setpair) : string =
    let z3_int = z3_string_of_integer in
    let z3_pair = z3_string_of_pair in
    let z3_setpair = z3_string_of_setpair in
    match s with
      PE.VarSetPair (v)     -> variable_invocation_to_str v
    | PE.EmptySetPair       -> " spempty"
    | PE.SinglPair p        -> Printf.sprintf "(spsingle %s)" (z3_pair p)
    | PE.UnionPair(s1,s2)   -> Printf.sprintf "(spunion %s %s)" (z3_setpair s1)
                                                                (z3_setpair s2)
    | PE.IntrPair(s1,s2)    -> Printf.sprintf "(spintr %s %s)" (z3_setpair s1)
                                                               (z3_setpair s2)
    | PE.SetdiffPair(s1,s2) -> Printf.sprintf "(spdiff %s %s)" (z3_setpair s1)
                                                               (z3_setpair s2)
    | PE.LowerPair(s,i)     -> Printf.sprintf "(splower %s %s)" (z3_setpair s)
                                                                (z3_int i)


  and z3_string_of_term (t:PE.term) : string =
    match t with
      PE.IntV i -> z3_string_of_integer i
    | PE.PairV p -> z3_string_of_pair p
    | PE.SetV s -> z3_string_of_set s
    | PE.SetPairV s -> z3_string_of_setpair s


  and z3_string_of_atom a =
    let int_tostr = z3_string_of_integer in
    let pair_tostr = z3_string_of_pair in
    let set_tostr = z3_string_of_set in
    let setpair_tostr = z3_string_of_setpair in
    let term_tostr = z3_string_of_term in
      match a with
        PE.Less(x,y)      -> " (< "  ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.Greater(x,y)   -> " (> "  ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.LessEq(x,y)    -> " (<= " ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.GreaterEq(x,y) -> " (>= " ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.LessTid(x,y)   -> " (tid order support for z3 not added yet )"
      | PE.Eq(x,y)        -> " (= "  ^ (term_tostr x) ^ (term_tostr y) ^ ")"
      | PE.InEq(x,y)      -> " (not (=" ^ (term_tostr x) ^ (term_tostr y) ^ "))"
      | PE.In(i,s)        -> " (select " ^ set_tostr s ^ " " ^ int_tostr i ^ ")"
      | PE.Subset(s1,s2)  -> " (subseteq " ^ set_tostr s1 ^ " " ^ set_tostr s2 ^ ")"
      | PE.InPair(i,s)        -> " (" ^ setpair_tostr s ^ " " ^ pair_tostr i ^ ")"
      | PE.SubsetEqPair(s1,s2)  -> " (spsubseteq " ^ setpair_tostr s1 ^ " " ^ setpair_tostr s2 ^ ")"
      | PE.TidEq(x,y)     -> " (= "  ^ (tid_to_str x) ^ " " ^
                                            (tid_to_str y) ^ ")"
      | PE.TidInEq(x,y)   -> " (not (= " ^ (tid_to_str x) ^ " " ^
                                           (tid_to_str y) ^ "))"
      | PE.FunEq(x,y)     -> " (= "  ^ (fun_to_str x) ^ " " ^
                                            (fun_to_str y) ^ ")"
      | PE.FunInEq(x,y)   -> " (not (= " ^ (fun_to_str x) ^ " " ^
                                           (fun_to_str y) ^ "))"
      | PE.PC (i,th,pr)   -> " " ^ z3_string_of_pos (i,th,pr) ^ " "
      | PE.PCUpdate(i,th) -> " " ^ z3_string_of_posupd (i,th) ^ " "
      | PE.PCRange (i,j,th,pr) -> " " ^ z3_string_of_posrange (i,j,th,pr) ^ " "

  and string_of_literal l =
    match l with
      F.Atom a    -> z3_string_of_atom a
    | F.NegAtom a -> "(not "^ z3_string_of_atom a ^")"

  and string_of_formula  phi =
    let tostr = string_of_formula in
      match phi with
        F.Literal(l)   -> string_of_literal l
      | F.True         -> " true "
      | F.False        -> " false "
      | F.And(a,b)     -> " (and " ^ (tostr a) ^ (tostr b) ^ ")"
      | F.Or(a,b)      -> " (or "  ^ (tostr a) ^ (tostr b) ^ ")"
      | F.Not(a)       -> " (not " ^ (tostr a) ^ ")"
      | F.Implies(a,b) -> " (=> "  ^ (tostr a) ^ (tostr b) ^ ")"
      | F.Iff(a,b)     -> " (= "   ^ (tostr a) ^ (tostr b) ^ ")"



  and tid_variable_to_str (th:PE.tid) : string =
    let t_str = tid_to_str th in
    let _ = GM.sm_decl_const sort_map t_str GM.tid_s
    in
      Printf.sprintf "(declare-const %s %s)\n" t_str tid_s


  and local_var_to_str (v:PE.V.t) : string =
    let v_str = variable_to_str v in
    let v_sort = var_sort_to_str v in
    let gm_v_sort = var_sort_to_gmsort_str v in
    let _ = GM.sm_decl_fun sort_map v_str [GM.tid_s] [gm_v_sort]
    in
      Printf.sprintf "(declare-const %s (Array %s %s))\n" v_str tid_s v_sort


  and z3_string_of_pos (pc:(int * PE.V.shared_or_local * bool)) : string =
    let (i, th, pr) = pc in
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(= (%s %s) %i)" pc_str th_str i


  and z3_string_of_posrange (pc:(int * int * PE.V.shared_or_local * bool)) : string =
    let (i, j, th, pr) = pc in
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(and (<= %i (%s %s)) (<= (%s %s) %i))"
          i pc_str th_str pc_str th_str j


  and z3_string_of_posupd (pc:(int * PE.tid)) : string =
    let (i, th) = pc
    in
      Printf.sprintf "(= %s (store %s %s %i))" pc_prime_name Conf.pc_name
                                           (tid_to_str th) i


  and variable_invocation_to_str (v:PE.V.t) : string =
    let th_str = shared_or_local_to_str (PE.V.parameter v) in
    let p_str  = procedure_name_to_append (PE.V.scope v) in
    let pr_str = if (PE.V.is_primed v) then "_prime" else ""
    in
      match (PE.V.parameter v) with
      | PE.V.Shared  -> Printf.sprintf " %s%s%s%s" p_str (PE.V.id v) th_str pr_str
  (* For LEAP *)
      | PE.V.Local _ -> Printf.sprintf " (%s%s%s %s)" p_str (PE.V.id v) pr_str th_str
  (* For numinv *)
  (*    | PE.V.Local _ -> Printf.sprintf " %s%s%s_%s" p_str (PE.V.id v) pr_str th_str *)




  (************************** Support for sets **************************)

  let z3_type_decl (buf:Buffer.t) : unit =
    B.add_string buf ("(declare-sort " ^tid_s^ ")\n");
    B.add_string buf ("(define-sort " ^set_s^ " () (Array " ^int_s^ " " ^bool_s^ "))\n");
    B.add_string buf ("(declare-datatypes () ((" ^pair_s^ " (mk-pair (first " ^int_s^ ") (second " ^tid_s^ ")))))\n");
    B.add_string buf ("(define-sort " ^setpair_s^ " () (Array " ^pair_s^ " " ^bool_s^ "))\n");
    B.add_string buf ("(define-sort " ^loc_s^ " () " ^int_s^ ")\n")


  let z3_undefined_decl (buf:Buffer.t) : unit =
    let _ = GM.sm_decl_const sort_map undefInt GM.int_s in
      B.add_string buf ("(declare-const " ^ undefInt ^ " " ^ int_s ^ ")\n");
      B.add_string buf ("(define-fun is_legal ((i " ^int_s^ ")) " ^bool_s^ "\n" ^
                        "  (not (= i " ^undefInt^ ")))\n")


  let z3_emp_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(declare-const emp " ^set_s^ ")\n" ^
       "(assert (= emp ((as const " ^set_s^ " ) false)))\n")


  let z3_singleton_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define-fun singleton ((i " ^int_s^ ")) " ^set_s^ "\n" ^
        "  (store emp i true))\n")


  let z3_union_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define-fun unionset ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^set_s^ "\n" ^
        "  ((_ map or) s1 s2))\n")


  let z3_setdiff_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define-fun setdiff ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^set_s^ "\n" ^
        "  ((_ map and) s1 ((_ map not) s2)))\n")


  let z3_intersection_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define-fun intersection ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^set_s^ "\n" ^
     "  ((_ map and) s1 s2))\n")


  let z3_subseteq_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define-fun subseteq ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^bool_s^ "\n" ^
         "  (= (intersection s1 s2) s1))\n")




  let z3_spemp_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(declare-const spempty " ^setpair_s^ ")\n" ^
       "(assert (= spempty ((as const " ^setpair_s^ " ) false)))\n")


  let z3_spsingleton_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define-fun spsingle ((p " ^pair_s^ ")) " ^setpair_s^ "\n" ^
        "  (store spempty p true))\n")


  let z3_spunion_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define-fun spunion ((s1 " ^setpair_s^ ") (s2 " ^setpair_s^ ")) " ^setpair_s^ "\n" ^
        "  ((_ map or) s1 s2))\n")


  let z3_spsetdiff_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define-fun spdiff ((s1 " ^setpair_s^ ") (s2 " ^setpair_s^ ")) " ^setpair_s^ "\n" ^
        "  ((_ map and) s1 ((_ map not) s2)))\n")


  let z3_spintersection_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define-fun spintr ((s1 " ^setpair_s^ ") (s2 " ^setpair_s^ ")) " ^setpair_s^ "\n" ^
     "  ((_ map and) s1 s2))\n")


  let z3_spsubseteq_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define-fun spsubseteq ((s1 " ^setpair_s^ ") (s2 " ^setpair_s^ ")) " ^bool_s^ "\n" ^
         "  (= (spintr s1 s2) s1))\n")

       
  let z3_is_min_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define-fun is_min ((int_v " ^int_s^ ") (set_v " ^set_s^ ")) " ^bool_s^ "\n" ^
         "  (and");
    List.iter (fun v ->
      B.add_string buf
        (Printf.sprintf "\n    (if (select set_v %s) (<= int_v %s) true)" v v)
    ) vars_rep;
    B.add_string buf "))\n"


  let z3_is_max_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define-fun is_max ((int_v " ^int_s^ ") (set_v " ^set_s^ ")) " ^bool_s^ "\n" ^
         "  (and") ;
    List.iter (fun v ->
      B.add_string buf
        (Printf.sprintf "\n    (if (select set_v %s) (>= int_v %s) true)" v v)
    ) vars_rep;
    B.add_string buf "))\n"


  let z3_min_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define-fun setmin ((set_v " ^set_s^ ")) " ^int_s ^
      List.fold_left (fun str v ->
        Printf.sprintf ("\n  (if (and (select set_v %s) (is_min %s set_v)) %s %s)")
          v v v str
      ) undefInt vars_rep ^
     ")\n")


  let z3_max_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define-fun setmax ((set_v " ^set_s^ ")) " ^int_s^
      List.fold_left (fun str v ->
        Printf.sprintf ("\n  (if (and (select set_v %s) (is_max %s set_v)) %s %s)")
          v v v str
      ) undefInt vars_rep ^
     ")\n")


  let z3_is_spmin_def (vars_rep:string list) (voc_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define-fun is_spmin ((pair_v " ^pair_s^ ") (setpair_v " ^setpair_s^ ")) " ^bool_s^ "\n" ^
         "  (and");
    List.iter (fun v ->
      List.iter (fun t ->
        B.add_string buf
          (Printf.sprintf "\n    (if (select setpair_v (mk-pair %s %s)) (<= (first pair_v) %s) true)" v t v)
      ) voc_rep
    ) vars_rep;
    B.add_string buf "))\n"


  let z3_is_spmax_def (vars_rep:string list) (voc_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define-fun is_spmax ((pair_v " ^pair_s^ ") (setpair_v " ^setpair_s^ ")) " ^bool_s^ "\n" ^
         "  (and") ;
    List.iter (fun v ->
      List.iter (fun t ->
        B.add_string buf
          (Printf.sprintf "\n    (if (select setpair_v (mk-pair %s %s)) (>= (first pair_v) %s) true)" v t v)
      ) voc_rep
    ) vars_rep;
    B.add_string buf "))\n"


  let z3_spmin_def (vars_rep:string list) (voc_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define-fun spmin ((setpair_v " ^setpair_s^ ")) " ^pair_s ^
      List.fold_left (fun str v ->
        List.fold_left (fun str t ->
          let pair_rep = "(mk-pair " ^v^ " " ^t^ ")" in
          Printf.sprintf ("\n  (if (and (select setpair_v %s) (is_spmin %s setpair_v)) %s %s)")
            pair_rep pair_rep pair_rep str
        ) str voc_rep
      ) undefInt vars_rep ^
     ")\n")


  let z3_spmax_def (vars_rep:string list) (voc_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define-fun spmax ((setpair_v " ^setpair_s^ ")) " ^pair_s^
      List.fold_left (fun str v ->
        List.fold_left (fun str t ->
          let pair_rep = "(mk-pair " ^v^ " " ^t^ ")" in
          Printf.sprintf ("\n  (if (and (select setpair_v %s) (is_spmax %s setpair_v)) %s %s)")
            pair_rep pair_rep pair_rep str
        ) str voc_rep
      ) undefInt vars_rep ^
     ")\n")


  let z3_intof_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(define-fun int_of ((pair_v " ^pair_s^ ")) " ^int_s^ "\n" ^
       "  (first pair_v))\n")

  let z3_tidof_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(define-fun tid_of ((pair_v " ^pair_s^ ")) " ^tid_s^ "\n" ^
       "  (second pair_v))\n")


  let z3_filter_set_def (vars_rep:string list) (buf:Buffer.t) : unit =
    let univ = List.fold_left (fun str v ->
                 "\n  (store " ^str^ " " ^v^ " true)"
               ) "emp" vars_rep in
    B.add_string buf
      ("(declare-const var_universe " ^set_s^ ")" ^
       "(assert (= var_universe\n " ^univ^ "))" ^
       "(define-fun filter_set ((s1 " ^set_s^ ")) " ^set_s^ "\n" ^
       "  (intersection s1 var_universe))\n")


  let z3_lower_def (vars_rep:string list) (buf:Buffer.t) : unit =
    let low_set = List.fold_left (fun str v ->
                    "\n  (store " ^str^ " " ^v^ " (and (select set_v " ^v^ ") (<= " ^v^ " pairs_v)))"
                  ) "emp" vars_rep in
    B.add_string buf
    ("(define-fun subsetLowerThan ((set_v " ^set_s^ ") (pairs_v " ^int_s^ ")) " ^set_s^
     "  " ^low_set^ ")\n")


  let z3_splower_def (vars_rep:string list) (voc_rep:string list) (buf:Buffer.t) : unit =
    let low_set = List.fold_left (fun str v ->
                    List.fold_left (fun str t ->
                      "\n  (store " ^str^ " (mk-pair " ^v^ " " ^t^ ") (and (select setpair_v (mk-pair " ^v^ " " ^t^ " )) (<= " ^v^ " int_v)))"
                    ) str voc_rep
                  ) "emp" vars_rep in
    B.add_string buf
    ("(define-fun splower ((setpair_v " ^setpair_s^ ") (int_v " ^int_s^ ")) " ^setpair_s^
     "  " ^low_set^ ")\n")


  (************************** Support for sets **************************)


  (************************ Preamble definitions ************************)

  let z3_pc_def (pc_vars:string list) (buf:Buffer.t) : unit =
    GM.sm_decl_fun sort_map Conf.pc_name [GM.tid_s] [GM.loc_s];
    GM.sm_decl_fun sort_map pc_prime_name [GM.tid_s] [GM.loc_s];
    List.iter (fun pc ->
      B.add_string buf
        ("(assert (and (<= 0 " ^pc^ ") (<= " ^pc^ " " ^(string_of_int !prog_lines)^ ") ))\n");
    ) pc_vars


  let z3_aux_pairs_def (cutoff:int) (buf:Buffer.t) : unit =
    let i_list = LeapLib.rangeList 1 cutoff in
    List.iter (fun i ->
      let i_name = aux_int ^ string_of_int i in
      let i_var = PE.build_var i_name PE.Int false PE.V.Shared PE.V.GlobalScope in
      B.add_string buf (var_to_str i_var)
    ) i_list


  let z3_legal_values (global_vars:PE.V.t list)
                         (local_vars:PE.V.t list)
                         (voc:PE.tid list)
                         (buf:Buffer.t) : unit =
    List.iter (fun v ->
      match PE.V.sort v with
      | PE.Int -> let v_str = variable_invocation_to_str v in
                    B.add_string buf ("(assert (is_legal " ^ v_str ^ "))\n")
      | PE.Set -> let v_str = variable_invocation_to_str v in
                    B.add_string buf ("(assert (= " ^v_str^ " (filter_set " ^v_str^ ")))\n")
      | _ -> ()
    ) global_vars;
    List.iter (fun v ->
      List.iter (fun t->
        match PE.V.sort v with
        | PE.Int -> let v_str = variable_invocation_to_str
                          (PE.V.set_param v (PE.V.Local (PE.voc_to_var t))) in
                      B.add_string buf ("(assert (is_legal " ^ v_str ^ "))\n")
        | PE.Set -> let v_str = variable_invocation_to_str
                          (PE.V.set_param v (PE.V.Local (PE.voc_to_var t))) in
                      B.add_string buf ("(assert (= " ^v_str^ " (filter_set " ^v_str^ ")))\n")
        | _ -> ()
      ) voc
    ) local_vars


  (* TODO: Verify, if no set is defined, then do not include the preamble for sets *)
  let z3_preamble (buf:Buffer.t)
                     (voc:PE.tid list)
                     (cutoff:int)
                     (pc_vars:PE.V.t list)
                     (gbl_pairs_vars:PE.V.t list)
                     (lcl_pairs_vars:PE.V.t list) : unit =
    let loc_vars_str = List.flatten $ List.map (fun t ->
                         List.map (fun v ->
                           variable_invocation_to_str(PE.V.set_param v (PE.V.Local (PE.voc_to_var t)))
                         ) lcl_pairs_vars
                       ) voc in
    let glb_vars_str = List.map variable_invocation_to_str gbl_pairs_vars in
    let pc_vars_str = List.map variable_invocation_to_str pc_vars in
    let aux_vars_str = List.map (fun i ->
                         let i_name = aux_int ^ string_of_int i in
                         let i_var = PE.build_var i_name PE.Int
                                        false PE.V.Shared PE.V.GlobalScope
                         in
                           variable_invocation_to_str i_var
                       ) (LeapLib.rangeList 1 cutoff) in
    let all_vars_str = glb_vars_str @ loc_vars_str @ aux_vars_str in
    let voc_str = List.map tid_to_str voc
    in
      z3_undefined_decl                     buf;
      z3_aux_pairs_def cutoff               buf;
      z3_emp_def                            buf;
      z3_singleton_def                      buf;
      z3_union_def                          buf;
      z3_setdiff_def                        buf;
      z3_intersection_def                   buf;
      z3_subseteq_def all_vars_str          buf;
      z3_spemp_def                          buf;
      z3_spsingleton_def                    buf;
      z3_spunion_def                        buf;
      z3_spsetdiff_def                      buf;
      z3_spintersection_def                 buf;
      z3_spsubseteq_def all_vars_str        buf;
      z3_is_min_def all_vars_str            buf;
      z3_is_max_def all_vars_str            buf;
      z3_min_def all_vars_str               buf;
      z3_max_def all_vars_str               buf;
      z3_is_spmin_def all_vars_str voc_str  buf;
      z3_is_spmax_def all_vars_str voc_str  buf;
      z3_spmin_def all_vars_str voc_str     buf;
      z3_spmax_def all_vars_str voc_str     buf;
      z3_intof_def                          buf;
      z3_tidof_def                          buf;
      z3_filter_set_def all_vars_str        buf;
      z3_lower_def all_vars_str             buf;
      z3_splower_def all_vars_str voc_str   buf;
      z3_pc_def pc_vars_str                 buf



  (************************ Preamble definitions ************************)


  let tid_decl_to_str (voc:PE.tid list) : string =
    let id_list = List.map (fun t ->
                    match t with
                    | PE.VarTh v -> (PE.V.id v)
                    | PE.NoTid  -> "NoThread"
                    | PE.PairTid p -> "(tid_of " ^ z3_string_of_pair p ^ ")"
                  ) voc in
    "(declare-datatypes () (( " ^tid_s^ " " ^(String.concat " " id_list)^ ")))\n"


  let pairs_locVarlist_to_str (vars:PE.V.VarSet.t) : string =
    PE.V.VarSet.fold (fun v str -> str ^ local_var_to_str v) vars ""


  let pairs_formula_to_str (phi:PE.formula) : string =
    let _ = GM.clear_sort_map sort_map in
    (*  if direct then *)
    let vars        = PE.all_vars phi in
    let var_str     = pairs_varlist_to_str vars in
    let formula_str = "(assert " ^ (string_of_formula phi) ^ ")\n(check-sat)\n" in
      var_str ^ formula_str


  let pairs_formula_with_lines_to_str (phi:PE.formula) : string =
    let _ = GM.clear_sort_map sort_map in
    let filter_ints xs = List.filter (fun v ->
                           (PE.V.sort v) = PE.Int
                         ) xs in
    let filter_global_ints xs = List.fold_left (fun (ps,gs) v ->
                                  if PE.treat_as_pc v then
                                    (v::ps, gs)
                                  else if (PE.V.sort v = PE.Int) then
                                    (ps, v::gs)
                                  else
                                    (ps, gs)
                                ) ([],[]) xs in
    let voc            = PE.voc phi in
    let cutoff         = SmpPairs.cut_off phi in
    let global_vars    = PE.all_global_vars phi in
    let local_vars     = PE.all_local_vars_without_param phi in
    let (pc_vars, glb_pairs_vars) = filter_global_ints global_vars in
    let lcl_pairs_vars   = filter_ints local_vars in
    let buf            = B.create 1024 in
    let _              = z3_type_decl buf in
    let _              = List.iter (fun v ->
                           B.add_string buf (tid_variable_to_str v)
                         ) voc in
    let _              = List.iter (fun v ->
                           B.add_string buf (var_to_str v)
                         ) global_vars in
    let _              = List.iter (fun v ->
                          B.add_string buf (local_var_to_str v)
                         ) local_vars in
    let _              = z3_preamble buf voc cutoff
                            pc_vars glb_pairs_vars lcl_pairs_vars in
    let _              = z3_legal_values global_vars local_vars voc buf in
    let _              = B.add_string buf ("(assert " ^ (string_of_formula phi) ^
                                            ")\n(check-sat)\n")
    in
      B.contents buf
   

  let get_sort_map () : GM.sort_map_t =
    GM.copy_sort_map sort_map

end
