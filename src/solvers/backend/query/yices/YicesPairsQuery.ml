
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


open PairsQuery
open LeapLib


module YicesPairsQuery : PAIRS_QUERY =

struct
  module E=Expression
  module PE=PairsExpression
  module PI=PairsInterface
  module B = Buffer
  module GM = GenericModel
  module F = Formula
  module MS = ModelSize


  exception NotSupportedInYices of string


  (* Configuration *)
  let pc_prime_name : string = Conf.pc_name ^ "'"
  let aux_int       : string = "ai_"
  let undefInt      : string = "undefined_int"
  let someTid       : string = "someTid"


  (* Program lines *)
  let prog_lines : int ref = ref 0


  (* Sort names *)
  let int_s : string = "myint"
  let pair_s : string = "pair"
  let tid_s : string = "tid"
  let set_s : string = "set"
  let setpair_s : string = "setpair"
  let bool_s : string = "bool"
  let loc_s : string = "loc"


  (* Information storage *)
  let sort_map : GM.sort_map_t = GM.new_sort_map()


  (* Program lines manipulation *)
  let set_prog_lines (n:int) : unit =
    prog_lines := n


  (* Translation funtions *)
  let pairs_varid_to_str (v:E.V.id) : string =
    let _ = GM.sm_decl_const sort_map v GM.int_s
    in
      Printf.sprintf "(define %s::%s)\n" v int_s


  let pairs_local_varid_to_str (v:E.V.id) : string =
    let _ = GM.sm_decl_fun sort_map v [GM.tid_s] [GM.int_s]
    in
      Printf.sprintf "(define %s::(-> %s %s))\n" v tid_s int_s


  let pairs_var_to_str (v:PE.V.t) : string =
    let pr_str = if (PE.V.is_primed v) then "'" else ""
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
                   "(define-type " ^tid_s^ ")\n" ^
                      PE.ThreadSet.fold (fun t str ->
                        let t_str = tid_to_str t in
                        let _ = GM.sm_decl_const sort_map t_str GM.tid_s
                        in
                          str ^ (Printf.sprintf "(define %s::%s)\n" t_str tid_s)
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
    let pr_str = if (PE.V.is_primed v) then "'" else "" in
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
      Printf.sprintf "(define %s::%s)\n" v_str sort_str


  and tid_to_str (t:PE.tid) : string =
    let pair_str = yices_string_of_pair in
    match t with
    | PE.VarTh v       -> variable_to_str v
    | PE.NoTid         -> "NoTid"
    | PE.PairTid p     -> "(select " ^pair_str p^ " tid_of)"


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
        let i_str = yices_string_of_term i
        in
          Printf.sprintf "(update %s (%s) %s)" f_str th_str i_str


  and yices_string_of_integer (t:PE.integer) : string =
    let constanttostr t =
      match t with
          PE.Val(n) -> string_of_int n
        | _ -> raise(NotSupportedInYices(PE.integer_to_str t)) in
    let tostr = yices_string_of_integer in
      match t with
        PE.Val(n)       -> " " ^ string_of_int n
      | PE.Var(v)       -> variable_invocation_to_str v
      | PE.Neg(x)       -> " -" ^  (constanttostr x)
      | PE.Add(x,y)     -> " (+ " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.Sub(x,y)     -> " (- " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.Mul(x,y)     -> " (* " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.Div(x,y)     -> " (/ " ^ (tostr x) ^ (tostr y) ^ ")"
      | PE.ArrayRd(_,_) -> raise(NotSupportedInYices(PE.integer_to_str t))
      | PE.SetMin(s)    -> " (setmin " ^ yices_string_of_set s ^ ")"
      | PE.SetMax(s)    -> " (setmax " ^ yices_string_of_set s ^ ")"
      | PE.PairInt(p)   -> " (select " ^ yices_string_of_pair p ^ " int_of)"


  and yices_string_of_pair (p:PE.pair) : string =
    let yices_int = yices_string_of_integer in
    let yices_setpair = yices_string_of_setpair in
    match p with
      PE.VarPair (v)      -> variable_invocation_to_str v
    | PE.IntTidPair (i,t) -> "(mk-record int_of::" ^ yices_int i^ " tid_of::" ^ tid_to_str t^ ")"
    | PE.SetPairMin (ps)  -> "(spmin " ^ yices_setpair ps ^ ")"
    | PE.SetPairMax (ps)  -> "(spmax " ^ yices_setpair ps ^ ")"


  and yices_string_of_set (s:PE.set) : string =
    let yices_int = yices_string_of_integer in
    let yices_set = yices_string_of_set in
    match s with
      PE.VarSet (v)   -> variable_invocation_to_str v
    | PE.EmptySet     -> " emp"
    | PE.Singl i      -> Printf.sprintf "(singleton %s)" (yices_int i)
    | PE.Union(s1,s2) -> Printf.sprintf "(union %s %s)" (yices_set s1) (yices_set s2)
    | PE.Intr(s1,s2)  -> Printf.sprintf "(intersection %s %s)" (yices_set s1) (yices_set s2)
    | PE.Diff(s1,s2)  -> Printf.sprintf "(setdiff %s %s)" (yices_set s1) (yices_set s2)
    | PE.Lower(s,i)   -> Printf.sprintf "(subsetLowerThan %s %s)" (yices_set s) (yices_int i)


  and yices_string_of_setpair (s:PE.setpair) : string =
    let yices_int = yices_string_of_integer in
    let yices_pair = yices_string_of_pair in
    let yices_setpair = yices_string_of_setpair in
    match s with
      PE.VarSetPair (v)     -> variable_invocation_to_str v
    | PE.EmptySetPair       -> " spempty"
    | PE.SinglPair p        -> Printf.sprintf "(spsingle %s)" (yices_pair p)
    | PE.UnionPair(s1,s2)   -> Printf.sprintf "(spunion %s %s)" (yices_setpair s1)
                                                                (yices_setpair s2)
    | PE.IntrPair(s1,s2)    -> Printf.sprintf "(spintr %s %s)" (yices_setpair s1)
                                                               (yices_setpair s2)
    | PE.SetdiffPair(s1,s2) -> Printf.sprintf "(spdiff %s %s)" (yices_setpair s1)
                                                               (yices_setpair s2)
    | PE.LowerPair(s,i)     -> Printf.sprintf "(splower %s %s)" (yices_setpair s)
                                                                (yices_int i)


  and yices_string_of_term (t:PE.term) : string =
    match t with
      PE.IntV i -> yices_string_of_integer i
    | PE.PairV p -> yices_string_of_pair p
    | PE.SetV s -> yices_string_of_set s
    | PE.SetPairV s -> yices_string_of_setpair s


  and yices_string_of_atom a =
    let int_tostr = yices_string_of_integer in
    let pair_tostr = yices_string_of_pair in
    let set_tostr = yices_string_of_set in
    let setpair_tostr = yices_string_of_setpair in
    let term_tostr = yices_string_of_term in
      match a with
        PE.Less(x,y)      -> " (< "  ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.Greater(x,y)   -> " (> "  ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.LessEq(x,y)    -> " (<= " ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.GreaterEq(x,y) -> " (>= " ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | PE.LessTid _      -> " (tid order support for yices not added yet )"
      | PE.Eq(x,y)        -> " (= "  ^ (term_tostr x) ^ (term_tostr y) ^ ")"
      | PE.InEq(x,y)      -> " (/= " ^ (term_tostr x) ^ (term_tostr y) ^ ")"
      | PE.In(i,s)        -> " (" ^ set_tostr s ^ " " ^ int_tostr i ^ ")"
      | PE.Subset(s1,s2)  -> " (subseteq " ^ set_tostr s1 ^ " " ^ set_tostr s2 ^ ")"
      | PE.InPair(i,s)        -> " (" ^ setpair_tostr s ^ " " ^ pair_tostr i ^ ")"
      | PE.SubsetEqPair(s1,s2)  -> " (spsubseteq " ^ setpair_tostr s1 ^ " " ^ setpair_tostr s2 ^ ")"
      | PE.InTidPair(t,s) -> " (intidpair " ^ tid_to_str t ^ " " ^ setpair_tostr s ^ ")"
      | PE.InIntPair(i,s) -> " (inintpair " ^ int_tostr i ^ " " ^ setpair_tostr s ^ ")"
      | PE.TidEq(x,y)     -> " (= "  ^ (tid_to_str x) ^ " " ^
                                            (tid_to_str y) ^ ")"
      | PE.TidInEq(x,y)   -> " (/= " ^ (tid_to_str x) ^ " " ^
                                            (tid_to_str y) ^ ")"
      | PE.FunEq(x,y)     -> " (= "  ^ (fun_to_str x) ^ " " ^
                                            (fun_to_str y) ^ ")"
      | PE.FunInEq(x,y)   -> " (/= " ^ (fun_to_str x) ^ " " ^
                                            (fun_to_str y) ^ ")"
      | PE.UniqueInt(s)   -> " (uniqueint" ^ setpair_tostr s ^ ")"
      | PE.UniqueTid(s)   -> " (uniquetid" ^ setpair_tostr s ^ ")"
      | PE.PC (i,th,pr)   -> " " ^ yices_string_of_pos (i,th,pr) ^ " "
      | PE.PCUpdate(i,th) -> " " ^ yices_string_of_posupd (i,th) ^ " "
      | PE.PCRange (i,j,th,pr) -> " " ^ yices_string_of_posrange (i,j,th,pr) ^ " "

  and string_of_literal l =
    match l with
      F.Atom a    -> yices_string_of_atom a
    | F.NegAtom a -> "(not "^ yices_string_of_atom a ^")"

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
      Printf.sprintf "(define %s::%s)\n" t_str tid_s


  and local_var_to_str (v:PE.V.t) : string =
    let v_str = variable_to_str v in
    let v_sort = var_sort_to_str v in
    let gm_v_sort = var_sort_to_gmsort_str v in
    let _ = GM.sm_decl_fun sort_map v_str [GM.tid_s] [gm_v_sort]
    in
      Printf.sprintf "(define %s::(-> %s %s))\n" v_str tid_s v_sort


  and yices_string_of_pos (pc:(int * PE.V.shared_or_local * bool)) : string =
    let (i, th, pr) = pc in
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(= (%s %s) %i)" pc_str th_str i


  and yices_string_of_posrange (pc:(int * int * PE.V.shared_or_local * bool)) : string =
    let (i, j, th, pr) = pc in
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(and (<= %i (%s %s)) (<= (%s %s) %i))"
          i pc_str th_str pc_str th_str j


  and yices_string_of_posupd (pc:(int * PE.tid)) : string =
    let (i, th) = pc
    in
      Printf.sprintf "(= %s (update %s (%s) %i))" pc_prime_name Conf.pc_name
                                           (tid_to_str th) i


  and variable_invocation_to_str (v:PE.V.t) : string =
    let th_str = shared_or_local_to_str (PE.V.parameter v) in
    let p_str  = procedure_name_to_append (PE.V.scope v) in
    let pr_str = if (PE.V.is_primed v) then "'" else ""
    in
      match (PE.V.parameter v) with
      | PE.V.Shared  -> Printf.sprintf " %s%s%s%s" p_str (PE.V.id v) th_str pr_str
      (* For LEAP *)
      | PE.V.Local _ -> Printf.sprintf " (%s%s%s %s)" p_str (PE.V.id v) pr_str th_str
      (* For numinv *)
      (* | PE.V.Local _ -> Printf.sprintf " %s%s%s_%s" p_str (PE.V.id v) pr_str th_str *)





  (************************** Support for sets **************************)

  let yices_type_decl (max_ints:int) (max_tids:int) (prog_lines:int) (buf:Buffer.t) : unit =
    B.add_string buf ("(define-type " ^int_s^ " (subrange 1 " ^(string_of_int max_ints)^ "))\n");
    B.add_string buf
      ("(define-type " ^tid_s^ " (subrange 1 " ^(string_of_int max_tids)^ "))\n" ^
       "(define " ^someTid^ "::" ^tid_s^ ")\n" ^
       "(define-type " ^set_s^ " (-> " ^int_s^ " " ^bool_s^ "))\n" ^
       "(define-type " ^pair_s^ " (record int_of::" ^int_s^ " tid_of::" ^tid_s^ "))\n" ^
       "(define-type " ^setpair_s^ " (-> " ^pair_s^ " " ^bool_s^ "))\n" ^
       "(define-type " ^loc_s^ " (subrange 1 " ^(string_of_int prog_lines)^ "))\n")


  let yices_undefined_decl (maxint:int) (buf:Buffer.t) : unit =
    let _ = GM.sm_decl_const sort_map undefInt GM.int_s in
      B.add_string buf
        ("(define " ^ undefInt ^ "::" ^ int_s ^ ")\n");
      B.add_string buf
        ("(define is_legal::(-> " ^int_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (&e::" ^int_s^ ")\n" ^
         "    (and\n" ^
         "      (/= &e " ^undefInt ^ ")\n" ^
         "      (<= 0 &e)\n" ^
         "      (<= &e " ^(string_of_int maxint)^ "))))\n")


  let yices_emp_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(define emp::" ^set_s^ "\n" ^
       "  (lambda (a::" ^int_s ^ ") false))\n")


  let yices_singleton_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define singleton::(-> " ^int_s^ " " ^set_s^ ")\n" ^
        "    (lambda (a::" ^int_s^ ")\n" ^
        "        (lambda (b::" ^int_s^ ")\n" ^
        "            (= a b))))\n" )


  let yices_union_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define union::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
        "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
        "        (lambda (a::" ^int_s^ ")\n" ^
        "            (or (s a) (r a)))))\n" )


  let yices_setdiff_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define setdiff::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
        "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
        "        (lambda (a::" ^int_s^ ")\n" ^
        "            (and (s a) (not (r a))))))\n" )


  let yices_intersection_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define intersection::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
     "   (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
     "       (lambda (a::" ^int_s^ ")\n" ^
     "           (and (s a) (r a)))))\n")


  let yices_subseteq_def (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define subseteq::(-> " ^set_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (s1::" ^set_s^ " s2::" ^set_s^ ")\n" ^
         "    (= emp (setdiff s1 s2))))\n")


  let yices_spemp_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(define spempty::" ^setpair_s^ "\n" ^
       "  (lambda (p::" ^pair_s ^ ") false))\n")


  let yices_spsingleton_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define spsingle::(-> " ^pair_s^ " " ^setpair_s^ ")\n" ^
        "    (lambda (p::" ^pair_s^ ")\n" ^
        "        (lambda (q::" ^pair_s^ ")\n" ^
        "            (= p q))))\n" )


  let yices_spunion_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define spunion::(-> " ^setpair_s^ " " ^setpair_s^ " " ^setpair_s^ ")\n" ^
        "    (lambda (s::" ^setpair_s^ " r::" ^setpair_s^ ")\n" ^
        "        (lambda (p::" ^pair_s^ ")\n" ^
        "            (or (s p) (r p)))))\n" )


  let yices_spsetdiff_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define spdiff::(-> " ^setpair_s^ " " ^setpair_s^ " " ^setpair_s^ ")\n" ^
        "    (lambda (s::" ^setpair_s^ " r::" ^setpair_s^ ")\n" ^
        "        (lambda (p::" ^pair_s^ ")\n" ^
        "            (and (s p) (not (r p))))))\n" )


  let yices_spintersection_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define spintr::(-> " ^setpair_s^ " " ^setpair_s^ " " ^setpair_s^ ")\n" ^
     "   (lambda (s::" ^setpair_s^ " r::" ^setpair_s^ ")\n" ^
     "       (lambda (p::" ^pair_s^ ")\n" ^
     "           (and (s p) (r p)))))\n")


  let yices_spsubseteq_def (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define spsubseteq::(-> " ^setpair_s^ " " ^setpair_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (s1::" ^setpair_s^ " s2::" ^setpair_s^ ")\n" ^
         "    (= spempty (spdiff s1 s2))))\n")


  let yices_is_min_def (max_ints:int) (buf:Buffer.t) : unit =
    let str = ref "" in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      str := "\n    (=> (&s " ^i_str^ ") (<= &n " ^i_str^ "))" ^ (!str)
    done;
    B.add_string buf
        ("(define is_min::(-> " ^int_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (&n::" ^int_s^ " &s::" ^set_s^ ")\n" ^
         "    (and " ^ (!str) ^ ")))\n")


  let yices_is_max_def (max_ints:int) (buf:Buffer.t) : unit =
    let str = ref "" in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      str := "\n    (=> (&s " ^i_str^ ") (>= &n " ^i_str^ "))" ^ (!str)
    done;
    B.add_string buf
        ("(define is_max::(-> " ^int_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (&n::" ^int_s^ " &s::" ^set_s^ ")\n" ^
         "    (and " ^ (!str) ^ ")))\n")


  let yices_is_spmin_def (max_ints:int) (max_tids:int) (buf:Buffer.t) : unit =
    let str = ref "" in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      for j = 0 to max_tids do
        let j_str = string_of_int j in
        str := "\n    (=> (&s (mk-record int_of::" ^i_str^ " tid_of::" ^j_str^ ")) (<= (select &p int_of) " ^i_str^ "))" ^ (!str)
      done
    done;
    B.add_string buf
        ("(define is_spmin::(-> " ^pair_s^ " " ^setpair_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (&p::" ^pair_s^ " &s::" ^setpair_s^ ")\n" ^
         "    (and (&s &p)\n" ^ (!str) ^ ")))\n")


  let yices_is_spmax_def (max_ints:int) (max_tids:int) (buf:Buffer.t) : unit =
    let str = ref "" in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      for j = 0 to max_tids do
        let j_str = string_of_int j in
        str := "\n    (=> (&s (mk-record int_of::" ^i_str^ " tid_of::" ^j_str^ ")) (>= (select &p int_of) " ^i_str^ "))" ^ (!str)
      done
    done;
    B.add_string buf
        ("(define is_spmax::(-> " ^pair_s^ " " ^setpair_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (&p::" ^pair_s^ " &s::" ^setpair_s^ ")\n" ^
         "    (and (&s &p)\n" ^ (!str) ^ ")))\n")


  let yices_is_in_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define is_in::(-> " ^int_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
     "   (lambda (pairs_v::" ^int_s^ " set_v::" ^set_s^ ")\n" ^
     "       (set_v pairs_v)))\n")


  let yices_min_def (max_ints:int) (buf:Buffer.t) : unit =
    let str = ref undefInt in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      str := "\n    (if (and (is_in " ^i_str^ " &s) (is_min " ^i_str^ " &s)) " ^i_str^ " " ^(!str)^ ")"
    done;
    B.add_string buf
    ("(define setmin::(-> " ^set_s^ " " ^int_s^ ")\n" ^
     "  (lambda (&s::" ^set_s^ ")\n" ^ !str ^ "))\n")


  let yices_max_def (max_ints:int) (buf:Buffer.t) : unit =
    let str = ref undefInt in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      str := "\n    (if (and (is_in " ^i_str^ " &s) (is_max " ^i_str^ " &s)) " ^i_str^ " " ^(!str)^ ")"
    done;
    B.add_string buf
    ("(define setmax::(-> " ^set_s^ " " ^int_s^ ")\n" ^
     "  (lambda (&s::" ^set_s^ ")\n" ^ !str ^ "))\n")


  let yices_spmin_def (max_ints:int) (max_tids:int) (buf:Buffer.t) : unit =
    let str = ref ("(mk-record int_of::" ^undefInt^ " tid_of::" ^someTid^ ")") in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      for j = 0 to max_tids do
        let j_str = string_of_int j in
        let pair_rep = "(mk-record int_of::" ^i_str^ " tid_of::" ^j_str^ ")" in
        str := "\n    (if (and (&s " ^pair_rep^ ") (is_spmin " ^pair_rep^ " &s)) " ^pair_rep^ " " ^(!str)^ ")"
      done
    done;
    B.add_string buf
        ("(define spmin::(-> " ^setpair_s^ " " ^pair_s^ ")\n" ^
         "  (lambda (&s::" ^setpair_s^ ")\n" ^(!str)^ "))\n")



  let yices_spmax_def (max_ints:int) (max_tids:int) (buf:Buffer.t) : unit =
    let str = ref ("(mk-record int_of::" ^undefInt^ " tid_of::" ^someTid^ ")") in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      for j = 0 to max_tids do
        let j_str = string_of_int j in
        let pair_rep = "(mk-record int_of::" ^i_str^ " tid_of::" ^j_str^ ")" in
        str := "\n    (if (and (&s " ^pair_rep^ ") (is_spmax " ^pair_rep^ " &s)) " ^pair_rep^ " " ^(!str)^ ")"
      done
    done;
    B.add_string buf
        ("(define spmax::(-> " ^setpair_s^ " " ^pair_s^ ")\n" ^
         "  (lambda (&s::" ^setpair_s^ ")\n" ^(!str)^ "))\n")


  let yices_filter_legal_set_def (max_ints:int) (buf:Buffer.t) : unit =
    B.add_string buf
    ( "(define filter_legal_set::(-> " ^set_s^ " " ^set_s^ ")\n" ^
      "  (lambda (&s::" ^set_s^ ")\n" ^
      "    (lambda (&a::" ^int_s^ ")\n" ^
      "      (and (<= 0 &a) (<= &a " ^(string_of_int max_ints)^ ")))))\n")


  let yices_filter_legal_setpair_def (max_ints:int) (buf:Buffer.t) : unit =
    B.add_string buf
    ( "(define filter_legal_setpair::(-> " ^setpair_s^ " " ^setpair_s^ ")\n" ^
      "  (lambda (&s::" ^setpair_s^ ")\n" ^
      "    (lambda (&p::" ^pair_s^ ")\n" ^
      "      (and (&s &p) (<= 0 (select &p int_of)) (<= (select &p int_of) " ^(string_of_int max_ints)^ ")))))\n")


  let yices_lower_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define subsetLowerThan::(-> " ^set_s^ " " ^int_s^ " " ^set_s^ ")\n" ^
     "  (lambda (s::" ^set_s^ " i::" ^int_s^ ")\n" ^
     "    (lambda (a::" ^int_s^ ")\n" ^
     "      (and (s a) (<= a i)))))\n")


  let yices_splower_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define splower::(-> " ^setpair_s^ " " ^int_s^ " " ^setpair_s^ ")\n" ^
     "  (lambda (s::" ^setpair_s^ " i::" ^int_s^ ")\n" ^
     "    (lambda (p::" ^pair_s^ ")\n" ^
     "      (and (s p) (<= (select p int_of) i)))))\n")


  let yices_unique_def (max_ints:int) (max_tids:int) (buf:Buffer.t) : unit =
    let str1 = ref "" in
    let str2 = ref "" in

    for n1 = 0 to max_ints do
      let n1_str = string_of_int n1 in
      for n2 = 0 to max_ints do
        let n2_str = string_of_int n2 in
        for t = 0 to max_tids do
          let t_str = string_of_int t in
          str1 := "\n      (=> (and (&s (mk-record int_of::" ^n1_str^ " tid_of::" ^t_str^ ")) (&s (mk-record int_of::" ^n2_str^ " tid_of::" ^t_str^ "))) (= " ^n1_str^ " " ^n2_str^ "))" ^ (!str1)
        done
      done
    done;

    for t1 = 0 to max_tids do
      let t1_str = string_of_int t1 in
      for t2 = 0 to max_tids do
        let t2_str = string_of_int t2 in
        for n = 0 to max_ints do
          let n_str = string_of_int n in
          str2 := "\n      (=> (and (&s (mk-record int_of::" ^n_str^ " tid_of::" ^t1_str^ ")) (&s (mk-record int_of::" ^n_str^ " tid_of::" ^t2_str^ "))) (= " ^t1_str^ " " ^t2_str^ "))" ^ (!str2)
        done
      done
    done;

    B.add_string buf
      ("(define uniqueint::(-> " ^setpair_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (&s::" ^setpair_s^ ")\n" ^
       "    (and\n" ^ (!str1) ^ ")))\n" ^
       "(define uniquetid::(-> " ^setpair_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (&s::" ^setpair_s^ ")\n" ^
       "    (and\n" ^ (!str2) ^ ")))\n")


  let yices_intidpair_def (max_ints:int) (buf:Buffer.t) : unit =
    let str = ref "" in
    for i = 0 to max_ints do
      let i_str = string_of_int i in
      str := "\n    (&s (mk-record int_of::" ^i_str^ " tid_of::&t))"
    done;
    B.add_string buf
      ("(define intidpair::(-> " ^tid_s^ " " ^setpair_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (&t::" ^tid_s^ " &s::" ^setpair_s^ ")\n" ^
       "    (or " ^ (!str)^ ")))\n")


  let yices_inintpair_def (max_tids:int) (buf:Buffer.t) : unit =
    let str = ref "" in
    for i = 0 to max_tids do
      let i_str = string_of_int i in
      str := "\n    (&s (mk-record int_of::&n tid_of::" ^i_str^ "))"
    done;
    B.add_string buf
      ("(define inintpair::(-> " ^int_s^ " " ^setpair_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (&n::" ^int_s^ " &s::" ^setpair_s^ ")\n" ^
       "    (or " ^ (!str)^ ")))\n")


  (************************** Support for sets **************************)


  (************************ Preamble definitions ************************)

  let yices_pc_def (buf:Buffer.t) : unit =
    let _ = GM.sm_decl_fun sort_map Conf.pc_name [GM.tid_s] [GM.loc_s] in
    let _ = GM.sm_decl_fun sort_map pc_prime_name [GM.tid_s] [GM.loc_s]
    in
      B.add_string buf ("(define " ^Conf.pc_name^
                          "::(-> " ^tid_s^ " " ^loc_s^ "))\n");
      B.add_string buf ("(define " ^pc_prime_name^
                          "::(-> " ^tid_s^ " " ^loc_s^ "))\n")


  let yices_aux_pairs_def (cutoff:int) (buf:Buffer.t) : unit =
    let i_list = LeapLib.rangeList 1 cutoff in
    List.iter (fun i ->
      let i_name = aux_int ^ string_of_int i in
      let i_var = PE.build_var i_name PE.Int false PE.V.Shared PE.V.GlobalScope in
      B.add_string buf (var_to_str i_var)
    ) i_list


  let yices_legal_values (global_vars:PE.V.t list)
                         (local_vars:PE.V.t list)
                         (voc:PE.tid list)
                         (buf:Buffer.t) : unit =
    List.iter (fun v ->
      match PE.V.sort v with
      | PE.Int -> let v_str = variable_invocation_to_str v in
                    B.add_string buf ("(assert (is_legal " ^ v_str ^ "))\n")
      | PE.Set -> let v_str = variable_invocation_to_str v in
                    B.add_string buf ("(assert (= " ^v_str^ " (filter_legal_set " ^v_str^ ")))\n")
      | PE.SetPair -> let v_str = variable_invocation_to_str v in
                        B.add_string buf ("(assert (= " ^v_str^ " (filter_legal_setpair " ^v_str^ ")))\n")
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
                          B.add_string buf ("(assert (= " ^v_str^ " (filter_legal_set " ^v_str^ ")))\n")
        | PE.SetPair -> let v_str = variable_invocation_to_str
                          (PE.V.set_param v (PE.V.Local (PE.voc_to_var t))) in
                          B.add_string buf ("(assert (= " ^v_str^ " (filter_legal_setpair " ^v_str^ ")))\n")
        | _ -> ()
      ) voc
    ) local_vars


  (* ALE: Verify, if no set is defined, then do not include the preamble for sets *)
  let yices_preamble (buf:Buffer.t)
                     (voc:PE.tid list)
                     (int_cutoff:int)
                     (gbl_int_vars:PE.V.t list)
                     (lcl_int_vars:PE.V.t list) : unit =
    let loc_vars_str = List.flatten $ List.map (fun t ->
                         List.map (fun v ->
                           variable_invocation_to_str(PE.V.set_param v (PE.V.Local (PE.voc_to_var t)))
                         ) lcl_int_vars
                       ) voc in
    let glb_vars_str = List.map variable_invocation_to_str gbl_int_vars in
    let aux_vars_str = List.map (fun i ->
                         let i_name = aux_int ^ string_of_int i in
                         let i_var = PE.build_var i_name PE.Int
                                        false PE.V.Shared PE.V.GlobalScope
                         in
                           variable_invocation_to_str i_var
                       ) (LeapLib.rangeList 1 int_cutoff) in
    let all_vars_str = glb_vars_str @ loc_vars_str @ aux_vars_str in
    let max_ints = List.length all_vars_str in
    let max_tids = List.length voc
    in
      yices_undefined_decl max_ints                 buf;
      yices_aux_pairs_def int_cutoff                buf;
      yices_emp_def                                 buf;
      yices_singleton_def                           buf;
      yices_union_def                               buf;
      yices_setdiff_def                             buf;
      yices_intersection_def                        buf;
      yices_subseteq_def                            buf;
      yices_spemp_def                               buf;
      yices_spsingleton_def                         buf;
      yices_spunion_def                             buf;
      yices_spsetdiff_def                           buf;
      yices_spintersection_def                      buf;
      yices_spsubseteq_def                          buf;
      yices_is_min_def max_ints                     buf;
      yices_is_max_def max_ints                     buf;
      yices_is_spmin_def max_ints max_tids          buf;
      yices_is_spmax_def max_ints max_tids          buf;
      yices_is_in_def                               buf;
      yices_min_def max_ints                        buf;
      yices_max_def max_ints                        buf;
      yices_spmin_def max_ints max_tids             buf;
      yices_spmax_def max_ints max_tids             buf;
      yices_filter_legal_set_def max_ints           buf;
      yices_filter_legal_setpair_def max_ints       buf;
      yices_lower_def                               buf;
      yices_splower_def                             buf;
      yices_unique_def max_ints max_tids            buf;
      yices_intidpair_def max_ints                  buf;
      yices_inintpair_def max_tids                  buf;
      yices_pc_def                                  buf


  (************************ Preamble definitions ************************)


  let tid_decl_to_str (voc:PE.tid list) : string =
    let id_list = List.map (fun t ->
                    match t with
                    | PE.VarTh v -> (PE.V.id v)
                    | PE.NoTid  -> "NoThread"
                    | PE.PairTid p -> "(select " ^ yices_string_of_pair p ^ " tid_of)"
                  ) voc in
    Printf.sprintf "(define-type %s (scalar %s))\n" tid_s
                    (String.concat " " id_list)


  let pairs_locVarlist_to_str (vars:PE.V.VarSet.t) : string =
    PE.V.VarSet.fold (fun v str -> str ^ local_var_to_str v) vars ""


  let pairs_formula_to_str (phi:PE.formula) : string =
    let _ = GM.clear_sort_map sort_map in
    (*  if direct then *)
    let vars        = PE.all_vars phi in
    let var_str     = pairs_varlist_to_str vars in
    let formula_str = "(assert " ^ (string_of_formula phi) ^ ")\n(check)\n" in
      var_str ^ formula_str


  let pairs_formula_with_lines_to_str (phi:PE.formula) : string =
    let _ = GM.clear_sort_map sort_map in
    let filter_ints xs = List.filter (fun v ->
                           (PE.V.sort v) = PE.Int
                         ) xs in
    let voc            = PE.voc phi in
    let cutoff         = SmpPairs.cut_off phi in
    let int_cutoff     = MS.get cutoff MS.Int in
    let tid_cutoff     = MS.get cutoff MS.Tid in
    let global_vars    = PE.all_global_vars phi in
    let local_vars     = PE.all_local_vars_without_param phi in
    let glb_int_vars   = filter_ints global_vars in
    let lcl_int_vars   = filter_ints local_vars in
    let buf            = B.create 1024 in
    let _              = yices_type_decl int_cutoff tid_cutoff !prog_lines buf in
    let _              = List.iter (fun v ->
                           B.add_string buf (tid_variable_to_str v)
                         ) voc in
    let _              = List.iter (fun v ->
                           B.add_string buf (var_to_str v)
                         ) global_vars in
    let _              = List.iter (fun v ->
                          B.add_string buf (local_var_to_str v)
                         ) local_vars in
    let _              = yices_preamble buf voc int_cutoff
                            glb_int_vars lcl_int_vars in
    let _              = yices_legal_values global_vars local_vars voc buf in
    let _              = B.add_string buf ("(assert " ^ (string_of_formula phi) ^
                                            ")\n(check)\n")
    in
      B.contents buf


  let get_sort_map () : GM.sort_map_t =
    GM.copy_sort_map sort_map

end
