open NumQuery
open LeapLib


module YicesNumQuery : NUM_QUERY =

struct
  module E=Expression
  module NE=NumExpression
  module NI=NumInterface
  module B = Buffer
  module GM = GenericModel


  exception NotSupportedInYices of string
  exception UntypedVariable of string
  exception Not_implemented of string


  (* Configuration *)
  let pc_name       : string = "pc"
  let pc_prime_name : string = pc_name ^ "'"
  let aux_int       : string = "ai_"
  let undefInt      : string = "undefined_int"


  (* Program lines *)
  let prog_lines : int ref = ref 0


  (* Sort names *)
  let int_s : string = "int"
  let thid_s : string = "thid"
  let set_s : string = "set"
  let bool_s : string = "bool"
  let loc_s : string = "loc"


  (* Information storage *)
  let sort_map : GM.sort_map_t = GM.new_sort_map()


  (* Program lines manipulation *)
  let set_prog_lines (n:int) : unit =
    prog_lines := n


  (* Translation funtions *)
  let int_varid_to_str (v:E.varId) : string =
    let _ = GM.sm_decl_const sort_map v GM.int_s
    in
      Printf.sprintf "(define %s::%s)\n" v int_s


  let int_local_varid_to_str (v:E.varId) : string =
    let _ = GM.sm_decl_fun sort_map v [GM.tid_s] [GM.int_s]
    in
      Printf.sprintf "(define %s::(-> %s %s))\n" v thid_s int_s


  let int_var_to_str (v:NE.variable) : string =
    let pr_str = if (NE.var_is_primed v) then "'" else ""
    in
      match NE.var_scope v with
      | NE.GlobalScope -> int_varid_to_str ((NE.var_id v) ^ pr_str)
      | NE.Scope ""    -> int_varid_to_str ((NE.var_id v) ^ pr_str)
      | NE.Scope p     -> int_local_varid_to_str (p^"_"^(NE.var_id v)^pr_str)


  let rec int_varlist_to_str (vl:NE.variable list) : string =
    let add_th th set = match th with
                        | NE.Shared  -> set
                        | NE.Local t -> E.ThreadSet.add t set in
    let (t_set,v_set) = List.fold_left (fun (ts,vs) v ->
                          (add_th (NE.var_parameter v) ts,
                           NE.VarSet.add (NE.var_clear_param_info v) vs)
                        ) (E.ThreadSet.empty, NE.VarSet.empty) vl in
    let th_str = if E.ThreadSet.cardinal t_set <> 0 then
                   "(define-type " ^thid_s^ ")\n" ^
                      E.ThreadSet.fold (fun t str ->
                        let t_str = tid_to_str t in
                        let _ = GM.sm_decl_const sort_map t_str GM.tid_s
                        in
                          str ^ (Printf.sprintf "(define %s::%s)\n" t_str thid_s)
                   ) t_set ""
                 else
                   ""
    in
      List.fold_left (fun str v ->
        str ^ (int_var_to_str v)
      ) th_str (NE.VarSet.elements v_set)


  and procedure_name_to_append (proc:NE.procedure_name) : string =
    match proc with
    | NE.GlobalScope -> ""
    | NE.Scope "" -> ""
    | NE.Scope p  -> p ^ "_"


  and variable_to_str (v:NE.variable) : string =
    let pr_str = if (NE.var_is_primed v) then "'" else "" in
    let th_str = match (NE.var_parameter v) with
                 | NE.Shared  -> ""
                 | NE.Local t -> "_" ^ (tid_to_str t) in
    let p_str = procedure_name_to_append (NE.var_scope v)
    in
      Printf.sprintf "%s%s%s%s" p_str (NE.var_id v) th_str pr_str


  and var_sort_to_str (v:NE.variable) : string =
    match (NE.var_sort v) with
    | NE.Int  -> int_s
    | NE.Set  -> set_s
    | NE.Tid -> thid_s


  and var_sort_to_gmsort_str (v:NE.variable) : string =
    match (NE.var_sort v) with
      NE.Int  -> GM.int_s
    | NE.Set  -> GM.set_s
    | NE.Tid -> GM.tid_s


  and var_to_str (v:NE.variable) : string =
    let v_str = variable_to_str v in
    let sort_str = var_sort_to_str v in
    let gm_sort_str = var_sort_to_gmsort_str v in
    let _ = GM.sm_decl_const sort_map v_str gm_sort_str
    in
      Printf.sprintf "(define %s::%s)\n" v_str sort_str


  and tid_to_str (t:E.tid) : string =
    match t with
    | E.VarTh v       -> variable_to_str
                              (NI.variable_to_int_variable v)
    | E.NoTid        -> "NoTid"
    | E.CellLockId _  -> raise(NotSupportedInYices(E.tid_to_str t))
    | E.CellLockIdAt _-> raise(NotSupportedInYices(E.tid_to_str t))
    | E.TidArrayRd _ -> raise(NotSupportedInYices(E.tid_to_str t))
    | E.TidArrRd _   -> raise(NotSupportedInYices(E.tid_to_str t))


  and shared_or_local_to_str (th:NE.shared_or_local) : string =
    match th with
    | NE.Shared  -> ""
    | NE.Local t -> tid_to_str t


  let thid_variable_to_str (th:E.tid) : string =
    let t_str = tid_to_str th in
    let _ = GM.sm_decl_const sort_map t_str GM.tid_s
    in
      Printf.sprintf "(define %s::%s)\n" t_str thid_s


  let local_var_to_str (v:NE.variable) : string =
    let v_str = variable_to_str v in
    let v_sort = var_sort_to_str v in
    let gm_v_sort = var_sort_to_gmsort_str v in
    let _ = GM.sm_decl_fun sort_map v_str [GM.tid_s] [gm_v_sort]
    in
      Printf.sprintf "(define %s::(-> %s %s))\n" v_str thid_s v_sort


  let yices_string_of_pos (pc:(int * NE.shared_or_local * bool)) : string =
    let (i, th, pr) = pc in
    let pc_str = if pr then pc_prime_name else pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(= (%s %s) %i)" pc_str th_str i


  let yices_string_of_posrange (pc:(int * int * NE.shared_or_local * bool)) : string =
    let (i, j, th, pr) = pc in
    let pc_str = if pr then pc_prime_name else pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(and (<= %i (%s %s)) (<= (%s %s) %i))"
          i pc_str th_str pc_str th_str j


  let yices_string_of_posupd (pc:(int * E.tid)) : string =
    let (i, th) = pc
    in
      Printf.sprintf "(= %s (update %s (%s) %i))" pc_prime_name pc_name
                                           (tid_to_str th) i


  let variable_invocation_to_str (v:NE.variable) : string =
    let th_str = shared_or_local_to_str (NE.var_parameter v) in
    let p_str  = procedure_name_to_append (NE.var_scope v) in
    let pr_str = if (NE.var_is_primed v) then "'" else ""
    in
      match (NE.var_parameter v) with
      | NE.Shared  -> Printf.sprintf " %s%s%s%s" p_str (NE.var_id v) th_str pr_str
  (* For LEAP *)
      | NE.Local _ -> Printf.sprintf " (%s%s%s %s)" p_str (NE.var_id v) pr_str th_str
  (* For numinv *)
  (*    | NE.Local _ -> Printf.sprintf " %s%s%s_%s" p_str (NE.var_id v) pr_str th_str *)



  (***** Not sure =S ******
      match th with
        None -> Printf.sprintf " %s%s%s%s" p_str id th_str pr_str
      | Some t -> if E.is_tid_val t then
                    Printf.sprintf " %s%s%s_%s" p_str id pr_str th_str
                  else
                    Printf.sprintf " (%s%s%s %s)" p_str id pr_str th_str
   ************************)


  (************************** Support for sets **************************)

  let yices_type_decl (prog_lines:int) (buf:Buffer.t) : unit =
    B.add_string buf ("(define-type " ^thid_s^ ")\n");
    B.add_string buf (Printf.sprintf "(define-type %s (-> %s %s))\n"
                        set_s int_s bool_s);
    B.add_string buf (Printf.sprintf "(define-type %s (subrange 1 %i))\n"
                        loc_s prog_lines)


  let yices_undefined_decl (buf:Buffer.t) : unit =
    let _ = GM.sm_decl_const sort_map undefInt GM.int_s in
      B.add_string buf ("(define " ^ undefInt ^ "::" ^ int_s ^ ")\n");
      B.add_string buf ("(define is_legal::(-> " ^int_s^ " " ^bool_s^ ")\n" ^
                        "  (lambda (e::" ^int_s^ ") (/= e " ^
                            undefInt ^ ")))\n")


  (* (define emp::set)               *)
  (*   (lambda (a::address) (false)) *)
  let yices_emp_def (buf:Buffer.t) : unit =
    B.add_string buf
      ("(define emp::" ^set_s^ "\n" ^
       "  (lambda (a::" ^int_s ^ ") false))\n")

  (* (define singleton::(-> int set)       *)
  (*     (lambda (a::int)                  *)
  (*         (lambda (b::int)              *)
  (*             (= a b))))                *)
  let yices_singleton_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define singleton::(-> " ^int_s^ " " ^set_s^ ")\n" ^
        "    (lambda (a::" ^int_s^ ")\n" ^
        "        (lambda (b::" ^int_s^ ")\n" ^
        "            (= a b))))\n" )

  (* (define union::(-> set set set)        *)
  (*     (lambda (s::set r::set)            *)
  (*         (lambda (a::int)               *)
  (*             (or (s a) (r a)))))        *)
  let yices_union_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define union::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
        "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
        "        (lambda (a::" ^int_s^ ")\n" ^
        "            (or (s a) (r a)))))\n" )

  (* (define setdiff::(-> set set set)      *)
  (*     (lambda (s::set r::set)            *)
  (*         (lambda (a::int)               *)
  (*             (and (s a) (not (r a)))))) *)
  let yices_setdiff_def (buf:Buffer.t) : unit =
    B.add_string buf
      ( "(define setdiff::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
        "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
        "        (lambda (a::" ^int_s^ ")\n" ^
        "            (and (s a) (not (r a))))))\n" )

  (* (define intersection::(-> set set set) *)
  (*     (lambda (s::set r::set) *)
  (*         (lambda (a::address) *)
  (*             (and (s a) (r a))))) *)
  let yices_intersection_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define intersection::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
     "   (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
     "       (lambda (a::" ^int_s^ ")\n" ^
     "           (and (s a) (r a)))))\n")


  (* (define subseteq::(-> set set bool)  *)
  (*   (lambda (s1::set s2::set)        *)
  (*     (and (if (s1 null) (s2 null))    *)
  (*          (if (s1 a1) (s2 a1))        *)
  (*          (if (s1 a1) (s2 a2))        *)
  (*          (if (s1 a3) (s2 a3))        *)
  (*          (if (s1 a4) (s2 a4))        *)
  (*          (if (s1 a5) (s2 a5)))))     *)
  let yices_subseteq_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define subseteq::(-> " ^set_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (s1::" ^set_s^ " s2::" ^set_s^ ")\n" ^
         "    (and") ;
    List.iter (fun v ->
      B.add_string buf
        ("\n         (if (s1 " ^ v ^ ") (s2 " ^ v ^ "))")
    ) vars_rep;
    B.add_string buf ")))\n"


  let yices_is_min_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define is_min::(-> " ^int_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (int_v::" ^int_s^ " set_v::" ^set_s^ ")\n" ^
         "    (and") ;
    List.iter (fun v ->
      B.add_string buf
        (Printf.sprintf "\n         (if (set_v %s) (<= int_v %s) true)" v v)
    ) vars_rep;
    B.add_string buf ")))\n"


  let yices_is_max_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
        ("(define is_max::(-> " ^int_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (int_v::" ^int_s^ " set_v::" ^set_s^ ")\n" ^
         "    (and") ;
    List.iter (fun v ->
      B.add_string buf
        (Printf.sprintf "\n         (if (set_v %s) (>= int_v %s) true)" v v)
    ) vars_rep;
    B.add_string buf ")))\n"


  let yices_is_in_def (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define is_in::(-> " ^int_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
     "   (lambda (int_v::" ^int_s^ " set_v::" ^set_s^ ")\n" ^
     "       (set_v int_v)))\n")


  let yices_min_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define setmin::(-> " ^set_s^ " " ^int_s^ ")\n" ^
     "   (lambda (set_v::" ^set_s^ ")\n" ^
      List.fold_left (fun str v ->
        Printf.sprintf ("\n        (if (and (is_in %s set_v) \
                                            (is_min %s set_v)) %s %s)")
          v v v str
      ) undefInt vars_rep ^
     "))\n")


  let yices_max_def (vars_rep:string list) (buf:Buffer.t) : unit =
    B.add_string buf
    ("(define setmax::(-> " ^set_s^ " " ^int_s^ ")\n" ^
     "   (lambda (set_v::" ^set_s^ ")\n" ^
      List.fold_left (fun str v ->
        Printf.sprintf ("\n        (if (and (is_in %s set_v) \
                                            (is_max %s set_v)) %s %s)")
          v v v str
      ) undefInt vars_rep ^
     "))\n")

  (************************** Support for sets **************************)


  (************************ Preamble definitions ************************)

  let yices_pc_def (buf:Buffer.t) : unit =
    let _ = GM.sm_decl_fun sort_map pc_name [GM.tid_s] [GM.loc_s] in
    let _ = GM.sm_decl_fun sort_map pc_prime_name [GM.tid_s] [GM.loc_s]
    in
      B.add_string buf ("(define " ^pc_name^
                          "::(-> " ^thid_s^ " " ^loc_s^ "))\n");
      B.add_string buf ("(define " ^pc_prime_name^
                          "::(-> " ^thid_s^ " " ^loc_s^ "))\n")


  let yices_aux_int_def (cutoff:int) (buf:Buffer.t) : unit =
    let i_list = LeapLib.rangeList 1 cutoff in
    List.iter (fun i ->
      let i_name = aux_int ^ string_of_int i in
      let i_var = NE.build_var i_name NE.Int false NE.Shared NE.GlobalScope in
      B.add_string buf (var_to_str i_var)
    ) i_list


  let yices_legal_values (global_vars:NE.variable list)
                         (local_vars:NE.variable list)
                         (voc:E.tid list)
                         (buf:Buffer.t) : unit =
    List.iter (fun v ->
      if (NE.var_sort v) = NE.Int then
        let v_str = variable_invocation_to_str v in
        B.add_string buf ("(assert+ (is_legal " ^ v_str ^ "))")
    ) global_vars;
    List.iter (fun v ->
      List.iter (fun t->
        if (NE.var_sort v) = NE.Int then
          let v_str = variable_invocation_to_str (NE.param_var v t) in
          B.add_string buf ("(assert+ (is_legal " ^ v_str ^ "))\n")
      ) voc
    ) local_vars


  (* TODO: Verify, if no set is defined, then do not include the preamble for sets *)
  let yices_preamble (buf:Buffer.t)
                     (voc:E.tid list)
                     (cutoff:int)
                     (gbl_int_vars:NE.variable list)
                     (lcl_int_vars:NE.variable list) : unit =
    let loc_vars_str = List.flatten $ List.map (fun t ->
                         List.map (fun v ->
                           variable_invocation_to_str(NE.param_var v t)
                         ) lcl_int_vars
                       ) voc in
    let glb_vars_str = List.map variable_invocation_to_str gbl_int_vars in
    let aux_vars_str = List.map (fun i ->
                         let i_name = aux_int ^ string_of_int i in
                         let i_var = NE.build_var i_name NE.Int
                                        false NE.Shared NE.GlobalScope
                         in
                           variable_invocation_to_str i_var
                       ) (LeapLib.rangeList 1 cutoff) in
    let all_vars_str = glb_vars_str @ loc_vars_str @ aux_vars_str
    in
      yices_undefined_decl             buf;
      yices_aux_int_def cutoff         buf;
      yices_emp_def                    buf;
      yices_singleton_def              buf;
      yices_union_def                  buf;
      yices_setdiff_def                buf;
      yices_intersection_def           buf;
      yices_subseteq_def all_vars_str  buf;
      yices_is_min_def all_vars_str    buf;
      yices_is_max_def all_vars_str    buf;
      yices_is_in_def                  buf;
      yices_min_def all_vars_str       buf;
      yices_max_def all_vars_str       buf;
      yices_pc_def                     buf


  (************************ Preamble definitions ************************)


  let rec fun_to_str (f:NE.fun_term) : string =
    match f with
      NE.FunVar v ->
        if (NE.var_parameter v) = NE.Shared then
          variable_to_str v
        else
          let v_str  = variable_to_str (NE.var_clear_param_info v) in
          let th_str = shared_or_local_to_str (NE.var_parameter v)
          in
            Printf.sprintf "(%s %s)" v_str th_str
    | NE.FunUpd (f,th,i) ->
        let f_str = fun_to_str f in
        let th_str = tid_to_str th in
        let i_str = yices_string_of_term i
        in
          Printf.sprintf "(update %s (%s) %s)" f_str th_str i_str


  and yices_string_of_integer (t:NE.integer) : string =
    let constanttostr t =
      match t with
          NE.Val(n) -> string_of_int n
        | _ -> raise(NotSupportedInYices(NE.integer_to_str t)) in
    let tostr = yices_string_of_integer in
      match t with
        NE.Val(n)       -> " " ^ string_of_int n
      | NE.Var(v)       -> variable_invocation_to_str v
      | NE.Neg(x)       -> " -" ^  (constanttostr x)
      | NE.Add(x,y)     -> " (+ " ^ (tostr x) ^ (tostr y) ^ ")"
      | NE.Sub(x,y)     -> " (- " ^ (tostr x) ^ (tostr y) ^ ")"
      | NE.Mul(x,y)     -> " (* " ^ (tostr x) ^ (tostr y) ^ ")"
      | NE.Div(x,y)     -> " (/ " ^ (tostr x) ^ (tostr y) ^ ")"
      | NE.ArrayRd(_,_) -> raise(NotSupportedInYices(NE.integer_to_str t))
      | NE.SetMin(s)    -> " (setmin " ^ yices_string_of_set s ^ ")"
      | NE.SetMax(s)    -> " (setmax " ^ yices_string_of_set s ^ ")"

  and yices_string_of_set (s:NE.set) : string =
    let yices_int = yices_string_of_integer in
    let yices_set = yices_string_of_set in
    match s with
      NE.VarSet (v)   -> variable_invocation_to_str v
    | NE.EmptySet     -> " emp"
    | NE.Singl i      -> Printf.sprintf "(singleton %s)" (yices_int i)
    | NE.Union(s1,s2) -> Printf.sprintf "(union %s %s)" (yices_set s1) (yices_set s2)
    | NE.Intr(s1,s2)  -> Printf.sprintf "(intersection %s %s)" (yices_set s1) (yices_set s2)
    | NE.Diff(s1,s2)  -> Printf.sprintf "(setdiff %s %s)" (yices_set s1) (yices_set s2)


  and yices_string_of_term (t:NE.term) : string =
    match t with
      NE.IntV i -> yices_string_of_integer i
    | NE.SetV s -> yices_string_of_set s


  and yices_string_of_atom a =
    let int_tostr = yices_string_of_integer in
    let set_tostr = yices_string_of_set in
    let term_tostr = yices_string_of_term in
      match a with
        NE.Less(x,y)      -> " (< "  ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | NE.Greater(x,y)   -> " (> "  ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | NE.LessEq(x,y)    -> " (<= " ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | NE.GreaterEq(x,y) -> " (>= " ^ (int_tostr x) ^ (int_tostr y) ^ ")"
      | NE.LessTid(x,y)   -> " (tid order support for yices not added yet )"
      | NE.Eq(x,y)        -> " (= "  ^ (term_tostr x) ^ (term_tostr y) ^ ")"
      | NE.InEq(x,y)      -> " (/= " ^ (term_tostr x) ^ (term_tostr y) ^ ")"
      | NE.In(i,s)        -> " (" ^ set_tostr s ^ " " ^ int_tostr i ^ ")"
      | NE.Subset(s1,s2)  -> " (subseteq " ^ set_tostr s1 ^ " " ^ set_tostr s2 ^ ")"
      | NE.TidEq(x,y)     -> " (= "  ^ (tid_to_str x) ^ " " ^
                                            (tid_to_str y) ^ ")"
      | NE.TidInEq(x,y)   -> " (/= " ^ (tid_to_str x) ^ " " ^
                                            (tid_to_str y) ^ ")"
      | NE.FunEq(x,y)     -> " (= "  ^ (fun_to_str x) ^ " " ^
                                            (fun_to_str y) ^ ")"
      | NE.FunInEq(x,y)   -> " (/= " ^ (fun_to_str x) ^ " " ^
                                            (fun_to_str y) ^ ")"
      | NE.PC (i,th,pr)   -> " " ^ yices_string_of_pos (i,th,pr) ^ " "
      | NE.PCUpdate(i,th) -> " " ^ yices_string_of_posupd (i,th) ^ " "
      | NE.PCRange (i,j,th,pr) -> " " ^ yices_string_of_posrange (i,j,th,pr) ^ " "

  and yices_string_of_literal l =
    match l with
      NE.Atom a    -> yices_string_of_atom a
    | NE.NegAtom a -> "(not "^ yices_string_of_atom a ^")"

  and yices_string_of_formula  phi =
    let tostr = yices_string_of_formula in
      match phi with
        NE.Literal(l)   -> yices_string_of_literal l
      | NE.True         -> " true "
      | NE.False        -> " false "
      | NE.And(a,b)     -> " (and " ^ (tostr a) ^ (tostr b) ^ ")"
      | NE.Or(a,b)      -> " (or "  ^ (tostr a) ^ (tostr b) ^ ")"
      | NE.Not(a)       -> " (not " ^ (tostr a) ^ ")"
      | NE.Implies(a,b) -> " (=> "  ^ (tostr a) ^ (tostr b) ^ ")"
      | NE.Iff(a,b)     -> " (= "   ^ (tostr a) ^ (tostr b) ^ ")"


  let tid_decl_to_str (voc:NE.tid list) : string =
    let id_list = List.map (fun t ->
                    match t with
                      E.VarTh v -> (E.var_id v)
                    | E.NoTid  -> "NoThread"
                    | _ -> raise(Not_implemented "sort type in tid_decl")
                  ) voc in
    Printf.sprintf "(define-type %s (scalar %s))\n" thid_s
                    (String.concat " " id_list)


  let int_locVarlist_to_str (vars:NE.VarSet.t) : string =
    NE.VarSet.fold (fun v str -> str ^ local_var_to_str v) vars ""


  let int_formula_to_str (phi:NE.formula) : string =
    let _ = GM.clear_sort_map sort_map in
    (*  if direct then *)
    let vars        = NE.all_vars phi in
    let var_str     = int_varlist_to_str vars in
    let formula_str = "(assert+ " ^ (yices_string_of_formula phi) ^ ")\n(check)\n" 
    in
      var_str ^ formula_str


  let int_formula_with_lines_to_str (phi:NE.formula) : string =
    let _ = GM.clear_sort_map sort_map in
    let filter_ints xs = List.filter (fun v ->
                           (NE.var_sort v) = NE.Int
                         ) xs in
    let voc            = NE.voc phi in
    let cutoff         = SmpNum.cut_off phi in
    let global_vars    = NE.all_global_vars phi in
    let local_vars     = NE.all_local_vars_without_param phi in
    let glb_int_vars   = filter_ints global_vars in
    let lcl_int_vars   = filter_ints local_vars in
    let buf            = B.create 1024 in
    let _              = yices_type_decl !prog_lines buf in
    let _              = List.iter (fun v ->
                           B.add_string buf (thid_variable_to_str v)
                         ) voc in
    let _              = List.iter (fun v ->
                           B.add_string buf (var_to_str v)
                         ) global_vars in
    let _              = List.iter (fun v ->
                          B.add_string buf (local_var_to_str v)
                         ) local_vars in
    let _              = yices_preamble buf voc cutoff
                            glb_int_vars lcl_int_vars in
    let _              = yices_legal_values global_vars local_vars voc buf in
    let _              = B.add_string buf ("(assert+ " ^ (yices_string_of_formula 
                                            phi) ^
                                            ")\n(check)\n")
    in
      B.contents buf
   
  let standard_widening (vars : NE.variable list) (f : NE.formula) 
      (l : NE.literal) =
    let vars' = int_varlist_to_str vars in
    let f'    = int_formula_to_str f in
    let l'    = yices_string_of_literal l
    in Printf.sprintf "%s\n(assert+ (not (=> %s %s)))\n(check)\n" vars' f' l'


  let get_sort_map () : GM.sort_map_t =
    GM.copy_sort_map sort_map

end
