open LeapLib
open LeapVerbose

module type CUSTOM_THMSOLVER = sig
  module ThmExp : ExpressionTypes.THMEXP
  
  
  val check_sat_conj  : int -> bool -> ThmExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : int -> bool -> ThmExp.formula -> Sat.t
  
  val check_valid_dnf : int -> bool -> ThmExp.formula -> Valid.t
  val check_valid_dnf_pus_info : int -> bool -> ThmExp.formula -> (Valid.t * int)
    
  val check_sat       : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     ThmExp.formula -> Sat.t
  val check_valid     : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     ThmExp.formula -> Valid.t
  
  val check_valid_plus_info 
                   : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     ThmExp.formula -> (Valid.t * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_THMSOLVER
  with module ThmExp = ThmExpression
  
module Make(Solver : BackendSolverIntf.BACKEND_THM) : S =
struct
  module ThmExp   = Solver.Translate.Thm.Exp
  module VarIdSet = ThmExp.V.VarIdSet
  module GM       = GenericModel

  let comp_model : bool ref = ref false

  let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
  
  (* 
   * is_var 
   *)
  let is_var_path = function
      ThmExp.VarPath(_) -> true
    | _               -> false
  and is_var_addr = function
      ThmExp.VarAddr(_) -> true
    | _               -> false
  and is_var_mem = function
      ThmExp.VarMem(_) -> true
    | _              -> false
  and is_var_int = function
      ThmExp.VarInt(_) -> true
    | _              -> false
  and is_var_tidarr = function
      ThmExp.VarTidArray(_) -> true
    | _                     -> false
  and is_var_bucketarr = function
      ThmExp.VarBucketArray(_) -> true
    | _                        -> false
  and is_var_mark = function
      ThmExp.VarMark(_) -> true
    | _                 -> false
  and is_var_bucket = function
      ThmExp.VarBucket(_) -> true
    | _                   -> false
  and is_var_lock = function
      ThmExp.VarLock(_) -> true
    | _                 -> false
  and is_var_lockarr = function
      ThmExp.VarLockArray(_) -> true
    | _                      -> false
  and is_var_cell = function
      ThmExp.VarCell(_) -> true
    | _               -> false
  and is_var_elem = function
      ThmExp.VarElem(_) -> true
    | _               -> false
  and is_var_thid = function
      ThmExp.VarTh(_) -> true
    | _             -> false
  and is_var_set = function
      ThmExp.VarSet(_) -> true
    | _              -> false
  and is_var_setth = function
      ThmExp.VarSetTh(_) -> true
    | _                -> false
  and is_var_setelem = function
      ThmExp.VarSetElem(_) -> true
    | _                    -> false
  
  let is_var_term = function
      ThmExp.VarT(_)          -> true
    | ThmExp.SetT(s)          -> is_var_set s
    | ThmExp.ElemT(e)         -> is_var_elem e
    | ThmExp.TidT(t)          -> is_var_thid t
    | ThmExp.AddrT(a)         -> is_var_addr a
    | ThmExp.CellT(c)         -> is_var_cell c
    | ThmExp.SetThT(st)       -> is_var_setth st
    | ThmExp.SetElemT(st)     -> is_var_setelem st
    | ThmExp.PathT(p)         -> is_var_path p
    | ThmExp.MemT(m)          -> is_var_mem m
    | ThmExp.IntT(i)          -> is_var_int i
    | ThmExp.TidArrayT(tt)    -> is_var_tidarr tt
    | ThmExp.BucketArrayT(bb) -> is_var_bucketarr bb
    | ThmExp.MarkT(m)         -> is_var_mark m
    | ThmExp.BucketT(b)       -> is_var_bucket b
    | ThmExp.VarUpdate _      -> false (* ALE: Not sure if OK *)
  
  (* 
   * is_constant 
   *)
  let is_constant_set = function
        ThmExp.EmptySet -> true
      | _             -> false
  and is_constant_setth = function
        ThmExp.EmptySetTh -> true
      | _               -> false
  and is_constant_setelem = function
        ThmExp.EmptySetElem -> true
      | _                   -> false
  and is_constant_elem = function
        ThmExp.LowestElem  -> true
      | ThmExp.HighestElem -> true
      | _                  -> false
  and is_constant_thid = function
        ThmExp.NoTid -> true
      | _             -> false
  and is_constant_addr =  function
        ThmExp.Null -> true
      | _         -> false
  and is_constant_cell = function
        ThmExp.Error -> true
      | _          -> false
  and is_constant_path = function
        ThmExp.Epsilon -> true
      | _            -> false
  and is_constant_mem = function
        ThmExp.Emp -> true
      | _        -> false
  and is_constant_int = function
        ThmExp.IntVal _ -> true
      | _        -> false
  and is_constant_bucketarr = function
        _ -> false
  and is_constant_tidarr = function
        _ -> false
  and is_constant_mark = function
        ThmExp.MarkTrue -> true
      | ThmExp.MarkFalse -> true
      | _        -> false
  and is_constant_bucket = function
        _ -> false
  and is_constant_lock = function
        _ -> false
  and is_constant_lockarr = function
        _ -> false
  let is_constant_term = function
        ThmExp.VarT(_)          -> false
      | ThmExp.SetT(s)          -> is_constant_set s
      | ThmExp.ElemT(e)         -> is_constant_elem e
      | ThmExp.TidT(th)         -> is_constant_thid th
      | ThmExp.AddrT(a)         -> is_constant_addr a
      | ThmExp.CellT(c)         -> is_constant_cell c
      | ThmExp.SetThT(st)       -> is_constant_setth st
      | ThmExp.SetElemT(st)     -> is_constant_setelem st
      | ThmExp.PathT(p)         -> is_constant_path p
      | ThmExp.MemT(m)          -> is_constant_mem m
      | ThmExp.IntT(i)          -> is_constant_int i
      | ThmExp.TidArrayT(tt)    -> is_constant_tidarr tt
      | ThmExp.BucketArrayT(bb) -> is_constant_bucketarr bb
      | ThmExp.MarkT(m)         -> is_constant_mark m
      | ThmExp.BucketT(b)       -> is_constant_bucket b
      | ThmExp.VarUpdate _      -> false
  
  (* 
   * is_flat
   *)
  
  let is_flat_set       s   = is_var_set        s   || is_constant_set        s
  and is_flat_setth     st  = is_var_setth      st  || is_constant_setth      st
  and is_flat_setelem   se  = is_var_setelem    se  || is_constant_setelem    se
  and is_flat_elem      e   = is_var_elem       e   || is_constant_elem       e
  and is_flat_thid      th  = is_var_thid       th  || is_constant_thid       th
  and is_flat_addr      a   = is_var_addr       a   || is_constant_addr       a
  and is_flat_cell      c   = is_var_cell       c   || is_constant_cell       c
  and is_flat_mem       m   = is_var_mem        m   || is_constant_mem        m
  and is_flat_int       i   = is_var_int        i   || is_constant_int        i
  and is_flat_tidarr    tt  = is_var_tidarr     tt  || is_constant_tidarr     tt
  and is_flat_bucketarr bb  = is_var_bucketarr  bb  || is_constant_bucketarr  bb
  and is_flat_mark      m   = is_var_mark       m   || is_constant_mark       m
  and is_flat_bucket    b   = is_var_bucket     b   || is_constant_bucket     b
  and is_flat_lock      l   = is_var_lock       l   || is_constant_lock       l
  and is_flat_lockarr   ll  = is_var_lockarr    ll  || is_constant_lockarr    ll
  and is_flat_path      p   = is_var_path       p   || is_constant_path       p
  
  let is_flat_term t =
    match t with
        ThmExp.VarT   _          -> true
      | ThmExp.SetT   s          -> is_flat_set s
      | ThmExp.ElemT  e          -> is_flat_elem e
      | ThmExp.TidT  th          -> is_flat_thid th
      | ThmExp.AddrT  a          -> is_flat_addr a
      | ThmExp.CellT  c          -> is_flat_cell c
      | ThmExp.SetThT st         -> is_flat_setth st
      | ThmExp.SetElemT se       -> is_flat_setelem se
      | ThmExp.PathT  p          -> is_flat_path p
      | ThmExp.MemT   m          -> is_flat_mem m
      | ThmExp.IntT   i          -> is_flat_int i
      | ThmExp.TidArrayT tt      -> is_flat_tidarr tt
      | ThmExp.BucketArrayT bb   -> is_flat_bucketarr bb
      | ThmExp.MarkT  m          -> is_flat_mark m
      | ThmExp.BucketT b         -> is_flat_bucket b
      | ThmExp.LockT l           -> is_flat_lock l
      | ThmExp.LockArrayT ll     -> is_flat_lockarr ll
      | ThmExp.VarUpdate _       -> false
  
  
  let is_flat_literal lit =
    match lit with
      | ThmExp.Append(p1,p2,p3)      -> is_var_path p1 && is_var_path p2 &&
                                        is_var_path p3
      | ThmExp.Reach(m,a1,a2,p)      -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2 && is_var_path p
      | ThmExp.OrderList(m,a1,a2)    -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2
      | ThmExp.Hashmap(m,s,se,bb,i)  -> is_var_mem m && is_var_set s &&
                                        is_var_setelem se && is_var_bucketarr bb &&
                                        is_var_int i
      | ThmExp.In (a,s)              -> is_var_addr a && is_var_set s
      | ThmExp.SubsetEq(s1,s2)       -> is_var_set s1 && is_var_set s2
      | ThmExp.InTh(t,st)            -> is_var_thid t && is_var_setth st
      | ThmExp.SubsetEqTh(st1,st2)   -> is_var_setth st1 && is_var_setth st2
      | ThmExp.InElem(e,se)          -> is_var_elem e && is_var_setelem se
      | ThmExp.SubsetEqElem(se1,se2) -> is_var_setelem se1 && is_var_setelem se2
      | ThmExp.Less(i1,i2)           -> is_var_int i1 && is_var_int i2
      | ThmExp.LessEq(i1,i2)         -> is_var_int i1 && is_var_int i2
      | ThmExp.Greater(i1,i2)        -> is_var_int i1 && is_var_int i2
      | ThmExp.GreaterEq(i1,i2)      -> is_var_int i1 && is_var_int i2
      | ThmExp.LessElem(e1,e2)       -> is_var_elem e1 && is_var_elem e2
      | ThmExp.GreaterElem(e1,e2)    -> is_var_elem e1 && is_var_elem e2
      | ThmExp.Eq((t1,t2))           -> is_var_term t1 && is_var_term t2
      | ThmExp.InEq((t1,t2))         -> is_var_term t1 && is_var_term t2
      | ThmExp.BoolVar _             -> true
      | ThmExp.PC _                  -> true
      | ThmExp.PCUpdate _            -> true
      | ThmExp.PCRange _             -> true
  
  let is_flat expr =
    List.for_all is_flat_literal expr
      
  
  (* INVOCATIONS TRANSFORMING TO DNF FIRST *)
  let check_sat_conj (lines : int)
                  (use_q : bool)
                  (phi : ThmExp.conjunctive_formula) : Sat.t =
    match phi with
      | Formula.TrueConj   -> Sat.Sat
      | Formula.FalseConj  -> Sat.Unsat
      | Formula.Conj conjs ->
        begin
          let module Q = (val QueryManager.get_thm_query Solver.identifier) in
          let module Trans = Solver.Translate.Thm.Query(Q) in
          Trans.set_prog_lines lines;
          Solver.check_sat (Trans.literal_list use_q conjs)
        end
  
  let check_sat_dnf (prog_lines : int)
                 (use_q : bool)
                 (phi : ThmExp.formula) : Sat.t =
    let dnf_phi = Formula.dnf phi in
    let check phi = Sat.is_sat (check_sat_conj prog_lines use_q phi) in
    if List.exists check dnf_phi then
      Sat.Sat
    else
      Sat.Unsat
  
  
  let check_valid_dnf (prog_lines : int)
                   (use_q : bool)
                   (phi : ThmExp.formula) : Valid.t =
    let dnf_phi       = Formula.dnf (Formula.Not phi) in
    let is_unsat conj = Sat.is_unsat
                          (check_sat_conj prog_lines use_q conj) in
    if (List.for_all is_unsat dnf_phi) then
      Valid.Valid
    else
      Valid.Invalid

  
  
  let check_valid_dnf_pus_info (prog_lines:int)
                            (use_q : bool)
                            (phi:ThmExp.formula) : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid_dnf prog_lines use_q phi in
    (res, Solver.calls_count ())
  
  
  (* INVOCATIONS WITHOUT CONVERTING TO DNF *)
  let check_sat (lines : int)
             (co : Smp.cutoff_strategy_t)
             (use_q : bool)
             (phi : ThmExp.formula) : Sat.t =
(*    LOG "Entering check_sat..." LEVEL TRACE; *)
    match phi with
    | Formula.Not(Formula.Implies(_,Formula.True)) ->
        (Solver.calls_force_incr(); Sat.Unsat)
    | Formula.Not (Formula.Implies(Formula.False, _)) ->
        (Solver.calls_force_incr(); Sat.Unsat)
    | Formula.Implies(Formula.False, _) ->
        (Solver.calls_force_incr(); Sat.Sat)
    | Formula.Implies(_, Formula.True) ->
        (Solver.calls_force_incr(); Sat.Sat)
    | _ -> begin
             verbl _LONG_INFO "**** THM Solver, about to translate THM...\n";
             let module Q = (val QueryManager.get_thm_query Solver.identifier) in
             let module Trans = Solver.Translate.Thm.Query(Q) in
             Trans.set_prog_lines lines;
             Solver.check_sat (Trans.formula co cutoff_opt use_q phi)
           end
  
  let check_valid (prog_lines:int)
               (co:Smp.cutoff_strategy_t)
               (use_q : bool)
               (phi:ThmExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat prog_lines co use_q (Formula.Not phi))
  
  let check_valid_plus_info (prog_lines:int)
                         (co:Smp.cutoff_strategy_t)
                         (use_q : bool)
                         (phi:ThmExp.formula) : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid prog_lines co use_q phi in
    (res, Solver.calls_count())


  let search_type_to_str (model:GM.t) (sm:GM.sort_map_t) (s:GM.sort) : string =
    let xs = GM.sm_dom_of_type sm (GM.Const s) @
             GM.sm_dom_of_type sm (GM.Fun ([GM.tid_s],[s]))
    in
      GM.id_list_to_str model xs


let search_sets_to_str (model:GM.t) (sm:GM.sort_map_t) (s:GM.sort) : string =
  let set_to_str (id:GM.id) : string =
    let elems = Hashtbl.fold (fun es b xs ->
                  match (es,b) with
                  | ([Some e], GM.Single "true") -> e :: xs
                  | ([None]  , GM.Single "true") -> "_" :: xs
                  | _                            -> xs
                ) (GM.get_fun model id) [] in
    Printf.sprintf "%s = {%s}\n" id (String.concat "," elems) in
  let local_set_to_str (id:GM.id) : string =
    let locTbl = Hashtbl.create 10 in
    let _ = Hashtbl.iter (fun es b ->
              match es with
              | x::y::[] -> begin
                              try
                                let zs = Hashtbl.find locTbl x in
                                Hashtbl.replace locTbl x ((y,b)::zs)
                              with
                                _ -> Hashtbl.add locTbl x [(y,b)]
                            end
              | _ -> ()
            ) (GM.get_fun model id) in
    Hashtbl.fold (fun t es str ->
      let elems = List.fold_left (fun xs elem ->
                    match elem with
                    | (Some e, GM.Single "true") -> e::xs
                    | (None  , GM.Single "true") -> "_"::xs
                    | _                          -> xs
                  ) [] es in
      str ^ (Printf.sprintf "%s[%s] = {%s}\n" id (Option.default "_" t)
              (String.concat "," elems))
    ) locTbl "" in
  let gSets = GM.sm_dom_of_type sm (GM.Const s) in
  let lSets = GM.sm_dom_of_type sm (GM.Fun ([GM.tid_s],[s])) in
    (List.fold_left (fun str s -> str ^ set_to_str s) "" gSets) ^
    (List.fold_left (fun str s -> str ^ local_set_to_str s) "" lSets)


  let compute_model (b:bool) : unit =
    let _ = comp_model := b
    in
      Solver.compute_model b


  let model_to_str () : string =
    let module Q = (val QueryManager.get_thm_query Solver.identifier) in
    let module Trans = Solver.Translate.Thm.Query(Q) in
    let query_sort_map = Trans.sort_map () in
    let model = Solver.get_model () in
    let sort_map = GM.sm_union query_sort_map (GM.get_aux_sort_map model) in
    let thid_str = search_type_to_str model sort_map GM.tid_s in
    let int_str  = search_type_to_str model sort_map GM.int_s in
    let addr_str = search_type_to_str model sort_map GM.addr_s in
    let elem_str = search_type_to_str model sort_map GM.elem_s in
    let cell_str = search_type_to_str model sort_map GM.cell_s in
    let path_str = search_type_to_str model sort_map GM.path_s in
    (* Special description for sets *)
    let set_str = search_sets_to_str model sort_map GM.set_s in
    let setth_str = search_sets_to_str model sort_map GM.setth_s in
    let setelem_str = search_sets_to_str model sort_map GM.setelem_s in
    (* Special description for sets *)
    let heap_str = search_type_to_str model sort_map GM.heap_s
    in
      "\nThreads:\n" ^ thid_str ^
      "\nIntegers:\n" ^ int_str ^
      "\nAddresses:\n" ^ addr_str ^
      "\nElements:\n" ^ elem_str ^
      "\nCells:\n" ^ cell_str ^
      "\nPaths:\n" ^ path_str ^
      "\nSets:\n" ^ set_str ^
      "\nSets of tids:\n" ^ setth_str ^
      "\nSets of elements:\n" ^ setelem_str ^
      "\nHeap:\n" ^ heap_str

  let print_model () : unit =
    if !comp_model && (not (GM.is_empty_model (Solver.get_model()))) then
      print_endline (model_to_str())
    else
      ()


  let set_forget_primed_mem (b:bool) : unit =
    Smp.set_forget_primed_mem cutoff_opt b


  let set_group_vars (b:bool) : unit =
    Smp.set_group_vars cutoff_opt b

end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.thmTbl solverIdent
    with Not_found -> BackendSolvers.defaultThm () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_THM) in
  (module Make(Sol) : S)
