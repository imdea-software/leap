open LeapLib
open LeapVerbose

module type CUSTOM_TLLSOLVER = sig
  module TllExp : ExpressionTypes.TLLEXP
  
  
  val is_sat_conj  : int -> TllExp.conjunctive_formula -> bool
  val is_sat_dnf   : int -> TllExp.formula -> bool
  
  val is_valid_dnf : int -> TllExp.formula -> bool
  val is_valid_dnf_pus_info 
                   : int -> TllExp.formula -> (bool * int)
    
  val is_sat       : int ->
                     Smp.cutoff_strategy_t ->
                     TllExp.formula -> bool
  val is_valid     : int ->
                     Smp.cutoff_strategy_t ->
                     TllExp.formula -> bool
  
  val is_valid_plus_info 
                   : int ->
                     Smp.cutoff_strategy_t ->
                     TllExp.formula -> (bool * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TLLSOLVER
  with module TllExp = TllExpression
  
module Make(Solver : BackendSolverIntf.BACKEND_TLL) : S =
struct
  module TllExp   = Solver.Translate.Tll.Exp
  module VarIdSet = TllExp.V.VarIdSet
  module GM       = GenericModel

  let comp_model : bool ref = ref false

  let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
  
  (* 
   * is_var 
   *)
  let is_var_path = function
      TllExp.VarPath(_) -> true
    | _               -> false
  and is_var_addr = function
      TllExp.VarAddr(_) -> true
    | _               -> false
  and is_var_mem = function
      TllExp.VarMem(_) -> true
    | _              -> false
  and is_var_int = function
      TllExp.VarInt(_) -> true
    | _              -> false

  and is_var_cell = function
      TllExp.VarCell(_) -> true
    | _               -> false
  and is_var_elem = function
      TllExp.VarElem(_) -> true
    | _               -> false
  and is_var_thid = function
      TllExp.VarTh(_) -> true
    | _             -> false
  and is_var_set = function
      TllExp.VarSet(_) -> true
    | _              -> false
  and is_var_setth = function
      TllExp.VarSetTh(_) -> true
    | _                -> false
  and is_var_setelem = function
      TllExp.VarSetElem(_) -> true
    | _                    -> false
  
  let is_var_term = function
      TllExp.VarT(_)     -> true
    | TllExp.SetT(s)     -> is_var_set s
    | TllExp.ElemT(e)    -> is_var_elem e
    | TllExp.TidT(t)    -> is_var_thid t
    | TllExp.AddrT(a)    -> is_var_addr a
    | TllExp.CellT(c)    -> is_var_cell c
    | TllExp.SetThT(st)  -> is_var_setth st
    | TllExp.SetElemT(st)-> is_var_setelem st
    | TllExp.PathT(p)    -> is_var_path p
    | TllExp.MemT(m)     -> is_var_mem m
    | TllExp.IntT(i)     -> is_var_int i
    | TllExp.VarUpdate _ -> false (* ALE: Not sure if OK *)
  
  (* 
   * is_constant 
   *)
  let is_constant_set = function
        TllExp.EmptySet -> true
      | _             -> false
  and is_constant_setth = function
        TllExp.EmptySetTh -> true
      | _               -> false
  and is_constant_setelem = function
        TllExp.EmptySetElem -> true
      | _                   -> false
  and is_constant_elem = function
        TllExp.LowestElem  -> true
      | TllExp.HighestElem -> true
      | _                  -> false
  and is_constant_thid = function
        TllExp.NoTid -> true
      | _             -> false
  and is_constant_addr =  function
        TllExp.Null -> true
      | _         -> false
  and is_constant_cell = function
        TllExp.Error -> true
      | _          -> false
  and is_constant_path = function
        TllExp.Epsilon -> true
      | _            -> false
  and is_constant_mem  = function
        TllExp.Emp -> true
      | _        -> false
  and is_constant_int  = function
        TllExp.IntVal _ -> true
      | _        -> false
  
  let is_constant_term = function
        TllExp.VarT(_)     -> false
      | TllExp.SetT(s)     -> is_constant_set s
      | TllExp.ElemT(e)    -> is_constant_elem e
      | TllExp.TidT(th)   -> is_constant_thid th
      | TllExp.AddrT(a)    -> is_constant_addr a
      | TllExp.CellT(c)    -> is_constant_cell c
      | TllExp.SetThT(st)  -> is_constant_setth st
      | TllExp.SetElemT(st)-> is_constant_setelem st
      | TllExp.PathT(p)    -> is_constant_path p
      | TllExp.MemT(m)     -> is_constant_mem m
      | TllExp.IntT(i)     -> is_constant_int i
      | TllExp.VarUpdate _ -> false
  
  (* 
   * is_flat
   *)
  
  let is_flat_set     s  = is_var_set     s  || is_constant_set     s
  and is_flat_setth   st = is_var_setth   st || is_constant_setth   st
  and is_flat_setelem se = is_var_setelem se || is_constant_setelem se
  and is_flat_elem    e  = is_var_elem    e  || is_constant_elem    e
  and is_flat_thid    th = is_var_thid    th || is_constant_thid    th
  and is_flat_addr    a  = is_var_addr    a  || is_constant_addr    a
  and is_flat_cell    c  = is_var_cell    c  || is_constant_cell    c
  and is_flat_mem     m  = is_var_mem     m  || is_constant_mem     m
  and is_flat_int     i  = is_var_int     i  || is_constant_int     i
  and is_flat_path    p  = is_var_path    p  || is_constant_path    p
  
  let is_flat_term t =
    match t with
        TllExp.VarT   _    -> true
      | TllExp.SetT   s    -> is_flat_set s
      | TllExp.ElemT  e    -> is_flat_elem e
      | TllExp.TidT  th   -> is_flat_thid th
      | TllExp.AddrT  a    -> is_flat_addr a
      | TllExp.CellT  c    -> is_flat_cell c
      | TllExp.SetThT st   -> is_flat_setth st
      | TllExp.SetElemT se -> is_flat_setelem se
      | TllExp.PathT  p    -> is_flat_path p
      | TllExp.MemT   m    -> is_flat_mem m
      | TllExp.IntT   i    -> is_flat_int i
      | TllExp.VarUpdate _ -> false
  
  
  let is_flat_literal lit =
    match lit with
      | TllExp.Append(p1,p2,p3)      -> is_var_path p1 && is_var_path p2 &&
                                        is_var_path p3
      | TllExp.Reach(m,a1,a2,p)      -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2 && is_var_path p
      | TllExp.OrderList(m,a1,a2)    -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2
      | TllExp.In (a,s)              -> is_var_addr a && is_var_set s
      | TllExp.SubsetEq(s1,s2)       -> is_var_set s1 && is_var_set s2
      | TllExp.InTh(t,st)            -> is_var_thid t && is_var_setth st
      | TllExp.SubsetEqTh(st1,st2)   -> is_var_setth st1 && is_var_setth st2
      | TllExp.InElem(e,se)          -> is_var_elem e && is_var_setelem se
      | TllExp.SubsetEqElem(se1,se2) -> is_var_setelem se1 && is_var_setelem se2
      | TllExp.Less(i1,i2)           -> is_var_int i1 && is_var_int i2
      | TllExp.LessEq(i1,i2)         -> is_var_int i1 && is_var_int i2
      | TllExp.Greater(i1,i2)        -> is_var_int i1 && is_var_int i2
      | TllExp.GreaterEq(i1,i2)      -> is_var_int i1 && is_var_int i2
      | TllExp.LessElem(e1,e2)       -> is_var_elem e1 && is_var_elem e2
      | TllExp.GreaterElem(e1,e2)    -> is_var_elem e1 && is_var_elem e2
      | TllExp.Eq((t1,t2))           -> is_var_term t1 && is_var_term t2
      | TllExp.InEq((t1,t2))         -> is_var_term t1 && is_var_term t2
      | TllExp.BoolVar v             -> true
      | TllExp.PC(pc,t,pr)           -> true
      | TllExp.PCUpdate (pc,t)       -> true
      | TllExp.PCRange(pc1,pc2,t,pr) -> true
  
  let is_flat expr =
    List.for_all is_flat_literal expr
      
  
  (* INVOCATIONS TRANSFORMING TO DNF FIRST *)
  let is_sat_conj (lines : int) (phi : TllExp.conjunctive_formula) : bool =
    match phi with
        Formula.TrueConj   -> true
      | Formula.FalseConj  -> false
      | Formula.Conj conjs ->
        begin
          let module Q = (val QueryManager.get_tll_query Solver.identifier) in
          let module Trans = Solver.Translate.Tll.Query(Q) in
          Trans.set_prog_lines lines;
          Solver.sat (Trans.literal_list conjs)
        end
  
  let is_sat_dnf (prog_lines : int) (phi : TllExp.formula) : bool =
    let dnf_phi = Formula.dnf phi in
      List.exists (is_sat_conj prog_lines) dnf_phi
  
  
  let is_valid_dnf (prog_lines : int) (phi : TllExp.formula) : bool =
    let dnf_phi       = Formula.dnf (Formula.Not phi) in
    let is_unsat conj = (not (is_sat_conj prog_lines conj))
    in List.for_all is_unsat dnf_phi
  
  
  let is_valid_dnf_pus_info (prog_lines:int)
      (phi:TllExp.formula) : (bool * int) =
    Solver.reset_calls ();
    let res = is_valid_dnf prog_lines phi in
    (res, Solver.calls_count ())
  
  
  (* INVOCATIONS WITHOUT CONVERTING TO DNF *)
  let is_sat (lines : int)
             (co : Smp.cutoff_strategy_t)
             (phi : TllExp.formula) : bool =
(*    LOG "Entering is_sat..." LEVEL TRACE; *)
    match phi with
    | Formula.Not(Formula.Implies(_,Formula.True)) -> (Solver.calls_force_incr(); false)
    | Formula.Not (Formula.Implies(Formula.False, _)) -> (Solver.calls_force_incr(); false)
    | Formula.Implies(Formula.False, _) -> (Solver.calls_force_incr(); true)
    | Formula.Implies(_, Formula.True) -> (Solver.calls_force_incr(); true)
    | _ -> begin
             verbl _LONG_INFO "**** TLL Solver, about to translate TLL...\n";
             let module Q = (val QueryManager.get_tll_query Solver.identifier) in
             let module Trans = Solver.Translate.Tll.Query(Q) in
             Trans.set_prog_lines lines;
             Solver.sat (Trans.formula co cutoff_opt phi)
           end
  
  let is_valid (prog_lines:int)
               (co:Smp.cutoff_strategy_t)
               (phi:TllExp.formula) : bool =
    not (is_sat prog_lines co (Formula.Not phi))
  
  let is_valid_plus_info (prog_lines:int)
                         (co:Smp.cutoff_strategy_t)
                         (phi:TllExp.formula) : (bool * int) =
    Solver.reset_calls ();
    let res = is_valid prog_lines co phi in
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
    let module Q = (val QueryManager.get_tll_query Solver.identifier) in
    let module Trans = Solver.Translate.Tll.Query(Q) in
    let sort_map = Trans.sort_map () in
    let model = Solver.get_model () in
    let thid_str = search_type_to_str model sort_map GM.tid_s in
    let pc_str   = search_type_to_str model sort_map GM.loc_s in
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
      "\nProgram counters:\n" ^ pc_str ^
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
  let m = try Hashtbl.find BackendSolvers.tllTbl solverIdent
    with Not_found -> BackendSolvers.defaultTll () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_TLL) in
  (module Make(Sol) : S)
