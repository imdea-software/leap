open LeapLib

module type CUSTOM_TSLKSOLVER = sig
  module TslkExp : ExpressionTypes.TSLKEXP
 
(*
  module Smp : sig
    type cutoff_strategy
  end
*)
  
  val is_sat_conj  : int -> TslkExp.conjunctive_formula -> bool
  val is_sat_dnf   : int -> TslkExp.formula -> bool
  
  val is_valid_dnf : int -> TslkExp.formula -> bool
  val is_valid_dnf_pus_info 
                   : int -> TslkExp.formula -> (bool * int)
    
  val is_sat       : int ->
                     Tactics.solve_tactic_t option ->
                     SmpTslk.cutoff_strategy ->
                     TslkExp.formula -> bool
  val is_valid     : int ->
                     Tactics.solve_tactic_t option ->
                     SmpTslk.cutoff_strategy ->
                     TslkExp.formula -> bool
  
  val is_valid_plus_info 
                   : int ->
                     Tactics.solve_tactic_t option ->
                     SmpTslk.cutoff_strategy ->
                     TslkExp.formula -> (bool * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TSLKSOLVER
(*  with module TslkExp = TslkExpression *)
(*  with module Smp = SmpTslk *)


module Make(K : Level.S) (Solver : BackendSolverIntf.BACKEND_TSLK) : S =
struct
  module TslkSol = Solver.Translate.Tslk(K)
  module TslkExp = TslkSol.Exp
  module Smp     = SmpTslk
(*
  module TslkExp  = Solver.Translate.Tslk.Exp
  module Smp      = Solver.Translate.Tslk.Smp
*)
  module VarIdSet = TslkExp.VarIdSet
  module GM       = GenericModel

  let comp_model : bool ref = ref false

  let cutoff_opt : SmpTslk.cutoff_options_t = SmpTslk.opt_empty()
  
  (* 
   * is_var 
   *)
  let is_var_path = function
      TslkExp.VarPath(_) -> true
    | _               -> false
  and is_var_addr = function
      TslkExp.VarAddr(_) -> true
    | _               -> false
  and is_var_mem = function
      TslkExp.VarMem(_) -> true
    | _              -> false
  and is_var_level = function
      TslkExp.VarLevel(_) -> true
    | _              -> false
  and is_var_cell = function
      TslkExp.VarCell(_) -> true
    | _               -> false
  and is_var_elem = function
      TslkExp.VarElem(_) -> true
    | _               -> false
  and is_var_thid = function
      TslkExp.VarTh(_) -> true
    | _             -> false
  and is_var_set = function
      TslkExp.VarSet(_) -> true
    | _              -> false
  and is_var_setth = function
      TslkExp.VarSetTh(_) -> true
    | _                -> false
  and is_var_setelem = function
      TslkExp.VarSetElem(_) -> true
    | _                    -> false
  
  let is_var_term = function
      TslkExp.VarT(_)     -> true
    | TslkExp.SetT(s)     -> is_var_set s
    | TslkExp.ElemT(e)    -> is_var_elem e
    | TslkExp.ThidT(t)    -> is_var_thid t
    | TslkExp.AddrT(a)    -> is_var_addr a
    | TslkExp.CellT(c)    -> is_var_cell c
    | TslkExp.SetThT(st)  -> is_var_setth st
    | TslkExp.SetElemT(st)-> is_var_setelem st
    | TslkExp.PathT(p)    -> is_var_path p
    | TslkExp.MemT(m)     -> is_var_mem m
    | TslkExp.LevelT(l)   -> is_var_level l
    | TslkExp.VarUpdate _ -> false (* ALE: Not sure if OK *)
  
  (* 
   * is_constant 
   *)
  let is_constant_set = function
        TslkExp.EmptySet -> true
      | _             -> false
  and is_constant_setth = function
        TslkExp.EmptySetTh -> true
      | _               -> false
  and is_constant_setelem = function
        TslkExp.EmptySetElem -> true
      | _                   -> false
  and is_constant_elem e = false
  and is_constant_thid th = false
  and is_constant_addr =  function
        TslkExp.Null -> true
      | _         -> false
  and is_constant_cell = function
        TslkExp.Error -> true
      | _          -> false
  and is_constant_path = function
        TslkExp.Epsilon -> true
      | _            -> false
  and is_constant_mem  = function
        TslkExp.Emp -> true
      | _        -> false
  and is_constant_level = function
        TslkExp.LevelVal _ -> true
      | _        -> false
  
  let is_constant_term = function
        TslkExp.VarT(_)     -> false
      | TslkExp.SetT(s)     -> is_constant_set s
      | TslkExp.ElemT(e)    -> is_constant_elem e
      | TslkExp.ThidT(th)   -> is_constant_thid th
      | TslkExp.AddrT(a)    -> is_constant_addr a
      | TslkExp.CellT(c)    -> is_constant_cell c
      | TslkExp.SetThT(st)  -> is_constant_setth st
      | TslkExp.SetElemT(st)-> is_constant_setelem st
      | TslkExp.PathT(p)    -> is_constant_path p
      | TslkExp.MemT(m)     -> is_constant_mem m
      | TslkExp.LevelT(l)   -> is_constant_level l
      | TslkExp.VarUpdate _ -> false
  
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
  and is_flat_level   l  = is_var_level   l  || is_constant_level   l
  and is_flat_path    p  = is_var_path    p  || is_constant_path    p
  
  let is_flat_term t =
    match t with
        TslkExp.VarT   _    -> true
      | TslkExp.SetT   s    -> is_flat_set s
      | TslkExp.ElemT  e    -> is_flat_elem e
      | TslkExp.ThidT  th   -> is_flat_thid th
      | TslkExp.AddrT  a    -> is_flat_addr a
      | TslkExp.CellT  c    -> is_flat_cell c
      | TslkExp.SetThT st   -> is_flat_setth st
      | TslkExp.SetElemT se -> is_flat_setelem se
      | TslkExp.PathT  p    -> is_flat_path p
      | TslkExp.MemT   m    -> is_flat_mem m
      | TslkExp.LevelT l    -> is_flat_level l
      | TslkExp.VarUpdate _ -> true
  
  
  let is_flat_literal lit =
    match lit with
      | TslkExp.Append(p1,p2,p3)      -> is_var_path p1 && is_var_path p2 &&
                                        is_var_path p3
      | TslkExp.Reach(m,a1,a2,p)      -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2 && is_var_path p
      | TslkExp.OrderList(m,a1,a2)    -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2
      | TslkExp.In (a,s)              -> is_var_addr a && is_var_set s
      | TslkExp.SubsetEq(s1,s2)       -> is_var_set s1 && is_var_set s2
      | TslkExp.InTh(t,st)            -> is_var_thid t && is_var_setth st
      | TslkExp.SubsetEqTh(st1,st2)   -> is_var_setth st1 && is_var_setth st2
      | TslkExp.InElem(e,se)          -> is_var_elem e && is_var_setelem se
      | TslkExp.SubsetEqElem(se1,se2) -> is_var_setelem se1 && is_var_setelem se2
      | TslkExp.Less(l1,l2)           -> is_var_level l1 && is_var_level l2
      | TslkExp.LessEq(l1,l2)         -> is_var_level l1 && is_var_level l2
      | TslkExp.Greater(l1,l2)        -> is_var_level l1 && is_var_level l2
      | TslkExp.GreaterEq(l1,l2)      -> is_var_level l1 && is_var_level l2
      | TslkExp.LessElem(e1,e2)       -> is_var_elem e1 && is_var_elem e2
      | TslkExp.GreaterElem(e1,e2)    -> is_var_elem e1 && is_var_elem e2
      | TslkExp.Eq((t1,t2))           -> is_var_term t1 && is_var_term t2
      | TslkExp.InEq((t1,t2))         -> is_var_term t1 && is_var_term t2
      | TslkExp.PC(pc,t,pr)           -> true
      | TslkExp.PCUpdate (pc,t)       -> true
      | TslkExp.PCRange(pc1,pc2,t,pr) -> true
  
  let is_flat expr =
    List.for_all is_flat_literal expr
      
  
  (* INVOCATIONS TRANSFORMING TO DNF FIRST *)
  let is_sat_conj (lines : int) (phi : TslkExp.conjunctive_formula) : bool =
    match phi with
        TslkExp.TrueConj   -> true
      | TslkExp.FalseConj  -> false
      | TslkExp.Conj conjs -> 
        begin
          Solver.set_prog_lines lines;
          Solver.sat (TslkSol.literal_list conjs)
        end
  
  let is_sat_dnf (prog_lines : int) (phi : TslkExp.formula) : bool =
    let dnf_phi = TslkExp.dnf phi in
      List.exists (is_sat_conj prog_lines) dnf_phi
  
  
  let is_valid_dnf (prog_lines : int) (phi : TslkExp.formula) : bool =
    let dnf_phi       = TslkExp.dnf (TslkExp.Not phi) in
    let is_unsat conj = (not (is_sat_conj prog_lines conj))
    in List.for_all is_unsat dnf_phi
  
  
  let is_valid_dnf_pus_info (prog_lines:int)
      (phi:TslkExp.formula) : (bool * int) =
    Solver.reset_calls ();
    let res = is_valid_dnf prog_lines phi in
    (res, Solver.calls_count ())
  
  
  (* INVOCATIONS WITHOUT CONVERTING TO DNF *)
  let is_sat (lines : int)
             (stac:Tactics.solve_tactic_t option)
             (co : SmpTslk.cutoff_strategy)
             (phi : TslkExp.formula) : bool =
    Solver.set_prog_lines lines;
    Solver.sat (TslkSol.formula stac co cutoff_opt phi)
  
  let is_valid (prog_lines:int)
               (stac:Tactics.solve_tactic_t option)
               (co:Smp.cutoff_strategy)
               (phi:TslkExp.formula) : bool =
    not (is_sat prog_lines stac co (TslkExp.Not phi))
  
  let is_valid_plus_info (prog_lines:int)
                         (stac:Tactics.solve_tactic_t option)
                         (co:Smp.cutoff_strategy)
                         (phi:TslkExp.formula) : (bool * int) =
    Solver.reset_calls ();
    let res = is_valid prog_lines stac co phi in
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
    let sort_map = TslkSol.sort_map () in
    let model = Solver.get_model () in
    let thid_str = search_type_to_str model sort_map GM.tid_s in
    let pc_str   = search_type_to_str model sort_map GM.loc_s in
    let addr_str = search_type_to_str model sort_map GM.addr_s in
    let elem_str = search_type_to_str model sort_map GM.elem_s in
    let cell_str = search_type_to_str model sort_map GM.cell_s in
    let path_str = search_type_to_str model sort_map GM.path_s in
    let level_str = search_type_to_str model sort_map GM.level_s in
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

end

let choose (solverIdent : string) (k : int) : (module S) =
  let m = try Hashtbl.find BackendSolvers.tslkTbl solverIdent
    with Not_found -> BackendSolvers.defaultTslk () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_TSLK) in
  let module K = struct let level = k end in
  (module Make(K)(Sol) : S)
