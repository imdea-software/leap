open LeapLib
open Printf

module Stm = Statement
module E   = Expression

type cond_effect_aux_t = E.formula list               * (*Condition list*)
                         (Stm.term * Stm.expr_t) list * (*Term/Expr assignment*)
                         E.pc_t                       * (*Current pc*)
                         E.pc_t                       * (*Next pc*)
                         bool                           (*Can be extended?*)

type cond_effect_t = E.formula * (* Condition list *)
                     E.formula * (* Term - Expression assignment *)
                     E.pc_t    * (* Current program counter *)
                     E.pc_t      (* Next program counter *)

type eqGenMode = NormalGenMode | ArrayGenMode

type malloc_info =
  {
    tids       : E.tid list;
    gAddrs     : E.variable list;
    gSets      : E.variable list;
    lAddrs     : E.variable list;
    lSets      : E.variable list;
  }

type prog_type = Num | Heap


exception Invalid_argument
exception Not_implemented of string


(* Pretty printers *)

let cond_effect_aux_to_str (cond:cond_effect_aux_t) : string =
  let (fs,es,c,n,e) = cond in
  Printf.sprintf "Formula: %s\n\
                  Assignment: %s\n\
                  Current: %i\n\
                  Next: %i\n\
                  Extended?: %s\n"
    (String.concat "," (List.map E.formula_to_str fs))
    (String.concat ";" (List.map (fun (t,e) ->
                          Stm.term_to_str t ^ ":=" ^ Stm.expr_to_str e)
                        es))
    (c) (n) (if e then "true" else "false")


(* FIX: This support is not extended to closed systems *)
let unfold_expression (mInfo:malloc_info)
                      (th_p:E.tid option)
                      (expr:Stm.expr_t) : (E.expr_t      *
                                           E.term list   *
                                           E.formula list) =
  LOG "Entering unfold_expression..." LEVEL TRACE;
  let gen_malloc (mkcell:E.cell) :
                 (E.expr_t * E.term list * E.formula list) =
    LOG "unfold_expression::gen_malloc()" LEVEL TRACE;
    let c_fresh = E.VarCell(E.build_var
                      E.fresh_cell_name E.Cell false None None E.Normal) in
    let a_fresh = E.VarAddr(E.build_var
                      E.fresh_addr_name E.Addr false None None E.Normal) in
    let diff_fresh a = E.ineq_addr a_fresh (E.VarAddr a) in
    let not_in_set s = E.Not (E.in_form a_fresh (E.VarSet s)) in
    let gDiffAddr = List.map diff_fresh mInfo.gAddrs in
    let gNotInSet = List.map not_in_set mInfo.gSets in
    let lDiffAddr = List.fold_left (fun xs t ->
                      xs @ List.map (fun v ->
                             diff_fresh (E.param_variable (Some t) v)
                           ) mInfo.lAddrs
                    ) [] mInfo.tids in
    let lNotInSet = List.fold_left (fun xs t ->
                      xs @ List.map (fun v ->
                             not_in_set (E.param_variable th_p v)
                           ) mInfo.lSets
                    ) [] mInfo.tids in
    let new_f = E.conj_list $
                  gDiffAddr @ gNotInSet @ lDiffAddr @ lNotInSet @
                  [
                    E.eq_cell c_fresh mkcell;
                    E.eq_cell (E.CellAt (E.heap, a_fresh)) E.Error;
                    E.eq_mem (E.prime_mem E.heap) (E.Update (E.heap, a_fresh, c_fresh))]
    in
      (E.Term (E.AddrT a_fresh), [E.MemT E.heap], [new_f])
  in
  match expr with
  | Stm.Term (Stm.AddrT (Stm.Malloc(e,a,t))) ->
      LOG "Malloc translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let e_expr  = Stm.elem_to_expr_elem e in
      let a_expr  = Stm.addr_to_expr_addr a in
      let t_expr  = Stm.tid_to_expr_tid t in
      let mkcell  = E.param_cell th_p (E.MkCell(e_expr, a_expr, t_expr)) in
        gen_malloc mkcell
  | Stm.Term (Stm.AddrT (Stm.MallocSLK(e,l))) ->
      LOG "MallocSLK translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let e_expr  = Stm.elem_to_expr_elem e in
      (* FIX: In fact, I am not using the parameter l *)
      let mkcell  = E.param_cell th_p (E.MkSLKCell(e_expr, [], [])) in
        gen_malloc mkcell
  | Stm.Term (Stm.AddrT (Stm.MallocSL(e,l))) ->
      LOG "MallocSL translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let e_expr   = Stm.elem_to_expr_elem e in
      let l_expr   = Stm.integer_to_expr_integer l in
      let aa_fresh = E.VarAddrArray(E.build_var
                       E.fresh_addrarr_name E.AddrArray false None None E.Normal) in
      let tt_fresh = E.VarTidArray(E.build_var
                       E.fresh_tidarr_name E.TidArray false None None E.Normal) in
      let i_fresh = E.VarInt(E.build_var
                       E.fresh_int_name E.Int false None None E.Normal) in
      let mkcell   = E.param_cell th_p
                       (E.MkSLCell(e_expr, aa_fresh, tt_fresh, l_expr)) in
      let (t,ms,fs) = gen_malloc mkcell in
      let fs' = List.map (fun f -> E.And
                                     (E.Implies
                                       (E.lesseq_form (E.IntVal 0) i_fresh,
                                        E.And
                                          (E.eq_addr (E.AddrArrRd(aa_fresh, i_fresh))
                                                     (E.Null),
                                           E.eq_tid (E.ThidArrRd(tt_fresh, i_fresh))
                                                    (E.NoThid))), f)) fs in
        (t,ms,fs')
  | Stm.Term (Stm.ElemT (Stm.PointerData a)) ->
      LOG "PointerData translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let a_expr = Stm.addr_to_expr_addr a in
      (E.Term (E.ElemT (E.CellData (E.CellAt (E.heap,a_expr)))), [], [])
  | Stm.Term (Stm.AddrT (Stm.PointerNext a)) ->
      LOG "PointerNext translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let a_expr = Stm.addr_to_expr_addr a in
      (E.Term (E.AddrT (E.Next (E.CellAt (E.heap,a_expr)))), [], [])
  | Stm.Term (Stm.AddrT (Stm.PointerNextAt (a,l))) ->
      LOG "PointerNextAt translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let a_expr = Stm.addr_to_expr_addr a in
      let l_expr = Stm.integer_to_expr_integer l in
      (E.Term (E.AddrT (E.AddrArrRd (E.CellArr (E.CellAt (E.heap,a_expr)), l_expr))), [], [])
(*
      (E.Term (E.AddrT (E.NextAt (E.CellAt (E.heap,a_expr), l_expr))), None, [], [])
*)
  | Stm.Term (Stm.ThidT (Stm.PointerLockid a)) ->
      LOG "PointerLockid translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let a_expr = Stm.addr_to_expr_addr a in
      (E.Term (E.ThidT (E.CellLockId (E.CellAt (E.heap,a_expr)))), [], [])
  | Stm.Term (Stm.ThidT (Stm.PointerLockidAt (a,l))) ->
      LOG "PointerLockidAt translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      let a_expr = Stm.addr_to_expr_addr a in
      let l_expr = Stm.integer_to_expr_integer l in
      (E.Term (E.ThidT (E.ThidArrRd (E.CellTids (E.CellAt (E.heap,a_expr)), l_expr))), [], [])
(*
      (E.Term (E.ThidT (E.CellLockIdAt (E.CellAt (E.heap,a_expr), l_expr))), None, [], [])
*)
  | _ ->
      LOG "Else translation of: %s" (Stm.expr_to_str expr) LEVEL DEBUG;
      (Stm.expr_to_expr_expr expr, [], [])



(* EXPRESSION PRESERVATION FUNCTIONS *)
let pres_th_param (t:E.term) (new_th:E.tid option) : E.tid option =
  let owner = E.get_var_owner t in
  match owner with
    Some _ -> new_th
  | None   -> None


(*
let construct_stm_term_eq (v:Stm.term)
                          (th_p:E.th_t option)
                          (e:Stm.expr_t) : (E.term list * E.formula) =

  let v' = Stm.term_to_expr_term v in
  let (new_e, aux_modif, aux_f) = unfold_expression e in
  let (modif,formula) = E.construct_term_eq v' th_p new_e
  in
    (modif @ aux_modif, E.conj_list (formula::aux_f))
*)


let generic_stm_term_eq (mode:eqGenMode)
                        (mInfo:malloc_info)
                        (pt:prog_type)
                        (v:Stm.term)
                        (th_p:E.tid option)
                        (e:Stm.expr_t) : (E.term list * E.formula) =
  let eq_generator = match mode with
                       NormalGenMode -> E.construct_term_eq
                     | ArrayGenMode  -> E.construct_term_eq_as_array in
  let heap_eq_generator v th e = let (mods,phi) = eq_generator v th e in
                                   (E.MemT E.heap::mods, phi) in
  let v' = Stm.term_to_expr_term v in
  let (new_e, aux_modif, aux_f) = unfold_expression mInfo th_p e in
(*  let aux_mem = Option.default E.heap mod_heap in *)
  let (modif,formula) =
    match (v', new_e) with
    (* CellData *)
    | (E.ElemT (E.CellData(E.CellAt(h,a))), E.Term(E.ElemT e')) ->
        let new_cell = E.MkCell(e',
                                E.Next(E.CellAt(E.heap,a)),
                                E.CellLockId(E.CellAt(E.heap,a))) in
          heap_eq_generator (E.MemT E.heap) th_p
              (E.Term(E.MemT(E.Update(E.heap,a,new_cell))))
    (* Next *)
    | (E.AddrT (E.Next(E.CellAt(h,a))), E.Term(E.AddrT a')) ->
        let new_cell = E.MkCell(E.CellData(E.CellAt(E.heap,a)),
                                a',
                                E.CellLockId(E.CellAt(E.heap,a))) in
        let new_term = E.param_term th_p (E.MemT(E.Update(E.heap,a,new_cell))) in
          heap_eq_generator (E.MemT E.heap) th_p (E.Term(new_term))
    (* NextAt *)
    | (E.AddrT (E.NextAt(E.CellAt(h,a), l)), E.Term(E.AddrT a')) ->
        let new_cell = E.MkSLCell(E.CellData(E.CellAt(E.heap,a)),
                                  E.AddrArrayUp(E.CellArr(E.CellAt(E.heap,a)),l,a'),
                                  E.CellTids(E.CellAt(E.heap,a)),
                                  E.CellMax(E.CellAt(E.heap,a))) in
        let new_term = E.param_term th_p (E.MemT(E.Update(E.heap,a,new_cell))) in
          heap_eq_generator (E.MemT E.heap) th_p (E.Term(new_term))
    (* CellArr *)
    | (E.AddrT (E.AddrArrRd (E.CellArr(E.CellAt(h,a)), l)), E.Term(E.AddrT a')) ->
        let new_cell = E.MkSLCell(E.CellData(E.CellAt(E.heap,a)),
                                  E.AddrArrayUp(E.CellArr(E.CellAt(E.heap,a)),l,a'),
                                  E.CellTids(E.CellAt(E.heap,a)),
                                  E.CellMax(E.CellAt(E.heap,a))) in
        let new_term = E.param_term th_p (E.MemT(E.Update(E.heap,a,new_cell))) in
          heap_eq_generator (E.MemT E.heap) th_p (E.Term(new_term))
    (* CellLockId *)
    | (E.ThidT (E.CellLockId(E.CellAt(h,a))), E.Term(E.ThidT t')) ->
        let new_cell = E.MkCell(E.CellData(E.CellAt(E.heap,a)),
                                E.Next(E.CellAt(E.heap,a)),
                                t') in
          heap_eq_generator (E.MemT E.heap) th_p
              (E.Term(E.MemT(E.Update(E.heap,a,new_cell))))
    (* CellLockIdAt *)
    | (E.ThidT (E.CellLockIdAt(E.CellAt(h,a),l)), E.Term(E.ThidT t')) ->
        let new_cell = E.MkSLCell(E.CellData(E.CellAt(E.heap,a)),
                                  E.CellArr(E.CellAt(E.heap,a)),
                                  E.TidArrayUp(E.CellTids(E.CellAt(E.heap,a)),l,t'),
                                  E.CellMax(E.CellAt(E.heap,a))) in
          heap_eq_generator (E.MemT E.heap) th_p
              (E.Term(E.MemT(E.Update(E.heap,a,new_cell))))
    (* CellTids *)
    | (E.ThidT (E.ThidArrRd(E.CellTids(E.CellAt(h,a)),l)), E.Term(E.ThidT t')) ->
        let new_cell = E.MkSLCell(E.CellData(E.CellAt(E.heap,a)),
                                  E.CellArr(E.CellAt(E.heap,a)),
                                  E.TidArrayUp(E.CellTids(E.CellAt(E.heap,a)),l,t'),
                                  E.CellMax(E.CellAt(E.heap,a))) in
          heap_eq_generator (E.MemT E.heap) th_p
              (E.Term(E.MemT(E.Update(E.heap,a,new_cell))))
    (* HavocListElem *)
    | (E.ElemT (E.VarElem v as e), E.Term (E.ElemT (E.HavocListElem))) ->
        ([E.ElemT (E.VarElem (E.var_base_info v))],
            E.And (E.ineq_elem (E.prime_elem (E.param_elem th_p e)) E.LowestElem,
                   E.ineq_elem (E.prime_elem (E.param_elem th_p e)) E.HighestElem))
    (* HavocSkiplistElem *)
    | (E.ElemT (E.VarElem v as e), E.Term (E.ElemT (E.HavocSkiplistElem))) ->
        ([E.ElemT (E.VarElem (E.var_base_info v))],
            E.And (E.ineq_elem (E.prime_elem (E.param_elem th_p e)) E.LowestElem,
                   E.ineq_elem (E.prime_elem (E.param_elem th_p e)) E.HighestElem))
    (* Remaining cases *)
    | _ -> eq_generator v' th_p new_e in
  (modif @ aux_modif, E.conj_list (formula::aux_f))



let construct_stm_term_eq (mInfo:malloc_info)
                          (pt:prog_type)
                          (v:Stm.term)
                          (th_p:E.tid option)
                          (e:Stm.expr_t) : (E.term list * E.formula) =
  generic_stm_term_eq NormalGenMode mInfo pt v th_p e


let construct_stm_term_eq_as_array (mInfo:malloc_info)
                                   (pt:prog_type)
                                   (v:Stm.term)
                                   (th_p:E.tid option)
                                   (e:Stm.expr_t) : (E.term list * E.formula) =
  generic_stm_term_eq ArrayGenMode mInfo pt v th_p e



(* Auxiliary transition effect construction function for ghost/atomic code *)
let rec gen_atomic_st_cond_effect (conds:cond_effect_aux_t list)
                                  (stm:Stm.statement_t)
                                    : cond_effect_aux_t list =
  let gen_atomic = gen_atomic_st_cond_effect in
  let to_expr    = Stm.boolean_to_expr_formula in
  match stm with
    Stm.StAwait(b,_,_)    -> List.fold_left (fun zs (cs,es,c,n,ext) ->
                               if ext then
                                 ((to_expr b)::cs,          es,c,n,ext)::
                                 ((to_expr (Stm.Not b))::cs,es,c,c,false)::zs
                               else
                                 (cs,es,c,n,ext) :: zs
                             ) [] conds
  | Stm.StAssign(t,e,_,_) -> List.map (fun (cs,es,c,n,ext) ->
                               if ext then
                                 (cs,(t,e)::es,c,n,ext)
                               else
                                 (cs,es,c,n,ext)
                             ) conds
  | Stm.StIf(b,t,e,_,_)   -> let then_map = List.map (fun (cs,es,c,n,ext) ->
                                              if ext then
                                                ((to_expr b)::cs,es,c,n,ext)
                                              else
                                                (cs,es,c,n,ext)
                                            ) conds in
                             let else_map = List.map (fun (cs,es,c,n,ext) ->
                                              if ext then
                                                (to_expr(Stm.Not b)::cs,es,c,n,ext)
                                              else
                                                (cs,es,c,n,ext)
                                            ) conds in
                             let gen_then = gen_atomic then_map t in
                             let gen_else = match e with
                                              Some expr -> gen_atomic else_map expr
                                            | None      -> gen_atomic else_map (Stm.StSeq [])
                             in
                               gen_then @ gen_else
  | Stm.StSeq stms -> List.fold_left gen_atomic conds stms
  | _ -> conds


(* Auxiliary transition effect construction functions *)
(* Generates the list of conditions and effects for a statment.
   Return a list of tuples [(c, [(t,e)], l, n)] meaning that when in line
   "l", if all conditions in "[c]" hold, effect represented by assignations of the list
   [(t,e)] is carried out, jumping finally to line "n"
*)
let rec gen_st_cond_effect_aux (is_ghost:bool)
                               (st:Stm.statement_t) : cond_effect_aux_t list =
  let to_expr             = Stm.boolean_to_expr_formula in
  let gen_atomic          = gen_atomic_st_cond_effect in
  let add_gc conds gc_opt = Option.map_default
                              (fun gc -> gen_atomic conds gc) conds gc_opt in
  let curr_p              = Stm.get_forced_st_pos st in
  let next_p              = Stm.get_forced_st_next_pos st in
  let else_p              = Stm.get_forced_st_else_pos st in
  let me_term             = Stm.ThidT Stm.me_tid in
  let def_assign          = [(me_term, Stm.Term me_term)]
  in
  let _ = Printf.printf "GEN_ST_COND: %s\n" (Stm.statement_to_str 0 st) in
  match st with
    Stm.StSkip (gc,info)       ->
      add_gc [([],def_assign,curr_p,next_p,true)] gc
  | Stm.StAssert (c,gc,info)   ->
      add_gc [([to_expr c],def_assign,curr_p,next_p,true)] gc
  | Stm.StAwait (c,gc,info)    ->
      add_gc [([to_expr c],         def_assign,curr_p,next_p,true);
              ([to_expr(Stm.Not c)],def_assign,curr_p,curr_p,false)] gc
  | Stm.StNonCrit (gc,info)    ->
      add_gc [([],def_assign,curr_p,next_p,true)] gc
  | Stm.StCrit (gc,info)       ->
      add_gc [([],def_assign,curr_p,next_p,true)] gc
  | Stm.StIf (c,t,e,gc,info)   ->
      let append cond xs = List.map (fun (cs,ef,c,n,e) -> (cond::cs,ef,c,n,e)) xs in
      if is_ghost then
        let true_res = append (to_expr c) (gen_st_cond_effect_aux true t) in
        let false_res = match e with
                        | None   -> [([to_expr(Stm.Not c)],def_assign,curr_p,else_p,true)]
                        | Some s -> append (to_expr(Stm.Not c)) (gen_st_cond_effect_aux true s)
        in
          true_res @ false_res
      else
         [([to_expr c],         def_assign,curr_p,next_p,true);
          ([to_expr(Stm.Not c)],def_assign,curr_p,else_p,true)]
  | Stm.StWhile (c,l,gc,info)  ->
      add_gc [([to_expr c],         def_assign,curr_p,next_p,true);
              ([to_expr(Stm.Not c)],def_assign,curr_p,else_p,true)] gc
  | Stm.StSelect (xs,gc,info)  ->
      let conds = match info with
                  | None     -> [([],def_assign,curr_p,next_p,true)]
                  | Some ops -> List.map (fun i ->
                                  ([],def_assign,curr_p,i,true)
                                ) ops.Stm.opt_pos
      in
        add_gc conds gc
  | Stm.StAssign (t,e,gc,info) ->
      add_gc [([],(t,e)::def_assign,curr_p,next_p,true)] gc
  (* FIX: To be implemented *)
  | Stm.StUnit (op,gc,info)    ->
      let msg = "StUnit case in function gen_st_cond_effect" in
        RAISE(Not_implemented msg)
  | Stm.StAtomic (xs,gc,info)  ->
      add_gc (gen_atomic_st_cond_effect [([],def_assign,curr_p,next_p,true)]
        (Stm.StSeq xs)) gc
  | Stm.StSeq xs               ->
      let conds = List.map (gen_st_cond_effect_aux is_ghost) xs in
      if is_ghost then
        let merge xs ys = List.fold_left (fun zs (cs_y,ef_y,c,n,e) ->
                            zs @ (List.map (fun (cs_x,ef_x,_,_,_) ->
                                    (cs_y@cs_x, ef_y@ef_x, c, n, e)
                                  ) xs)
                          ) [] ys in
        match conds with
        | [] -> []
        | cs::[] -> cs
        | cs1::cs2::css -> List.fold_left merge (merge cs1 cs2) css
      else
        List.flatten conds
  | Stm.StCall (t,proc,params,gc,info) ->
      add_gc [([],def_assign,curr_p,next_p,true)] gc
  (* FIX: I am not assigning the returned value *)
  | Stm.StReturn (t,gc,info)   ->
      add_gc [([],def_assign,curr_p,next_p,true)] gc


let gen_st_cond_effect_for_th (pt:prog_type)
                              (st:Stm.statement_t)
                              (is_ghost:bool)
                              (th_p:E.tid option) : cond_effect_t list =
  let aux_conds = gen_st_cond_effect_aux is_ghost st in

  (* FIX: Fill the information in mInfo if necessary *)
  let mInfo = {tids=[]; gAddrs=[]; gSets=[]; lAddrs=[]; lSets=[]}
  in
    List.map (fun (cs,es,c,n,_) ->
      let cs_phi = E.conj_list cs in
      let (mods,es_list) = List.fold_left (fun (ts,es) (t,e) ->
                             let (t_res, e_res) =
                               match th_p with
                               | None   -> construct_stm_term_eq mInfo pt t None e
                               | Some _ -> construct_stm_term_eq_as_array mInfo pt t th_p e in
                             (t_res@ts, e_res::es)
                           ) ([],[]) es in
      let es_phi = E.conj_list (
                     match pt with
                     | Num  -> es_list
                     | Heap -> begin
                               if (List.mem (E.MemT E.heap) mods || is_ghost) then
                                 es_list
                               else
                                 (E.eq_mem (E.prime_mem E.heap) E.heap)::es_list
                               end)
      in
        if (c = n) && not(is_ghost) then
          (cs_phi, E.True, c, n)
        else
          (cs_phi, es_phi, c, n)
    ) aux_conds



let gen_st_cond_effect (pt:prog_type)
                       (st:Stm.statement_t)
                       (is_ghost:bool): cond_effect_t list =
  gen_st_cond_effect_for_th pt st is_ghost None



let gen_st_cond_effect_as_array (pt:prog_type)
                                (st:Stm.statement_t)
                                (is_ghost:bool)
                                (th_p:E.tid option) : cond_effect_t list =
  gen_st_cond_effect_for_th pt st is_ghost th_p
