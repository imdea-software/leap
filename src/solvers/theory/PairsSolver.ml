open LeapLib

module type CUSTOM_PAIRSSOLVER = sig
  module PairsExp : ExpressionTypes.PAIRSEXP
    
  (* Basic invocations *)
  val check_sat              : PairsExp.formula -> Sat.t
  val check_valid            : PairsExp.formula -> Valid.t
  
  (* Invocations with extra information *)
  val check_valid_plus_info  : PairsExp.formula -> (Valid.t * int)
  
  val check_sat_with_lines   : int -> PairsExp.formula -> Sat.t
  val check_valid_with_lines : int -> PairsExp.formula -> Valid.t
  
  val check_valid_with_lines_plus_info 
                          : int -> PairsExp.formula -> (Valid.t * int)


  (* Counter models management *)
  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
end

module type S = CUSTOM_PAIRSSOLVER
  with module PairsExp = PairsExpression

module Make(Solver : BackendSolverIntf.BACKEND_PAIRS) : S =
struct
  module PairsExp = Solver.Translate.Pairs.Exp
  module GM       = GenericModel

  (* Compute counter model for not valid formulas? *)
  let comp_model : bool ref = ref false

  (* INVOCATIONS *)
  let check_sat (phi : PairsExp.formula) : Sat.t =
    let module Q = (val QueryManager.get_pairs_query Solver.identifier) in
    let module Trans = Solver.Translate.Pairs.Query(Q) in
    Solver.check_sat (Trans.pairs_formula phi)
  
  
  let check_valid (phi : PairsExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat (Formula.Not phi))
  
  
  let check_valid_plus_info (phi : PairsExp.formula) : (Valid.t * int) =
    let _ = Solver.reset_calls () in
    let res = check_valid phi in 
    (res, Solver.calls_count ())
  
  
  let check_sat_with_lines (prog_lines : int) (phi : PairsExp.formula) : Sat.t =
    let module Q = (val QueryManager.get_pairs_query Solver.identifier) in
    let module Trans = Solver.Translate.Pairs.Query(Q) in
    let _ = Trans.set_prog_lines prog_lines in
    let f = Trans.pairs_formula_with_lines phi in
    Solver.check_sat f
  
  
  let check_valid_with_lines (prog_lines : int) (phi : PairsExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat_with_lines prog_lines (Formula.Not phi))
  
  
  let check_valid_with_lines_plus_info (prog_lines : int) (phi : PairsExp.formula) 
    : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid_with_lines prog_lines phi
    in (res, Solver.calls_count ())


  (* Counter model computation functions *)
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
    let module Q = (val QueryManager.get_pairs_query Solver.identifier) in
    let module Trans = Solver.Translate.Pairs.Query(Q) in
    let query_sort_map = Trans.sort_map () in
    let model = Solver.get_model () in
    let sort_map = GM.sm_union query_sort_map (GM.get_aux_sort_map model) in
    let thid_str = search_type_to_str model sort_map GM.tid_s in
    let pc_str   = search_type_to_str model sort_map GM.loc_s in
    let int_str  = search_type_to_str model sort_map GM.int_s in
    let pair_str = search_type_to_str model sort_map GM.pair_s in

    (* Special description for sets *)
    let set_str  = search_sets_to_str model sort_map GM.set_s in
    let setpair_str  = search_sets_to_str model sort_map GM.setpair_s

    in
      "\nThreads:\n" ^ thid_str ^
      "\nProgram counters:\n" ^ pc_str ^
      "\nIntegers:\n" ^ int_str ^
      "\nPairs:\n" ^ pair_str ^
      "\nSets:\n" ^ set_str ^
      "\nSets of pairs:\n" ^ setpair_str


  let print_model () : unit =
    if !comp_model then
      print_endline (model_to_str())
    else
      ()
end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.pairsTbl solverIdent
    with Not_found -> BackendSolvers.defaultPairs () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_PAIRS) in
  (module Make(Sol) : S)
