open LeapLib
open Printf

module PE = PosExpression
module GM = GenericModel

(* Configuration *)
let pc_prime_name : string = Conf.pc_name ^ "_prime"


(* Program lines *)
let prog_lines : int ref = ref 0


(* Sort names *)
let bool_s : string = "bool"
let tid_s : string = "tid"
let loc_s  : string = "loc"


(* Program lines manipulation *)
let set_prog_lines (n:int) : unit =
  prog_lines := n


(* Information storage *)
let sort_map : GM.sort_map_t = GM.new_sort_map()


let pred_variable_to_str (v:string) : string =
  let _ = GM.sm_decl_const sort_map v bool_s
  in
    sprintf "(define %s::%s)\n" v bool_s


let rec variable_to_str (v:PE.V.t) : string =
  let pr_str = if PE.V.is_primed v then "_prime" else "" in
  let th_str = match PE.V.parameter v with
               | PE.V.Shared -> ""
               | PE.V.Local th -> variable_to_str th in
  let p_str = match PE.V.scope v with
              | PE.V.GlobalScope -> ""
              | PE.V.Scope p -> p ^ "_"
  in
    sprintf "%s%s%s%s" p_str (PE.V.id v) th_str pr_str


and tid_to_str (t:PE.tid) : string =
  match t with
    PE.VarTh v      -> variable_to_str v
  | PE.NoTid       -> "NoTid"
  | PE.CellLockId v -> variable_to_str v ^ "_lockid"


let thid_variable_to_str (th:PE.tid) : string =
  let var_id = tid_to_str th in
  let _ = GM.sm_decl_const sort_map var_id tid_s
  in
    sprintf "(define %s::%s)\n" var_id tid_s


let pos_to_str (bpc:(int * PE.V.shared_or_local * bool)) : string =
  let (i, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else Conf.pc_name in
  let th_str = match th with
               | PE.V.Shared -> ""
               | PE.V.Local t -> variable_to_str t
  in
    sprintf "(= (%s %s) %i)" pc_str th_str i


let posrange_to_str (bpc:(int * int * PE.V.shared_or_local * bool)) : string =
  let (i, j, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else Conf.pc_name in
  let th_str = match th with
               | PE.V.Shared -> ""
               | PE.V.Local t -> variable_to_str t
  in
    sprintf "(and (<= %i (%s %s)) (<= (%s %s) %i))"
        i pc_str th_str pc_str th_str j


let posupd_to_str (pc:(int * PE.tid)) : string =
  let (i, th) = pc
  in
    sprintf "(= %s (update %s (%s) %i))" pc_prime_name Conf.pc_name
                                         (tid_to_str th) i


let rec expr_to_str (expr:PE.expression) : string =
  let tostr = expr_to_str in
    match expr with
    | PE.Eq(x,y)         ->" (= " ^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ ")"
    | PE.InEq(x,y)       ->" (/= "^ (tid_to_str x) ^ " "
                                  ^ (tid_to_str y) ^ ")"
    | PE.Pred p          -> " " ^ p ^ " "
    | PE.PC (i,th,pr)    -> " " ^ pos_to_str (i,th,pr) ^ " "
    | PE.PCUpdate (i,th) -> " " ^ posupd_to_str (i,th) ^ " "
    | PE.PCRange (i,j,th,pr) -> " " ^ posrange_to_str (i,j,th,pr) ^ " "
    | PE.True            -> " true "
    | PE.False           -> " false "
    | PE.And(a,b)        -> " (and " ^ (tostr a) ^ (tostr b) ^ ")"
    | PE.Or(a,b)         -> " (or "   ^ (tostr a) ^ (tostr b) ^ ")"
    | PE.Not(a)          -> " (not " ^ (tostr a) ^ ")"
    | PE.Implies(a,b)    -> " (=> "   ^ (tostr a) ^ (tostr b) ^ ")"
    | PE.Iff(a,b)        -> " (= "  ^ (tostr a) ^ (tostr b) ^ ")"



let pos_expression_to_str (expr:PE.expression) : string =
  let _             = GM.clear_sort_map sort_map in
  let voc           = PE.voc expr in
  let preds         = PE.all_preds expr in
  let thid_decl_str = sprintf "(define-type %s)\n" tid_s in
  let loc_decl_str  = sprintf "(define-type %s (subrange 1 %i))\n"
                        loc_s !prog_lines in
  let pc_str        = sprintf "(define pc::(-> %s %s))\n" tid_s loc_s in
  let pc_prime_str  = sprintf "(define pc_prime::(-> %s %s))\n"
                        tid_s loc_s in
  let _             = GM.sm_decl_fun sort_map "pc" [tid_s] [loc_s] in
  let _             = GM.sm_decl_fun sort_map "pc_prime" [tid_s] [loc_s] in
  let voc_str       = List.fold_left (fun s v ->
                        s ^ (thid_variable_to_str v)
                      ) "" voc in
  let pred_str      = List.fold_left (fun s v ->
                        s ^ (pred_variable_to_str v)
                      ) "" preds in
  let formula_str   = "(assert " ^ (expr_to_str expr) ^ ")\n(check)\n"
  in
    thid_decl_str ^
    loc_decl_str ^ pc_str ^ pc_prime_str ^
    voc_str ^ pred_str ^
    formula_str


let get_sort_map () : GM.sort_map_t =
  GM.copy_sort_map sort_map
