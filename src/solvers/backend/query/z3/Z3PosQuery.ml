open LeapLib
open Printf

module PE = PosExpression
module GM = GenericModel

(* Configuration *)
let pc_prime_name : string = Conf.pc_name ^ "_prime"
let loc_str       : string = "loc_"


(* Program lines *)
let prog_lines : int ref = ref 0


(* Sort names *)
let bool_s : string = "Bool"
let thid_s : string = "Tid"
let loc_s  : string = "Loc"
let int_s  : string = "Int"


(* Program lines manipulation *)
let set_prog_lines (n:int) : unit =
  prog_lines := n


(* Information storage *)
let sort_map : GM.sort_map_t = GM.new_sort_map()


let linenum_to_str (i:int) : string =
  string_of_int i


let pred_variable_to_str (v:string) : string =
  let _ = GM.sm_decl_const sort_map v bool_s
  in
    Printf.sprintf "(declare-const %s %s)\n" v bool_s


let rec variable_to_str (v:PE.V.t) : string =
  let pr_str = if PE.V.is_primed v then "_prime" else "" in
  let th_str = match PE.V.parameter v with
               | PE.V.Shared -> ""
               | PE.V.Local t -> PE.V.to_str t in
  let p_str = match PE.V.scope v with
              | PE.V.GlobalScope -> ""
              | PE.V.Scope proc -> proc ^ "_"
  in
    sprintf "%s%s%s%s" p_str (PE.V.id v) th_str pr_str


and tid_to_str (t:PE.tid) : string =
  match t with
    PE.VarTh v      -> variable_to_str v
  | PE.NoTid       -> "NoTid"
  | PE.CellLockId v -> variable_to_str v ^ "_lockid"


let thid_variable_to_str (th:PE.tid) : string =
  let t_str = tid_to_str th in
  let _ = GM.sm_decl_const sort_map t_str thid_s in
  let tid_decl = Printf.sprintf "(declare-const %s %s)\n" t_str thid_s in
  let tid_range = Printf.sprintf "(assert (in_pos_range %s))\n" t_str
  in
    tid_decl ^ tid_range


let pos_to_str (bpc:(int * PE.V.shared_or_local * bool)) : string =
  let (i, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else Conf.pc_name in
  let th_str = match th with
               | PE.V.Shared -> ""
               | PE.V.Local t -> PE.V.to_str t
  in
    sprintf "(= (select %s %s) %s)" pc_str th_str (linenum_to_str i)


let posrange_to_str (bpc:(int * int * PE.V.shared_or_local * bool)) : string =
  let (i, j, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else Conf.pc_name in
  let th_str = match th with
               | PE.V.Shared -> ""
               | PE.V.Local t -> PE.V.to_str t
  in
    sprintf "(and (<= %s (select %s %s)) (<= (select %s %s) %s))"
      (linenum_to_str i) pc_str th_str pc_str th_str (linenum_to_str j)


let posupd_to_str (pc:(int * PE.tid)) : string =
  let (i, th) = pc
  in
    sprintf "(= %s (store %s %s %s))" pc_prime_name Conf.pc_name
                                      (tid_to_str th)
                                      (linenum_to_str i)


let rec expr_to_str (expr:PE.expression) : string =
  let tostr = expr_to_str in
    match expr with
    | PE.Eq(x,y)         ->" (= " ^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ ")"
    | PE.InEq(x,y)       ->" (not (= "^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ "))"
    | PE.Pred p          -> " " ^ p ^ " "
    | PE.PC (i,th,pr)    -> " " ^ pos_to_str (i,th,pr) ^ " "
    | PE.PCRange (i,j,th,pr) -> " " ^ posrange_to_str (i,j,th,pr) ^ " "
    | PE.PCUpdate (i,th) -> " " ^ posupd_to_str (i,th) ^ " "
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
  let set_logic_str = "(set-logic QF_AUFLIA)\n" in
  let thid_decl_str = "(declare-sort " ^thid_s^ ")\n" in
  let loc_decl_str  = sprintf "(define-sort " ^loc_s^ " () " ^int_s^ ")\n" in
  let _             = GM.sm_decl_fun sort_map Conf.pc_name [thid_s] [loc_s] in
  let _             = GM.sm_decl_fun sort_map pc_prime_name [thid_s] [loc_s] in
  let pc_str        = ("(declare-const " ^Conf.pc_name^ " (Array " ^thid_s^ " "
                          ^loc_s^ "))\n") in
  let pc_prime_str  = ("(declare-const " ^pc_prime_name^ " (Array " ^thid_s^
                      " " ^loc_s^ "))\n") in
  let range_func    = sprintf "(define-fun in_pos_range ((t %s)) %s\n\
                                 (and (<= 1 (select pc t))\n\
                                      (<= (select pc t) %i)\n\
                                      (<= 1 (select pc_prime t))\n\
                                      (<= (select pc_prime t) %i))\n\
                               )\n" thid_s bool_s !prog_lines !prog_lines in
  let voc_str       = List.fold_left (fun s v ->
                        s ^ (thid_variable_to_str v)
                      ) "" voc in
  let pred_str      = List.fold_left (fun s v ->
                        s ^ (pred_variable_to_str v)
                      ) "" preds in
  let formula_str   = "(assert " ^ (expr_to_str expr) ^ ")\n(check-sat)\n"
  in
    set_logic_str ^ thid_decl_str ^ loc_decl_str ^ pc_str ^ pc_prime_str ^
    range_func ^ voc_str ^ pred_str ^ formula_str


let get_sort_map () : GM.sort_map_t =
  GM.copy_sort_map sort_map
