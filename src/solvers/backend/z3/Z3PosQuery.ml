open LeapLib
open Printf

module Pexpr = PosExpression
module GM = GenericModel

(* Configuration *)
let pc_name       : string = "pc"
let pc_prime_name : string = pc_name ^ "_prime"
let loc_str       : string = "loc_"


(* Program lines *)
let prog_lines : int ref = ref 0


(* Sort names *)
let bool_s : string = "Bool"
let thid_s : string = "Thid"
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


let rec variable_to_str (v:Pexpr.variable) : string =
  let (id, pr, th, p) = v in
  let pr_str = if pr then "_prime" else "" in
  let th_str = Option.map_default tid_to_str "" th in
  let p_str = Option.map_default (fun n -> sprintf "%s_" n) "" p
  in
    sprintf "%s%s%s%s" p_str id th_str pr_str


and tid_to_str (t:Pexpr.tid) : string =
  match t with
    Pexpr.VarTh v      -> variable_to_str v
  | Pexpr.NoThid       -> "NoThid"
  | Pexpr.CellLockId v -> variable_to_str v ^ "_lockid"


let thid_variable_to_str (th:Pexpr.tid) : string =
  let t_str = tid_to_str th in
  let _ = GM.sm_decl_const sort_map t_str thid_s in
  let tid_decl = Printf.sprintf "(declare-const %s %s)\n" t_str thid_s in
  let tid_range = Printf.sprintf "(assert (in_pos_range %s))\n" t_str
  in
    tid_decl ^ tid_range


let pos_to_str (bpc:(int * Pexpr.tid option * bool)) : string =
  let (i, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else pc_name
  in
    sprintf "(= (select %s %s) %s)" pc_str
        (Option.map_default tid_to_str "" th)
        (linenum_to_str i)


let posrange_to_str (bpc:(int * int * Pexpr.tid option * bool)) : string =
  let (i, j, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else pc_name in
  let th_str = Option.map_default tid_to_str "" th
  in
    sprintf "(and (<= %s (select %s %s)) (<= (select %s %s) %s))"
      (linenum_to_str i) pc_str th_str pc_str th_str (linenum_to_str j)


let posupd_to_str (pc:(int * Pexpr.tid)) : string =
  let (i, th) = pc
  in
    sprintf "(= %s (store %s %s %s))" pc_prime_name pc_name
                                      (tid_to_str th)
                                      (linenum_to_str i)


let rec expr_to_str (expr:Pexpr.expression) : string =
  let tostr = expr_to_str in
    match expr with
    | Pexpr.Eq(x,y)         ->" (= " ^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ ")"
    | Pexpr.InEq(x,y)       ->" (not (= "^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ "))"
    | Pexpr.Pred p          -> " " ^ p ^ " "
    | Pexpr.PC (i,th,pr)    -> " " ^ pos_to_str (i,th,pr) ^ " "
    | Pexpr.PCRange (i,j,th,pr) -> " " ^ posrange_to_str (i,j,th,pr) ^ " "
    | Pexpr.PCUpdate (i,th) -> " " ^ posupd_to_str (i,th) ^ " "
    | Pexpr.True            -> " true "
    | Pexpr.False           -> " false "
    | Pexpr.And(a,b)        -> " (and " ^ (tostr a) ^ (tostr b) ^ ")"
    | Pexpr.Or(a,b)         -> " (or "   ^ (tostr a) ^ (tostr b) ^ ")"
    | Pexpr.Not(a)          -> " (not " ^ (tostr a) ^ ")"
    | Pexpr.Implies(a,b)    -> " (=> "   ^ (tostr a) ^ (tostr b) ^ ")"
    | Pexpr.Iff(a,b)        -> " (= "  ^ (tostr a) ^ (tostr b) ^ ")"



let pos_expression_to_str (expr:Pexpr.expression) : string =
  let _             = GM.clear_sort_map sort_map in
  let voc           = Pexpr.voc expr in
  let preds         = Pexpr.all_preds expr in
  let set_logic_str = "(set-logic QF_AUFLIA)\n" in
  let thid_decl_str = "(declare-sort " ^thid_s^ ")\n" in
  let loc_decl_str  = sprintf "(define-sort " ^loc_s^ " () " ^int_s^ ")\n" in
  let _             = GM.sm_decl_fun sort_map pc_name [thid_s] [loc_s] in
  let _             = GM.sm_decl_fun sort_map pc_prime_name [thid_s] [loc_s] in
  let pc_str        = ("(declare-const " ^pc_name^ " (Array " ^thid_s^ " "
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
