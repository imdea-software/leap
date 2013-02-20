open LeapLib
open Printf

module Exp = PosExpression
module GM = GenericModel

(* Configuration *)
let pc_name       : string = "pc"
let pc_prime_name : string = pc_name ^ "_prime"


(* Program lines *)
let prog_lines : int ref = ref 0


(* Sort names *)
let bool_s : string = "bool"
let thid_s : string = "thid"
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


let rec variable_to_str (v:Exp.variable) : string =
  let (id, pr, th, p) = v in
  let pr_str = if pr then "_prime" else "" in
  let th_str = Option.map_default tid_to_str "" th in
  let p_str = Option.map_default (fun n -> sprintf "%s_" n) "" p
  in
    sprintf "%s%s%s%s" p_str id th_str pr_str


and tid_to_str (t:Exp.tid) : string =
  match t with
    Exp.VarTh v      -> variable_to_str v
  | Exp.NoThid       -> "NoThid"
  | Exp.CellLockId v -> variable_to_str v ^ "_lockid"


let thid_variable_to_str (th:Exp.tid) : string =
  let var_id = tid_to_str th in
  let _ = GM.sm_decl_const sort_map var_id thid_s
  in
    sprintf "(define %s::%s)\n" var_id thid_s


let pos_to_str (bpc:(int * Exp.tid option * bool)) : string =
  let (i, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else pc_name
  in
    sprintf "(= (%s %s) %i)" pc_str
        (Option.map_default tid_to_str "" th) i


let posrange_to_str (bpc:(int * int * Exp.tid option * bool)) : string =
  let (i, j, th, pr) = bpc in
  let pc_str = if pr then pc_prime_name else pc_name in
  let th_str = Option.map_default tid_to_str "" th
  in
    sprintf "(and (<= %i (%s %s)) (<= (%s %s) %i))"
        i pc_str th_str pc_str th_str j


let posupd_to_str (pc:(int * Exp.tid)) : string =
  let (i, th) = pc
  in
    sprintf "(= %s (update %s (%s) %i))" pc_prime_name pc_name
                                         (tid_to_str th) i


let rec expr_to_str (expr:Exp.expression) : string =
  let tostr = expr_to_str in
    match expr with
    | Exp.Eq(x,y)         ->" (= " ^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ ")"
    | Exp.InEq(x,y)       ->" (/= "^ (tid_to_str x) ^ " "
                                     ^ (tid_to_str y) ^ ")"
    | Exp.Pred p          -> " " ^ p ^ " "
    | Exp.PC (i,th,pr)    -> " " ^ pos_to_str (i,th,pr) ^ " "
    | Exp.PCUpdate (i,th) -> " " ^ posupd_to_str (i,th) ^ " "
    | Exp.PCRange (i,j,th,pr) -> " " ^ posrange_to_str (i,j,th,pr) ^ " "
    | Exp.True            -> " true "
    | Exp.False           -> " false "
    | Exp.And(a,b)        -> " (and " ^ (tostr a) ^ (tostr b) ^ ")"
    | Exp.Or(a,b)         -> " (or "   ^ (tostr a) ^ (tostr b) ^ ")"
    | Exp.Not(a)          -> " (not " ^ (tostr a) ^ ")"
    | Exp.Implies(a,b)    -> " (=> "   ^ (tostr a) ^ (tostr b) ^ ")"
    | Exp.Iff(a,b)        -> " (= "  ^ (tostr a) ^ (tostr b) ^ ")"



let pos_expression_to_str (expr:Exp.expression) : string =
  let _             = GM.clear_sort_map sort_map in
  let voc           = Exp.voc expr in
  let preds         = Exp.all_preds expr in
  let thid_decl_str = sprintf "(define-type %s)\n" thid_s in
  let loc_decl_str  = sprintf "(define-type %s (subrange 1 %i))\n"
                        loc_s !prog_lines in
  let pc_str        = sprintf "(define pc::(-> %s %s))\n" thid_s loc_s in
  let pc_prime_str  = sprintf "(define pc_prime::(-> %s %s))\n"
                        thid_s loc_s in
  let _             = GM.sm_decl_fun sort_map "pc" [thid_s] [loc_s] in
  let _             = GM.sm_decl_fun sort_map "pc_prime" [thid_s] [loc_s] in
  let voc_str       = List.fold_left (fun s v ->
                        s ^ (thid_variable_to_str v)
                      ) "" voc in
  let pred_str      = List.fold_left (fun s v ->
                        s ^ (pred_variable_to_str v)
                      ) "" preds in
  let formula_str   = "(assert+ " ^ (expr_to_str expr) ^ ")\n(check)\n"
  in
    thid_decl_str ^ loc_decl_str ^ pc_str ^ pc_prime_str ^
    voc_str ^ pred_str ^ formula_str


let get_sort_map () : GM.sort_map_t =
  GM.copy_sort_map sort_map
