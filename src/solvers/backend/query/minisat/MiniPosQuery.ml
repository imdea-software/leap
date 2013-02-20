open LeapLib
open Printf

module Pexpr = PosExpression

let prog_lines : int ref = ref 0
(** The number of lines in the program *)

let set_prog_lines (n:int) : unit =
  prog_lines := n

let pos_expression_to_str (expr:Pexpr.expression) : string =
  let id_count = ref 1 in
  let expr_map : (Pexpr.expression, int) Hashtbl.t = Hashtbl.create 10 in
  let lookup (expr:Pexpr.expression) : int =
    let (neg, e) = match expr with
                     Pexpr.Not t -> (true , t   )
                   | _           -> (false, expr) in
    let es = match e with
               Pexpr.Eq (e1,e2)    -> [Pexpr.Eq(e1,e2); Pexpr.Eq (e2,e1)]
             | Pexpr.InEq (e1, e2) -> [Pexpr.InEq(e1,e2); Pexpr.InEq(e2, e1)]
             | _                   -> [e] in
    let id = if List.exists (Hashtbl.mem expr_map) es then
               (List.fold_left (fun id x ->
                 try
                   Hashtbl.find expr_map x
                 with
                   Not_found -> id
               ) (-1) es)
             else
               let i = !id_count in
               let _ = incr id_count in
               let _ = Hashtbl.add expr_map e i in i in
    let _ = assert (id >=0)
    in
      if neg then -id else id in
  let expand_form = Pexpr.expand_pc_range expr in
  let expr_voc = Pexpr.voc expr in
  (* All threads are at some location *)
  let some_pos_list = ref [] in
  let _ = for i=1 to !prog_lines do
            List.iter (fun t ->
              some_pos_list := Pexpr.PC (i,Some t,false) :: !some_pos_list
            ) expr_voc
          done in
  let some_pos = Pexpr.disj_list !some_pos_list in
  (* All threads are at an unique location *)
  let unique_pos_list = ref [] in
  let _ = for i=1 to !prog_lines do
            List.iter (fun t ->
              let not_pos = ref [] in
              let not_pos' = ref [] in
              let _ = for j=1 to !prog_lines do
                        if i!=j then
                          begin
                            not_pos := Pexpr.Not(Pexpr.PC(j,Some t,false))
                                          :: !not_pos;
                            not_pos':= Pexpr.Not(Pexpr.PC(j,Some t,true))
                                          :: !not_pos'
                          end
                      done in
              let no_other_pos = Pexpr.conj_list !not_pos in
              let no_other_pos' = Pexpr.conj_list !not_pos' in
              let impl = Pexpr.Implies (Pexpr.PC (i,Some t,false),
                                        no_other_pos) in
              let impl' = Pexpr.Implies (Pexpr.PC (i,Some t,true),
                                         no_other_pos')
              in
                unique_pos_list := impl :: impl' :: !unique_pos_list
            ) expr_voc
          done in
  let unique_pos = Pexpr.conj_list !unique_pos_list in
  (* Compute CNF and translate to SAT *)
  let full_formula = Pexpr.And (some_pos, Pexpr.And(unique_pos, expand_form)) in
  let cnf_form = Pexpr.cnf full_formula in
  let desc_str = sprintf "c SAT description for location reasoning \
                          on formula:\nc %s\n" (Pexpr.expr_to_str full_formula) 
  in
  let _ = print_endline (desc_str) in
  let _ = print_endline (string_of_int (List.length cnf_form)) in
  let expr_str = List.fold_left (fun str xs ->
                   str ^ (String.concat " " $
                            List.map (fun t ->
                              string_of_int (lookup t)
                            ) xs)
                       ^ " 0\n"
                 ) "" cnf_form in
  let header_str = sprintf "p cnf %i %i\n" (Hashtbl.length expr_map)
                                           (List.length cnf_form)

  in
    desc_str ^ header_str ^ expr_str
