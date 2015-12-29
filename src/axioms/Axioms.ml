
module Expr = Expression
module GSet = LeapGenericSet

exception Duplicated_special_case
exception Unsupported_axiom of string

type case_tbl_t = (Expr.pc_t, Tag.f_tag list) Hashtbl.t

type rule_t = Tag.f_tag  *  (* Invariant                     *)
              case_tbl_t    (* Special cases                 *)

type case_t = Expr.pc_t * Tag.f_tag list

type t = (Tag.f_tag, case_tbl_t) Hashtbl.t

type axiom_case_t = {premises : (Expr.literal * bool) GSet.t;
                     result: Expr.formula;}
type axiom_info_t = {params: System.var_table_t;
                     cases: axiom_case_t list }
type axiom_tbl_t = (Tag.f_tag, axiom_info_t) Hashtbl.t


let empty_axioms () : t =
  Hashtbl.create 0


let new_axioms (rs:rule_t list) : t =
  let tbl = Hashtbl.create (List.length rs) in
  List.iter (fun (inv, cases) ->
    Hashtbl.add tbl inv cases
  ) rs;
  tbl


let split_formula (phi:Expr.formula) : axiom_case_t list =
  let ax_conj = Formula.to_conj_list phi in
  List.map (fun conj ->
    print_endline ("CONJ: " ^ (Expr.formula_to_str conj));
    match conj with
    | Formula.Literal lit ->
        begin
          { premises = GSet.singleton (lit,false);
            result = Formula.True; }
        end
    | Formula.Implies (ante, conseq) ->
        begin
          print_endline ("ANTE: " ^ (Expr.formula_to_str ante));
          let prems = Formula.to_conj_literals (Formula.nnf ante) in
          print_endline "Done";
          let prem_set = GSet.empty () in
          List.iter (fun p -> GSet.add prem_set (p,false)) prems;
          { premises = prem_set;
            result = conseq; }
        end
    | Formula.And _ ->
        begin
          print_endline ("CONJ: " ^ (Expr.formula_to_str conj));
          let prems = Formula.to_conj_literals (Formula.nnf conj) in
          print_endline "Done";
          let prem_set = GSet.empty () in
          List.iter (fun p -> GSet.add prem_set (p,false)) prems;
          { premises = prem_set;
            result = Formula.True; }
        end
    | _ -> raise (Unsupported_axiom (Expr.formula_to_str phi))
  ) ax_conj


let new_axiom_table (ax_tags:Tag.tag_table) : axiom_tbl_t =
  print_endline ("AXIOM TAG SIZE: " ^ (string_of_int (Tag.tag_table_size ax_tags)));
  let tbl = Hashtbl.create (Tag.tag_table_size ax_tags) in
  Tag.tag_table_iter ax_tags (fun t (t_phi,info) ->
    let cases = split_formula t_phi in
    let ax_info = { params = Tag.info_params info;
                    cases = cases; } in
    Hashtbl.add tbl t ax_info
  );
  tbl


let reset_axiom_table (tbl:axiom_tbl_t) : unit =
  Hashtbl.iter (fun t info ->
    let reseted_cases = List.map (fun c ->
                          let reseted_prems = GSet.empty () in
                          GSet.iter (fun (phi,_) ->
                            GSet.add reseted_prems (phi,false)
                          ) c.premises;
                          {premises = reseted_prems; result = c.result;}
                        ) info.cases in
    Hashtbl.replace tbl t {params=info.params; cases=reseted_cases;}
  ) tbl


let new_rule (inv:Tag.f_tag) (cases:case_t list) : rule_t =
  let tbl = Hashtbl.create 10 in
  let _ = List.iter (fun (pc,tags) ->
            if Hashtbl.mem tbl pc then
              begin
                Interface.Err.msg "Special case already defined" "";
                raise(Duplicated_special_case)
              end
            else
              Hashtbl.add tbl pc tags
          ) cases
  in
    (inv, tbl)


let new_case (pc:Expr.pc_t) (xs:Tag.f_tag list) : case_t =
  (pc,xs)


(* Begin pretty printers *)
let axiom_table_to_str (tbl:axiom_tbl_t) : string =
  Hashtbl.fold (fun t info str ->
    str ^ "Axiom: " ^ (Tag.tag_id t) ^ "\n" ^
    "Parameters: " ^ (String.concat ";" (List.map Expr.V.to_str (System.get_variable_list info.params))) ^ "\n"
  ) tbl ""


(* End pretty printers *)


let lookup (ax:t) (inv:Tag.f_tag) (pc:Expr.pc_t) : Tag.f_tag list =
  try
    Hashtbl.find (Hashtbl.find ax inv) pc
  with _ -> []


  


(* Variable match finder *)
  







let apply_axiom_inst (ax:Expr.formula)
                     (ax_vars:System.var_table_t) 
                     (phi:Expr.formula) : Expr.formula =
  phi


let apply_axioms_inst (axs:(Expr.formula * System.var_table_t) list)
                      (phi:Expr.formula) : Expr.formula =
  List.fold_left (fun psi (ax_phi, ax_vars) ->
    apply_axiom_inst ax_phi ax_vars phi
  ) phi axs
                                



