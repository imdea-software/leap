
module Expr = Expression

exception Duplicated_special_case

type case_tbl_t = (Expr.pc_t, Tag.f_tag list) Hashtbl.t

type rule_t = Tag.f_tag  *  (* Invariant                     *)
              case_tbl_t    (* Special cases                 *)

type case_t = Expr.pc_t * Tag.f_tag list

type t = (Tag.f_tag, case_tbl_t) Hashtbl.t


let empty_axioms () : t =
  Hashtbl.create 0


let new_axioms (rs:rule_t list) : t =
  let tbl = Hashtbl.create (List.length rs) in
  List.iter (fun (inv, cases) ->
    Hashtbl.add tbl inv cases
  ) rs;
  tbl


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


let get_axioms (i:Tag.f_tag) (pc:Expr.pc_t) : Tag.f_tag list =
  []

