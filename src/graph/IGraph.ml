
module Expr = Expression

(* Type rename *)
(*type Tag.f_tag = Tag.f_tag*)

type mode_t = Sequential | Concurrent

type case_tbl_t = (Expr.pc_t * Premise.t, Tag.f_tag list * Tactics.proof_plan) Hashtbl.t

type rule_t = mode_t         *  (* Sequential or Concurrent mode *)
              Tag.f_tag list *  (* List of premises              *)
              Tag.f_tag      *  (* Invariant                     *)
              case_tbl_t     *  (* Special cases                 *)
              Tactics.proof_plan         (* General tactics               *)

type t = rule_t list
            
exception Duplicated_special_case

let empty_igraph (unit) : t =
  []


let new_igraph (rs:rule_t list) : t =
  rs


let add_rule (ig:t) (r:rule_t) : t =
  r :: ig


let new_rule (mode:mode_t)
             (supList:Tag.f_tag list)
             (inv:Tag.f_tag)
             (cases:(Expr.pc_t       *
                     Premise.t list  *
                     Tag.f_tag list  *
                     Tactics.proof_plan) list)
             (tacs:Tactics.proof_plan) : rule_t =
  let tbl = Hashtbl.create 10 in
  let _ = List.iter (fun (pc,prems,tags,ts) ->
            List.iter (fun prem ->
              if Hashtbl.mem tbl (pc, prem) then
                begin
                  Interface.Err.msg "Special case already defined" "";
                  raise(Duplicated_special_case)
                end
              else
                Hashtbl.add tbl (pc, prem) (tags, ts)
            ) prems
          ) cases
  in
    (mode, supList, inv, tbl, tacs)



let graph_info (grp:t)
                  : (mode_t         *
                     Tag.f_tag list *
                     Tag.f_tag      *
                     case_tbl_t     *
                     Tactics.proof_plan ) list =
  grp


let graph_tags (grp:t) : Tag.f_tag list =
  let tags = List.fold_left (fun set (_,sup,inv,cases,_) ->
               let set' = List.fold_left (fun s t ->
                            Tag.TagSet.add t s
                          ) set sup in
               let set'' = Tag.TagSet.add inv set' in
               let set_final = Hashtbl.fold (fun _ (ts,_) s ->
                                 List.fold_left (fun s' t ->
                                   Tag.TagSet.add t s'
                                 ) s ts
                               ) cases set''
               in
                 Tag.TagSet.union set set_final
             ) Tag.TagSet.empty grp
  in
    Tag.TagSet.elements tags


let empty_case_tbl () : case_tbl_t =
  Hashtbl.create 1


let num_of_cases (cases:case_tbl_t) : int =
  Hashtbl.length cases


let lookup_case (cases:case_tbl_t)
                (line:Expr.pc_t)
                (prem:Premise.t)
                  : (Tag.f_tag list * Tactics.proof_plan) option =
  try
    Some (Hashtbl.find cases (line,prem))
  with _ -> None
