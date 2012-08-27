
module Expr = Expression

(* Type rename *)
(*type Tag.f_tag = Tag.f_tag*)

type premise_t = Normal | Extra

type case_tbl_t = 
  (Expr.pc_t * premise_t, Tag.f_tag list * Tactics.t) Hashtbl.t

type rule_t = Tag.f_tag list *    (* List of premises *)
              Tag.f_tag      *    (* Invariant        *)
              case_tbl_t *    (* Special cases    *)
              Tactics.t  (* General tactics  *)

type iGraph_t = rule_t list
            
exception Duplicated_special_case

let empty_igraph (unit) : iGraph_t =
  []


let new_igraph (rs:rule_t list) : iGraph_t =
  rs


let add_rule (ig:iGraph_t) (r:rule_t) : iGraph_t =
  r :: ig


let new_rule (supList:Tag.f_tag list)
             (inv:Tag.f_tag)
             (cases:(Expr.pc_t  *
                     premise_t list *
                     Tag.f_tag list *
                     Tactics.t) list)
             (tacs:Tactics.t) : rule_t =
  let tbl = Hashtbl.create 10 in
  let _ = List.iter (fun (pc,prems,tags,ts) ->
            List.iter (fun prem ->
              if Hashtbl.mem tbl (pc, prem) then
                begin
                  Interface.Err.msg "Special case already defined" "";
                  raise Duplicated_special_case
                end
              else
                Hashtbl.add tbl (pc, prem) (tags, ts)
            ) prems
          ) cases
  in
    (supList, inv, tbl, tacs)


let graph_info (grp:iGraph_t)
                  : (Tag.f_tag list     *
                     Tag.f_tag          *
                     case_tbl_t     *
                     Tactics.t ) list =
  grp


let graph_tags (grp:iGraph_t) : Tag.f_tag list =
  let tags = List.fold_left (fun set (sup,inv,cases,_) ->
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
