
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


open LeapLib

module E = Expression
module F = Formula

(* Types for nodes *)
type node_id_t = string
type box_id_t = string
type node_info_t = {mu:E.formula; box:box_id_t option; }
type node_t = node_id_t * E.formula
type node_table_t = (node_id_t, node_info_t) Hashtbl.t

module NodeIdSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = node_id_t
  end )


(* Types for boxes *)
type box_t = (box_id_t * node_id_t list * E.ThreadSet.elt)
type box_table_t = (box_id_t, NodeIdSet.t * E.ThreadSet.elt) Hashtbl.t


(* Types for edges *)
type trans_t = NoLabel | Label of (int * E.V.t) list
type edge_type_t = Any | Pres
type edge_info_t = (edge_type_t * trans_t)

module EdgeInfoSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = edge_info_t
  end )

type edge_t = node_id_t * node_id_t * edge_info_t
type edge_table_t = ((node_id_t * node_id_t), EdgeInfoSet.t) Hashtbl.t

(* Types for acceptance conditions *)
type accept_triple_t = (node_id_t * node_id_t * edge_type_t)

(* The conditions to be analyzed for a PVD *)
type conditions_t = Initiation | Consecution | Acceptance | Fairness

module AcceptanceSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = accept_triple_t
  end )

type wf_op_t =
  | WFIntSubset
  | WFPairSubset
  | WFAddrSubset
  | WFElemSubset
  | WFTidSubset
  | WFIntLess

type delta_op_t =
  | Preserve
  | Decrement

type acceptance_t = {good : AcceptanceSet.t;
                     bad  : AcceptanceSet.t;
                     delta: (E.term * wf_op_t) list; }

type next_table_t = (node_id_t, NodeIdSet.t) Hashtbl.t
type tau_table_t = (node_id_t * int * E.V.t, NodeIdSet.t) Hashtbl.t

type supp_line_t =
  | All
  | Trans of int
  | TransSpec of int * conditions_t
  | TransNodeSpec of int * node_id_t list * conditions_t list

type tactic_table_t =
  {
    global_tactics : Tactics.proof_plan option;
    local_gral_tactics : (int, Tactics.proof_plan) Hashtbl.t;
    local_spec_tactics : (int * conditions_t, Tactics.proof_plan) Hashtbl.t;
    local_node_tactics : (int * node_id_t * conditions_t, Tactics.proof_plan) Hashtbl.t;
  }
type fact_table_t =
  {
    global_facts : Tag.f_tag list;
    local_gral_facts : (int, Tag.f_tag list) Hashtbl.t;
    local_spec_facts : (int * conditions_t, Tag.f_tag list) Hashtbl.t;
    local_node_facts : (int * node_id_t * conditions_t, Tag.f_tag list) Hashtbl.t;
  }
type support_t =
  {
    tactics : tactic_table_t;
    facts   : fact_table_t;
  }

exception Duplicated_node of node_id_t
exception Undefined_node of node_id_t
exception Undefined_edge of string
exception BadBoxedEdge of edge_t
exception BadBox of box_id_t
exception No_initial
exception Incorrect_ranking_function of string
exception Malformed_PVD_support
exception Unknown_condition_str of string


(* Type for Parametrized Verification Diagrams *)
type t = {
  name       : string;
  nodes      : node_table_t;
  initial    : NodeIdSet.t;
  boxes      : box_table_t;
  next       : next_table_t;
  tau        : tau_table_t;
  edges      : edge_table_t;
  acceptance : acceptance_t list;
  free_voc   : E.ThreadSet.t;
}


(**  Configuration  **)
let initNodeNum = 30
let initEdgeNum = 50


(**  Cache  **)
let cached_nodes : NodeIdSet.t option ref = ref None


(**  Selectors  **)
let box_param (nTbl:node_table_t)
              (bTbl:box_table_t)
              (n:node_id_t) : E.ThreadSet.elt option =
  try
    match (Hashtbl.find nTbl n).box with
    | None -> None
    | Some b_id -> Some (snd (Hashtbl.find bTbl b_id))
  with Not_found -> None


(**  Pretty printers  **)
let kind_to_str (k:edge_type_t) : string =
  match k with
  | Any -> "any"
  | Pres -> "pres"


let wf_op_to_str (op:wf_op_t) : string =
  match op with
  | WFIntSubset  -> "subset_op"
  | WFPairSubset -> "pairsubset_op"
  | WFAddrSubset -> "addrsubset_op"
  | WFElemSubset -> "elemsubset_op"
  | WFTidSubset  -> "tidsubset_op"
  | WFIntLess    -> "less_op"


let node_id_to_str (id:node_id_t) : string =
  id


let box_id_to_str (id:box_id_t) : string =
  id


let to_str (pvd:t) : string =
  let nodes_str = String.concat ","
                    (Hashtbl.fold (fun n info xs ->
                       let info_str =
                         match info.mu with
                         | F.True -> ""
                         | phi -> "{" ^(E.formula_to_str phi)^ "}" in
                      ((node_id_to_str n)^info_str)::xs
                     ) pvd.nodes []) in
  let boxes_str = String.concat ","
                    (Hashtbl.fold (fun b_id (nSet,param) xs ->
                       let param_str = E.tid_to_str param in
                       let nSet_str = String.concat ","
                                        (NodeIdSet.fold (fun n ys ->
                                           (node_id_to_str n)::ys
                                         ) nSet []) in
                       ("{" ^(box_id_to_str b_id)^ "[" ^param_str^ "]:" ^nSet_str^"}")::xs
                     ) pvd.boxes []) in
  let initial_str = String.concat ","
                      (NodeIdSet.fold (fun n set ->
                         (node_id_to_str n) :: set
                       ) pvd.initial [] ) in
  let edges_str = Hashtbl.fold (fun (n1,n2) infoSet str ->
                    let n1_str = node_id_to_str n1 in
                    let n2_str = node_id_to_str n2 in
                    (EdgeInfoSet.fold (fun (kind,trans) str ->
                      let trans_str =
                        match trans with
                        | NoLabel -> ""
                        | Label ts -> "{" ^(String.concat ","
                                              (List.map(fun (i,t) ->
                                                 (string_of_int i) ^"[" ^E.V.to_str t^ "]"
                                               ) ts))^ "}" in
                      let e_str = n1_str ^ " -" ^trans_str^ "-> " ^n2_str in
                      match kind with
                      | Any -> "\n  " ^ e_str ^ ";" ^ str
                      | Pres -> "\n  [" ^ e_str ^ "];" ^ str
                    ) infoSet "") ^ str
                  ) pvd.edges "" in
  let acceptance_str = List.fold_left (fun str acc ->
                         let map s = AcceptanceSet.fold (fun (n1,n2,k) xs ->
                                       ("(" ^(node_id_to_str n1)^ "," ^
                                             (node_id_to_str n2)^ "," ^
                                             (kind_to_str k)^ ")") :: xs
                                     ) s [] in
                         let good_list_str = String.concat "," (map acc.good) in
                         let bad_list_str = String.concat "," (map acc.bad) in
                         let delta_list_str = String.concat ";"
                                (List.map (fun (t,op) ->
                                  "(" ^(E.term_to_str t)^ "," ^(wf_op_to_str op)^ ")"
                                ) acc.delta) in
                         "\n  << Bad : {" ^bad_list_str^ "};\n" ^
                           "     Good: {" ^good_list_str^ "};\n" ^
                           "     [" ^delta_list_str^ "] >>" ^ str
                       ) "" pvd.acceptance in
  ("Diagram[" ^pvd.name^ "]\n\n" ^
   "Nodes: " ^nodes_str^ "\n\n" ^
   "Boxes: " ^boxes_str^ "\n\n" ^
   "Initial: " ^initial_str^ "\n\n" ^
   "Edges: " ^edges_str^ "\n\n" ^
   "Acceptance: " ^acceptance_str^ "\n")
  

let cond_to_str (c:conditions_t) : string =
 match c with
 | Initiation -> "initiation"
 | Consecution -> "consecution"
 | Acceptance -> "acceptance"
 | Fairness -> "fairness" 


let str_to_cond (str:string) : conditions_t =
  match str with
  | "initiation" -> Initiation
  | "consecution" -> Consecution
  | "acceptance" -> Acceptance
  | "fairness" -> Fairness
  | s -> raise(Unknown_condition_str s)


(**  Auxiliary constructor functions  **)

let is_defined (nTbl:node_table_t) (n:node_id_t) : unit =
  if not (Hashtbl.mem nTbl n) then
    raise(Undefined_node n)


let well_defined_acceptance_edge (eTbl:edge_table_t) (e:edge_t) : unit =
  let (n1,n2,(kind,_)) = e in
  let error () = begin
                   Interface.Err.msg "Undefined acceptance edge" $
                   Printf.sprintf "Edge (%s,%s,%s) is used in the acceptance \
                                   conditions, but it was not defined as a \
                                   diagram edge."
                     (node_id_to_str n1) (node_id_to_str n2) (kind_to_str kind);
                   let (n1,n2,(k,_)) = e in
                   let edge_str = "(" ^ (node_id_to_str n1) ^ "," ^
                                        (node_id_to_str n2) ^ "," ^
                                        (kind_to_str k) ^ ")" in
                   raise(Undefined_edge edge_str)
                 end in
  try
    let infoSet = Hashtbl.find eTbl (n1,n2) in
    if not (EdgeInfoSet.exists (fun (k,_) -> k = kind ) infoSet) then
      error()
  with Not_found -> error()


let well_defined_boxed_edge (nTbl:node_table_t) (e:edge_t) : unit =
  let (n1,n2,(kind,_)) = e in
  match kind with
  | Any -> ()
  | Pres -> try
              let b1 = (Hashtbl.find nTbl n1).box in
              let b2 = (Hashtbl.find nTbl n2).box in
              match (b1,b2) with
              | (None,_)
              | (_,None) ->
                  begin
                    Interface.Err.msg "Incorrect edge" $
                      Printf.sprintf "Edge connecting nodes %s and %s is marked \
                                      to preserve box parameter, but one node does \
                                      not belong to a box."
                              (node_id_to_str n1) (node_id_to_str n2);
                    raise(BadBoxedEdge e)
                  end
              | (Some b1, Some b2) ->
                  if b1 <> b2 then
                    begin
                      Interface.Err.msg "Incorrect edge" $
                        Printf.sprintf "Edge connecting nodes %s and %s is marked \
                                        to preserve box parameter, but they do not \
                                        belong to the same box."
                                (node_id_to_str n1) (node_id_to_str n2);
                      raise(BadBoxedEdge e)
                    end
            with Not_found ->
                begin
                  Interface.Err.msg "Incorrect edge" $
                    Printf.sprintf "Edge connecting nodes %s and %s is marked \
                                    to preserve box parameter, but one of them \
                                    is not defined."
                            (node_id_to_str n1) (node_id_to_str n2);
                  raise(BadBoxedEdge e)
                end


let build_initial (nTbl:node_table_t) (is:node_id_t list) : NodeIdSet.t =
  match is with
  | [] -> begin
            Interface.Err.msg "No initial nodes" $
              "No initial node was declared";
            raise(No_initial)
          end
  | _ -> List.fold_left (fun set n_id ->
           is_defined nTbl n_id;
           NodeIdSet.add n_id set
         ) NodeIdSet.empty is


let check_and_define_nodes (nodes:node_t list)
                           (boxes:box_t list)
    : (node_table_t * box_table_t * E.ThreadSet.t) =
  let free_voc = ref E.ThreadSet.empty in
  let nTbl = Hashtbl.create 40 in
  let bTbl = Hashtbl.create 40 in

  (* Preliminary table of nodes *)
  List.iter (fun (n_id,n_formula) ->
    if Hashtbl.mem nTbl n_id then
      begin
        Interface.Err.msg "Already defined node" $
          Printf.sprintf "Another node with id %s has already been defined."
            (node_id_to_str n_id);
        raise(Duplicated_node n_id)
      end
    else
      Hashtbl.add nTbl n_id {mu=n_formula; box=None;}
  ) nodes;

  (* Table of boxes *)
  List.iter (fun (box_id, ns, param) ->
    let nSet = List.fold_left (fun set n_id ->
                 try
                   let old_info = Hashtbl.find nTbl n_id in
                   match old_info.box with
                   | None -> Hashtbl.replace nTbl n_id {mu=old_info.mu;
                                                        box=Some box_id;};
                             NodeIdSet.add n_id set
                   | Some old_b ->
                       begin
                         Interface.Err.msg "Node already parametrized by box" $
                           Printf.sprintf "The node with identifier %s is trying to be \
                                           associated to box %s, while it has already \
                                           been associated to box %s"
                                             (node_id_to_str n_id)
                                             (box_id_to_str box_id)
                                             (box_id_to_str old_b);
                         raise(BadBox box_id)
                       end
                 with Not_found ->
                   begin
                     Interface.Err.msg "Box defined over unrecognized node" $
                       Printf.sprintf "A box is defined over node %s, which has not \
                                       been declared before."
                                         (node_id_to_str n_id);
                     raise(Undefined_node n_id)
                   end
               ) NodeIdSet.empty ns in
    Hashtbl.add bTbl box_id (nSet, param)
  ) boxes;


  (* Compute the free vocabulary of nodes *)
  Hashtbl.iter (fun n_id n_info ->
    let mu_voc = E.voc n_info.mu in
    let free_mu_voc = match box_param nTbl bTbl n_id with
                      | None -> mu_voc
                      | Some t -> E.ThreadSet.remove t mu_voc in
    free_voc := E.ThreadSet.union !free_voc free_mu_voc;
  ) nTbl;


  (nTbl, bTbl, !free_voc)


let check_and_define_edges (nTbl:node_table_t)
                           (bTbl:box_table_t)
                           (es:edge_t list)
    : (edge_table_t * next_table_t * tau_table_t * E.ThreadSet.t) =
  let eTbl = Hashtbl.create initEdgeNum in
  let nextTbl = Hashtbl.create initNodeNum in
  let tTbl = Hashtbl.create initEdgeNum in
  let add_next_node (n1:node_id_t) (n2:node_id_t) : unit =
    try
      let old_next = Hashtbl.find nextTbl n1 in
      Hashtbl.replace nextTbl n1 (NodeIdSet.add n2 old_next)
    with Not_found -> Hashtbl.add nextTbl n1 (NodeIdSet.singleton n2)
  in
  let add_tau (n1:node_id_t) (n2:node_id_t) (trans:trans_t) : unit =
    match trans with
    | NoLabel -> ()
    | Label ts -> List.iter (fun (i,t) ->
                    try
                      let old_dest = Hashtbl.find tTbl (n1,i,t) in
                      Hashtbl.replace tTbl (n1,i,t) (NodeIdSet.add n2 old_dest)
                    with Not_found -> Hashtbl.add tTbl (n1,i,t)
                                                       (NodeIdSet.singleton n2)

                  ) ts
  in
  let check_transition_param (n:node_id_t) (trans:trans_t) : E.ThreadSet.t =
    let trans_voc = match trans with
                    | NoLabel -> E.ThreadSet.empty
                    | Label ts -> List.fold_left (fun set (_,t) ->
                                    E.ThreadSet.add (E.VarTh t) set
                                  ) E.ThreadSet.empty ts in
    match box_param nTbl bTbl n with
    | None -> trans_voc
    | Some t -> E.ThreadSet.remove t trans_voc
  in
  let free_voc = ref E.ThreadSet.empty in
  List.iter (fun (n1,n2,(kind,trans) as e) ->
    is_defined nTbl n1;
    is_defined nTbl n2;
    well_defined_boxed_edge nTbl e;
    free_voc := E.ThreadSet.union (check_transition_param n1 trans) !free_voc;
    let _ = try
              let old_e_info = Hashtbl.find eTbl (n1,n2) in
              Hashtbl.replace eTbl (n1,n2) (EdgeInfoSet.add (kind,trans) old_e_info)
            with Not_found -> Hashtbl.add eTbl (n1,n2) (EdgeInfoSet.singleton (kind,trans)) in
    add_next_node n1 n2;
    add_tau n1 n2 trans;
  ) es;
  (eTbl, nextTbl, tTbl, !free_voc)


let check_acceptance (nTbl:node_table_t)
                     (eTbl:edge_table_t)
                     (acs:(accept_triple_t list * accept_triple_t list * (E.term * wf_op_t) list) list)
        : acceptance_t list =
  let fill_set xs = List.fold_left (fun set info ->
                      AcceptanceSet.add info set
                    ) AcceptanceSet.empty xs in
  let validate_delta ((t,op):E.term * wf_op_t) : unit =
    match (E.term_sort t, op) with
    | (E.SetInt, WFIntSubset)
    | (E.SetPair, WFPairSubset)
    | (E.Set, WFAddrSubset)
    | (E.SetElem, WFElemSubset)
    | (E.SetTh, WFTidSubset)
    | (E.Int, WFIntLess) -> ()
    | _ -> begin
             Interface.Err.msg "Unsupported ranking function" $
               Printf.sprintf "Term %s was provided as ranking function, \
                               but is not supported with operation %s."
                  (E.term_to_str t) (wf_op_to_str op);
             raise(Incorrect_ranking_function(E.term_to_str t))
           end in
  List.map (fun (bads, goods, ds) ->
    List.iter validate_delta ds;


    List.iter (fun (n1,n2,kind) ->
      is_defined nTbl n1;
      is_defined nTbl n2;
      well_defined_acceptance_edge eTbl (n1,n2, (kind,NoLabel));
      well_defined_boxed_edge nTbl (n1,n2,(kind,NoLabel));
    ) (bads @ goods);
    let goodSet = fill_set goods in
    let badSet = fill_set bads in
    {
      good = goodSet;
      bad = badSet;
      delta = ds;
    }
  ) acs


(**  Constructors  **)

let new_pvd (name:string)
            (ns:node_t list)
            (bs:box_t list)
            (is:node_id_t list)
            (es:edge_t list)
            (acs:(accept_triple_t list * accept_triple_t list * (E.term * wf_op_t) list) list) : t =
  let (nTbl,bTbl,free_voc_nodes) = check_and_define_nodes ns bs in
  let iSet = build_initial nTbl is in
  (* We implicitly add self-loops *)
  let es' = Hashtbl.fold (fun n info xs ->
              match info.box with
              | None -> (n,n,(Any,NoLabel)) :: xs
              | Some _ -> (n,n,(Pres,NoLabel)) :: xs
            ) nTbl es in
  let (eTbl, nextTbl, tTbl, free_voc_edges) = check_and_define_edges nTbl bTbl es' in
  let accept_list = check_acceptance nTbl eTbl acs in
  {
    name = name;
    nodes = nTbl;
    initial = iSet;
    boxes = bTbl;
    next = nextTbl;
    tau = tTbl;
    edges = eTbl;
    acceptance = accept_list;
    free_voc = E.ThreadSet.union free_voc_nodes free_voc_edges;
  }


let def_cond_list : conditions_t list =
  [Initiation; Consecution; Acceptance; Fairness]


let initial (pvd:t) : NodeIdSet.t =
  pvd.initial


let nodes (pvd:t) : NodeIdSet.t =
  match !cached_nodes with
  | Some n -> n
  | None -> begin
              let nSet = Hashtbl.fold (fun n _ set ->
                           NodeIdSet.add n set
                         ) pvd.nodes NodeIdSet.empty in
              cached_nodes := Some nSet;
              nSet
            end


let node_mu (pvd:t) (n:node_id_t) : E.formula =
  (Hashtbl.find pvd.nodes n).mu


let node_box (pvd:t) (n:node_id_t) : box_id_t option =
  (Hashtbl.find pvd.nodes n).box


let next (pvd:t) (n:node_id_t) : NodeIdSet.t =
  Hashtbl.find pvd.next n


let box_param (pvd:t) (b:box_id_t) : E.ThreadSet.elt =
  snd (Hashtbl.find pvd.boxes b)


let edges (pvd:t) (n1:node_id_t) (n2:node_id_t) : EdgeInfoSet.t =
  try
    Hashtbl.find pvd.edges (n1,n2)
  with Not_found -> EdgeInfoSet.empty


let edge_list (pvd:t) : (node_id_t * node_id_t * EdgeInfoSet.t) list =
  Hashtbl.fold (fun (n1,n2) info xs ->
    (n1,n2,info) :: xs
  ) pvd.edges []


let successor (pvd:t) (n:node_id_t) (line:int) (t:E.V.t) : NodeIdSet.t =
  try
    Hashtbl.find pvd.tau (n,line,t)
  with Not_found -> NodeIdSet.empty


let cond_next (pvd:t) (cond:edge_type_t) (n:node_id_t) : NodeIdSet.t =
  NodeIdSet.fold (fun n' set ->
    let e_info_set = edges pvd n n' in
    if EdgeInfoSet.exists (fun (k,_) -> k = cond) e_info_set then
      NodeIdSet.add n' set
    else
      set
  ) (next pvd n) NodeIdSet.empty


let acceptance_list (pvd:t) : acceptance_t list =
  pvd.acceptance


let beta (pvd:t) ((n1,n2,kind):(node_id_t * node_id_t * edge_type_t)) : E.formula =
  try
    let edgeSet = Hashtbl.find pvd.edges (n1,n2) in
    match (node_box pvd n1, node_box pvd n2) with
    | (Some b1, Some b2) ->
        if b1 = b2 && kind = Pres && EdgeInfoSet.exists (fun (k,_) -> k = kind) edgeSet then
        let t = snd (Hashtbl.find pvd.boxes b1) in
          F.atom_to_formula (E.Eq (E.prime_term (E.TidT t), E.TidT t))
        else
          F.True
    | _ -> F.True
  with Not_found -> F.True


let ranking_function (ante:E.formula)
                     (accept:acceptance_t)
                     (e:(node_id_t * node_id_t * edge_type_t)) : E.formula =
  let form = F.atom_to_formula in

  let build_dec (op:wf_op_t) (t1:E.term) (t2:E.term) : E.formula =
    match (op,t1,t2) with
    | (WFIntSubset, E.SetIntT s1, E.SetIntT s2) -> F.And(form (E.InEq (t2,t1)),
                                                         form (E.SubsetEqInt (s2,s1)))
    | (WFPairSubset, E.SetPairT s1, E.SetPairT s2) -> F.And(form (E.InEq (t2,t1)),
                                                            form (E.SubsetEqPair (s2,s1)))

    | (WFAddrSubset, E.SetT s1, E.SetT s2) -> F.And(form (E.InEq (t2,t1)),
                                                    form (E.SubsetEq (s2,s1)))
    | (WFElemSubset, E.SetElemT s1, E.SetElemT s2) -> F.And(form (E.InEq (t2,t1)),
                                                            form (E.SubsetEqElem (s2,s1)))
    | (WFTidSubset, E.SetThT s1, E.SetThT s2) -> F.And(form (E.InEq (t2,t1)),
                                                       form (E.SubsetEqTh (s2,s1)))
    | _ -> assert false in
  let cons (eq:delta_op_t) (op:wf_op_t) (t1:E.term) (t2:E.term) : E.formula =
    match (op, eq) with
    | (_, Preserve) -> form (E.Eq (t2, t1))
    | (WFIntLess, Decrement)    -> begin
                                    match (t1, t2) with
                                    | (E.IntT i1, E.IntT i2) -> form(E.Less (i2, i1))
                                    | _ -> assert false
                                   end
    | (WFIntSubset, Decrement)
    | (WFPairSubset, Decrement)
    | (WFAddrSubset, Decrement)
    | (WFElemSubset, Decrement)
    | (WFTidSubset, Decrement) -> build_dec op t1 t2 in

  let build_lexic_decrement () : E.formula =
    let (disjs, _) =
      List.fold_left (fun (ds,eq_phi) (pre,op) ->
        let post = E.prime_modified_term [ante] pre in
        let dec = cons Decrement op pre post in
        let pres = cons Preserve op pre post in
        match ds with
        | [] -> ([dec],pres)
        | _  -> ((F.And (dec, eq_phi))::ds, F.And(pres, eq_phi))
      ) ([],F.True) accept.delta in
    F.disj_list disjs in

  if AcceptanceSet.mem e accept.bad then begin
    let (n,m,t) = e in
    Debug.infoMsg (fun _ -> "IS BAD: " ^ (node_id_to_str n) ^ " -> " ^
                                         (node_id_to_str m));
    let _ = match t with
            | Any -> Debug.infoMsg (fun _ -> "ANY")
            | Pres -> Debug.infoMsg (fun _ -> "PRES") in
    build_lexic_decrement ();
    (*
    let (disjs, _) =
      List.fold_left (fun (ds,eq_phi) (pre,op) ->
        let post = E.prime_modified_term [ante] pre in
        let dec = cons Decrement op pre post in
        let pres = cons Preserve op pre post in
        match ds with
        | [] -> ([dec],pres)
        | _  -> ((F.And (dec, eq_phi))::ds, F.And(pres, eq_phi))
      ) ([],F.True) accept.delta in
    F.disj_list disjs
    *)
    (*
    let pre = fst accept.delta in
    let post = E.prime_modified_term [ante] (fst accept.delta) in
    cons pre post Decrement
    *)
  end else if (not (AcceptanceSet.mem e (AcceptanceSet.union accept.good accept.bad))) then begin
    let (n,m,t) = e in
    Debug.infoMsg (fun _ ->
                     "IS NOT CARE: " ^ (node_id_to_str n) ^ " -> " ^
                                       (node_id_to_str m));
    let _ = match t with
            | Any -> Debug.infoMsg (fun _ -> "ANY")
            | Pres -> Debug.infoMsg (fun _ -> "PRES") in

    let pres = F.conj_list (
                List.map (fun (pre,op) ->
                  let post = E.prime_modified_term [ante] pre in
                  cons Preserve op pre post
                ) accept.delta) in
    let dec = build_lexic_decrement () in
    F.Or (pres, dec)
    (*
        let post = E.prime_modified_term [ante] pre in
        let dec = cons Decrement op pre post in
        let pres = cons Preserve op pre post in
        F.Or (dec, pres)
    *)
    (*
        cons Preserve op pre post
    *)
    (*
    let pre = fst accept.delta in
    let post = E.prime_modified_term [ante] (fst accept.delta) in
    (* All functions in delta should be preserved *)
    cons pre post Preserve
    *)
  end else
    F.True


let free_voc (pvd:t) : E.ThreadSet.t =
  pvd.free_voc


let new_support (ts:(supp_line_t * Tactics.proof_plan) list)
                (fs:(supp_line_t * Tag.f_tag list) list) : support_t =
  let plans = Hashtbl.create 8 in
  let spec_plans = Hashtbl.create 8 in
  let node_plans = Hashtbl.create 8 in
  let gral_plan = ref None in
  let facts = Hashtbl.create 8 in
  let spec_facts = Hashtbl.create 8 in
  let node_facts = Hashtbl.create 8 in
  let gral_fact = ref [] in

  List.iter (fun (scope,plan) ->
    match scope with
    | All -> if !gral_plan <> None then begin
               Interface.Err.msg "General plan already defined" $
                  "Plans for the general case has already been defined.";
               raise(Malformed_PVD_support)
             end else
               gral_plan := Some plan
    | Trans i -> if Hashtbl.mem plans i then begin
                   Interface.Err.msg "Plans for transition already defined" $
                     Printf.sprintf "Plans for transition %i has already been \
                                     defined before." i;
                   raise(Malformed_PVD_support)
                 end else
                   Hashtbl.add plans i plan
    | TransSpec (i,c) -> if Hashtbl.mem spec_plans (i,c) then begin
                           Interface.Err.msg "Plans for transition already defined" $
                             Printf.sprintf "Plans for transition %i and condition %s has \
                                             already been defined before." i (cond_to_str c);
                           raise(Malformed_PVD_support)
                         end else
                           Hashtbl.add spec_plans (i,c) plan
    | TransNodeSpec (i,ns,cs) ->
        List.iter (fun n ->
          List.iter (fun c ->
            if Hashtbl.mem node_plans (i,n,c) then begin
              Interface.Err.msg "Plans for transition already defined" $
              Printf.sprintf "Plans for transition %i, node %s and condition %s \
                              has already been defined before." i n (cond_to_str c);
              raise(Malformed_PVD_support)
            end else
              Hashtbl.add node_plans (i,n,c) plan
          ) cs
        ) ns
  ) ts;
  List.iter (fun (scope,tags) ->
    match scope with
    | All -> if !gral_fact <> [] then begin
               Interface.Err.msg "General facts already defined" $
                  "Facts for the general case has already been defined.";
               raise(Malformed_PVD_support)
             end else
               gral_fact := tags
    | Trans i -> if Hashtbl.mem facts i then begin
                   Interface.Err.msg "Facts for transition already defined" $
                     Printf.sprintf "Facts for transition %i has already been \
                                     defined before." i;
                   raise(Malformed_PVD_support)
                 end else
                   Hashtbl.add facts i tags
    | TransSpec (i,c) -> if Hashtbl.mem spec_facts (i,c) then begin
                           Interface.Err.msg "Facts for transition already defined" $
                             Printf.sprintf "Facts for transition %i and condition %s \
                                             has already been defined before."
                                              i (cond_to_str c);
                           raise(Malformed_PVD_support)
                         end else
                           Hashtbl.add spec_facts (i,c) tags
    | TransNodeSpec (i,ns,cs) ->
        List.iter (fun n ->
          List.iter (fun c ->
            if Hashtbl.mem node_facts (i,n,c) then begin
              Interface.Err.msg "Facts for transition already defined" $
              Printf.sprintf "Facts for transition %i, node %s and condition %s \
                              has already been defined before."
                                i n (cond_to_str c);
              raise(Malformed_PVD_support)
            end else
              Hashtbl.add node_facts (i,n,c) tags
          ) cs
        )ns
  ) fs;
  {
    tactics = {global_tactics = !gral_plan;
               local_gral_tactics = plans;
               local_spec_tactics = spec_plans;
               local_node_tactics = node_plans};
    facts = {global_facts = !gral_fact;
             local_gral_facts = facts;
             local_spec_facts = spec_facts;
             local_node_facts = node_facts;};
  }


let supp_tags (supp:support_t) : Tag.f_tag list =
  (supp.facts.global_facts) @
  (Hashtbl.fold (fun _ tags xs ->
    tags @ xs
  ) (supp.facts.local_gral_facts) []) @
  (Hashtbl.fold (fun _ tags xs ->
    tags @ xs
  ) (supp.facts.local_spec_facts) [])


let supp_fact (supp:support_t)
              (line:int)
              (n_opt:node_id_t option)
              (c:conditions_t) : Tag.f_tag list =
  let subsearch () =
    try
      Hashtbl.find (supp.facts.local_spec_facts) (line,c)
    with Not_found ->
      begin
        try
          Hashtbl.find (supp.facts.local_gral_facts) line
        with Not_found -> supp.facts.global_facts
      end in
  match n_opt with
  | Some n -> begin
                try
                  Hashtbl.find (supp.facts.local_node_facts) (line,n,c)
                with Not_found -> subsearch()
              end
  | None -> subsearch()



let supp_plan (supp:support_t)
              (line:int)
              (n_opt:node_id_t option)
              (c:conditions_t) : Tactics.proof_plan =
  let subsearch () =
    try
      Hashtbl.find (supp.tactics.local_spec_tactics) (line,c)
    with Not_found ->
      begin
        try
          Hashtbl.find (supp.tactics.local_gral_tactics) line
        with Not_found -> match supp.tactics.global_tactics with
                          | None -> Tactics.empty_proof_plan
                          | Some plan -> plan
      end in
  match n_opt with
    | Some n -> begin
                  try
                    Hashtbl.find (supp.tactics.local_node_tactics) (line,n,c)
                  with Not_found -> subsearch()
                end
    | None -> subsearch()
