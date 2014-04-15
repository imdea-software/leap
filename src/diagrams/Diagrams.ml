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
type acceptance_t = {good : accept_triple_t list;
                     bad  : accept_triple_t list;
                     delta: E.formula; }

type next_table_t = (node_id_t, NodeIdSet.t) Hashtbl.t
type tau_table_t = (node_id_t * int * E.V.t, NodeIdSet.t) Hashtbl.t


exception Duplicated_node of node_id_t
exception Undefined_node of node_id_t
exception Undefined_edge of edge_t
exception BadBoxedEdge of edge_t
exception BadBox of box_id_t
exception No_initial


(* Type for Parametrized Verification Diagrams *)
type pvd_t = {
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


type pvd_vc_t = {
	initiation : Tactics.vc_info;
}


(**  Configuration  **)
let initNodeNum = 30
let initEdgeNum = 50


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


let node_id_to_str (id:node_id_t) : string =
  id


let box_id_to_str (id:box_id_t) : string =
  id


let to_str (pvd:pvd_t) : string =
  let nodes_str = String.concat ","
                    (Hashtbl.fold (fun n _ xs -> (node_id_to_str n)::xs) pvd.nodes []) in
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
                         let map xs = List.map (fun (n1,n2,k) ->
                                        "(" ^(node_id_to_str n1)^ "," ^
                                             (node_id_to_str n2)^ "," ^
                                             (kind_to_str k)^ ")"
                                      ) xs in
                         let good_list_str = String.concat "," (map acc.good) in
                         let bad_list_str = String.concat "," (map acc.bad) in
                         "\n  << Good : {" ^good_list_str^ "};\n" ^
                           "     Bad  : {" ^bad_list_str^ "};\n" ^
                           "     " ^(E.formula_to_str acc.delta)^ " >>" ^ str
                       ) "" pvd.acceptance in
  ("Diagram[" ^pvd.name^ "]\n\n" ^
   "Nodes: " ^nodes_str^ "\n\n" ^
   "Boxes: " ^boxes_str^ "\n\n" ^
   "Initial: " ^initial_str^ "\n\n" ^
   "Edges: " ^edges_str^ "\n\n" ^
   "Acceptance: " ^acceptance_str^ "\n")
   


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
                   raise(Undefined_edge e)
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

  print_endline "1";
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
  print_endline "2";

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

  print_endline "3";

  (* Compute the free vocabulary of nodes *)
  Hashtbl.iter (fun n_id n_info ->
    let mu_voc = E.voc n_info.mu in
    let free_mu_voc = match box_param nTbl bTbl n_id with
                      | None -> mu_voc
                      | Some t -> E.ThreadSet.remove t mu_voc in
    free_voc := E.ThreadSet.union !free_voc free_mu_voc;
  ) nTbl;

  print_endline "4";

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
                    | Label ts -> List.fold_left (fun set (id,t) ->
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
    try
      let old_e_info = Hashtbl.find eTbl (n1,n2) in
      Hashtbl.replace eTbl (n1,n2) (EdgeInfoSet.add (kind,trans) old_e_info)
    with Not_found -> Hashtbl.add eTbl (n1,n2) (EdgeInfoSet.singleton (kind,trans));
    add_next_node n1 n2;
    add_tau n1 n2 trans;
  ) es;
  (eTbl, nextTbl, tTbl, !free_voc)


let check_acceptance (nTbl:node_table_t)
                     (eTbl:edge_table_t)
                     (acs:(accept_triple_t list * accept_triple_t list * E.formula) list)
        : acceptance_t list =
  List.map (fun (goods, bads, delta) ->
    List.iter (fun (n1,n2,kind) ->
      is_defined nTbl n1;
      is_defined nTbl n2;
      well_defined_acceptance_edge eTbl (n1,n2, (kind,NoLabel));
      well_defined_boxed_edge nTbl (n1,n2,(kind,NoLabel));
    ) (goods @ bads);
    {
      good = goods;
      bad = bads;
      delta = delta;
    }
  ) acs


(**  Constructors  **)

let new_pvd (name:string)
            (ns:node_t list)
            (bs:box_t list)
            (is:node_id_t list)
            (es:edge_t list)
            (acs:(accept_triple_t list * accept_triple_t list * E.formula) list) : pvd_t =
  print_endline ("A");
  let (nTbl,bTbl,free_voc_nodes) = check_and_define_nodes ns bs in
  print_endline ("B");
  let iSet = build_initial nTbl is in
  print_endline ("C");
  let (eTbl, nextTbl, tTbl, free_voc_edges) = check_and_define_edges nTbl bTbl es in
  let accept_list = check_acceptance nTbl eTbl acs in
  print_endline ("D");
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


module type S =
  sig
		val gen_vcs : pvd_t -> pvd_vc_t
	end


module Make (C:Core.S) : S =
  struct

		let gen_initiation (pvd:pvd_t) : Tactics.vc_info =
			let init_mu = F.disj_list (NodeIdSet.fold (fun n xs ->
																	(Hashtbl.find pvd.nodes n).mu :: xs
																) pvd.initial []) in
			let (theta, voc) = C.theta (E.voc init_mu) in
			Tactics.create_vc_info [] F.True theta init_mu voc E.NoTid 0


		let gen_vcs (pvd:pvd_t) : vc_t =
			{
				initiation = gen_initiation pvd;
      }
	end
