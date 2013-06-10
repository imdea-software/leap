(* File Diagrams.ml *)

open Printf
open LeapLib

module E        = Expression
module OcamlSys = Sys
module Sys      = System
module Stm      = Statement

(* Type declaration *)

(* Types for transitions *)
type trans_id_t = E.pc_t
type trans_t = trans_id_t * E.shared_or_local


(* Types for nodes *)
type node_id_t = int
type node_info_t = E.formula
type node_t = node_id_t * node_info_t
type node_table_t = (node_id_t, node_info_t) Hashtbl.t
type next_table_t = (node_id_t, node_id_t) Hashtbl.t


(* Types for edges *)
type edge_type_t = Normal | Large
type edge_info_t = edge_type_t * trans_t list
type edge_pair_t = node_id_t * node_id_t
type edge_t = node_id_t * node_id_t * edge_info_t
type edge_table_t = (edge_pair_t, edge_info_t) Hashtbl.t


(* Types for boxes *)
type box_id_t    = int

module BoxIdSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = box_id_t
  end )

type box_t       = (box_id_t * node_id_t list * E.tid)
type box_table_t = (node_id_t, box_id_t * E.tid) Hashtbl.t



module NodeIdSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = node_id_t
  end )


module EdgeSet : Set.S with type elt = edge_pair_t = 
  Set.Make (struct
    let compare = Pervasives.compare
    type t = edge_pair_t
  end)


(* Acceptance conditions type *)
type delta_range_t =
    Single of node_id_t
  | Range of node_id_t * node_id_t
  | Default
type delta_fun_t = (node_id_t, E.term) Hashtbl.t
type acceptance_pair_t = EdgeSet.t * EdgeSet.t * delta_fun_t
type acceptance_list_t = acceptance_pair_t list


(* Type for Closed Verification Diagrams *)
type vd_t = {
  name    : string;
  threads : int;
  nodes   : node_table_t;
  nodes_0 : node_id_t list;
  next    : next_table_t;
  tau     : (node_id_t * trans_t, node_id_t) Hashtbl.t;
  edges   : edge_table_t;
  (* Acceptance conditions *)
  accept  : acceptance_list_t
  (* Ranking functions *)
  (* Labeling function *)
}



(* Type for Parametrized Verification Diagrams *)
type pvd_t = {
  pvd_name              : string;
  pvd_support           : E.formula list;
  pvd_nodes             : node_table_t;
  pvd_nodes_0           : node_id_t list;
  pvd_boxes             : box_t list;
  pvd_box_tbl           : box_table_t;
  pvd_next              : (node_id_t, node_id_t) Hashtbl.t;
  pvd_tau               : (node_id_t * trans_t, node_id_t) Hashtbl.t;
  pvd_edges             : edge_table_t;
  (* Acceptance conditions *)
  pvd_accept            : acceptance_list_t;
  (* Ranking functions *)
  (* Labeling function *)
  mutable pvd_phi_param : E.tid list;
}


(* Verification Diagram Verification conditions *)
type vd_vc_t = {
  initialization : E.formula;
  consecution    : (node_id_t * trans_t * E.formula) list;
  acceptance     : E.formula list;
  fairness       : (edge_pair_t * trans_t * E.formula) list;
  satisfaction   : E.formula list
}

(* Configuration *)
let initNodeNum = 30
let initEdgeNum = 50
let defaultNodeId = -1


module PP = struct
  (* PRINTING FUNCTIONS *)
  let node_id_to_str (i:node_id_t) : string =
    if i = defaultNodeId then
      "DEFAULT"
    else
      string_of_int i
  
  
  let node_info_to_str (info:node_info_t) : string =
    let f = info in
      (E.formula_to_str f)
  
  
  let node_to_str (n:node_t) : string =
    let (id,info) = n in
    sprintf "[%s] : { %s }" (node_id_to_str id) (node_info_to_str info)
  
  
  let node_table_to_str (nTbl:node_table_t) : string =
    let n_list = Hashtbl.fold (fun id info xs -> node_to_str(id,info)::xs) nTbl []
    in
      String.concat "\n" n_list
  
  
  let trans_id_to_str (id:trans_id_t) : string =
    E.pc_to_str id
  
  
  let trans_to_str (t:trans_t) : string =
    let (id,th) = t
    in
      sprintf "T_%s%s" (trans_id_to_str id) (E.shared_or_local_to_str th)
  
  
  let edge_info_to_str (info:edge_info_t) : string =
    let (_, t_list) = info in
    let th_str = String.concat ", " $ List.map (trans_to_str) t_list
    in
      th_str
  
  
  let edge_arrow_to_str (nodes:edge_pair_t) : string =
    let (n1,n2) = nodes in
    sprintf "[%s]->[%s]" (node_id_to_str n1) (node_id_to_str n2)
  
  
  let edge_large_arrow_to_str (nodes:edge_pair_t) : string =
    let (n1,n2) = nodes in
    sprintf "[%s]=>[%s]" (node_id_to_str n1) (node_id_to_str n2)
  
  
  let edge_to_str (e:edge_t) : string =
    let (from_node, to_node, info) = e in
    let (e_type,_) = info in
    let edge_fun   = match e_type with
                       Normal -> edge_arrow_to_str
                     | Large  -> edge_large_arrow_to_str in
    sprintf "%s: {%s}\n" (edge_fun (from_node, to_node))
                         (edge_info_to_str info)
  
  
  let edge_table_to_str (eTbl:edge_table_t) : string =
    let e_str = Hashtbl.fold (fun (n1,n2) info str ->
                  edge_to_str(n1,n2,info) ^ str
                ) eTbl ""
    in
      e_str
  
  
  let edgeset_to_str (s:EdgeSet.t) : string =
    let str_list = ref [] in
    let _        = EdgeSet.iter (fun e ->
                     str_list := (edge_arrow_to_str e) :: !str_list
                   ) s in
    let set_str  = String.concat ", " !str_list
    in
      sprintf "{%s}" set_str
  
  
  let delta_fun_to_str (fTbl:delta_fun_t) : string =
    let res = Hashtbl.fold (fun pos expr str ->
                sprintf"%s : %s\n%s" (node_id_to_str pos)
                                     (E.term_to_str expr)
                                     (str)
              ) fTbl ""
    in
      res
  
  
  let acceptance_pair_to_str (pair:acceptance_pair_t) : string =
    let (l1,l2,fTbl) = pair in
    let l1_str  = String.concat ", " $
                    List.map edge_arrow_to_str (EdgeSet.elements l1) in
    let l2_str  = String.concat ", " $
                    List.map edge_arrow_to_str (EdgeSet.elements l2) in
    let f_str   = delta_fun_to_str fTbl
    in
      sprintf "{%s}:{%s} with \n\
                %s\n" l1_str l2_str f_str
  
  
  let acceptance_list_to_str (l:acceptance_list_t) : string =
    String.concat "\n" $ List.map acceptance_pair_to_str l
  
  
  let vd_to_str (vd:vd_t) : string =
    sprintf "Diagram: %s\n\n\
             Threads: %i\n\n\
             Nodes:\n%s\n\n\
             Initial:\n{%s}\n\n\
             Edges:\n%s\n\
             Acceptance:\n%s\n"
            (vd.name)
            (vd.threads)
            (node_table_to_str vd.nodes)
            (String.concat ", " $ List.map node_id_to_str vd.nodes_0)
            (edge_table_to_str vd.edges)
            (acceptance_list_to_str vd.accept)
  
  
  let vc_to_str (vc:vd_vc_t) : string =
    sprintf "Initialization:\n%s\n\n\
             Consecution:\n%s\n\n\
             Acceptance:\n%s\n\n\
             Fairness:\n%s\n\n\
             Satisfaction:\n%s\n"
            (E.formula_to_str vc.initialization)
            (String.concat "\n" $ List.map (fun (n,t,f) ->
               sprintf "Node %s, %s: %s" (node_id_to_str n)
                                         (trans_to_str t)
                                         (E.formula_to_str f)) vc.consecution)
            (String.concat "\n" $ List.map E.formula_to_str vc.acceptance)
            (String.concat "\n" $ List.map (fun (e,t,f) ->
               sprintf "(%s,%s): %s" (edge_arrow_to_str e)
                                     (trans_to_str t)
                                     (E.formula_to_str f)) vc.fairness)
            (String.concat "\n" $ List.map E.formula_to_str vc.satisfaction)
end

(* Exceptions *)
exception Undefined_initial_node of node_id_t
exception Duplicated_node of node_id_t
exception Undefined_edge of node_id_t * node_id_t
exception No_edge_info of node_id_t * node_id_t
exception Unknown_transition of trans_t
exception Unknown_transition_param of E.tid list
exception Unparametrized_transition
exception Missing_transition_info of trans_t
exception Open_thread_identifier of E.tid
exception No_thread
exception Undefined_node of node_id_t
exception Uncovered_node of node_id_t
exception Unexpected_sort of E.sort
exception Unexpected_format
exception Sort_expected
exception Impossible_apply_function of delta_fun_t * node_id_t

module type S =
sig
  (********************  GENERAL VERIFICATION DIAGRAM  ********************)
  
  (* Diagram manipulation functions *)
  val new_diagram : string ->
                    int ->
                    node_t list ->
                    node_id_t list ->
                    edge_t list ->
                    acceptance_list_t ->
                    vd_t
  
  val new_node_id : int -> node_id_t
  val new_node : node_id_t -> Expression.formula -> node_t
  
  val new_box : box_id_t -> node_id_t list -> Expression.tid -> box_t
  
  val new_trans : Expression.pc_t -> Expression.shared_or_local -> trans_t
  
  val new_edge_info : edge_type_t -> trans_t list -> edge_info_t
  val new_edge : node_id_t -> node_id_t -> edge_info_t -> edge_t
  
  val new_acceptance_pair : (node_id_t * node_id_t) list ->
                            (node_id_t * node_id_t) list ->
                            delta_fun_t ->
                            acceptance_pair_t
  val new_acceptance_list : acceptance_pair_t list -> acceptance_list_t
  
  (* Verification diagram module *)
  val gen_node_range : node_id_t -> node_id_t -> node_id_t list
  
  
  
  (*******************  PARAMETRIZED VERIFICATION DIAGRAM  *******************)
  val new_param_diagram : string ->
                          Expression.formula list ->
                          node_t list ->
                          node_id_t list ->
                          box_t list ->
                          edge_t list ->
                          acceptance_list_t ->
                          (pvd_t * Expression.tid list)
  
  
  val load_pvd_formula_param : pvd_t -> Expression.tid list -> Expression.tid list -> pvd_t
  
  
  (* Printing functions *)
  val pvd_to_str : pvd_t -> string
  
  
  (* General verification diagram verification conditions *)
  val gen_vd_vc : bool -> System.system_t -> vd_t -> vd_vc_t
  
  
  (* Parametrized verification diagram verification conditions *)
  val gen_pvd_vc : bool -> System.system_t -> pvd_t -> vd_vc_t
  
  
  (* Verification condition queries *)
  val vd_initialization : vd_vc_t -> Expression.formula
  val vd_consecution : vd_vc_t -> (node_id_t * trans_t * Expression.formula) list
  val vd_acceptance : vd_vc_t -> Expression.formula list
  val vd_fairness : vd_vc_t -> (edge_pair_t * trans_t * Expression.formula) list
  val vd_satisfaction : vd_vc_t -> Expression.formula list
  
  (* Verification conditions check *)
  val check_pvd : System.system_t -> pvd_t -> bool
end

module Make (VCG : VCGen.S) : S =
struct
  (* Empty box table *)
  let empty_box_tbl = Hashtbl.create 1
  
  
  (* COMPARISON FUNCTION *)
  let comp_tag t1 t2 =
    String.lowercase t1 = String.lowercase t2  
  
  (* CONSTRUCTION FUNCTIONS *)
  let new_trans (p:E.pc_t) (th:E.shared_or_local) : trans_t = (p,th)
  
  let new_node_id (i:int) : node_id_t = i
  let new_node_info (f:E.formula) : node_info_t = f
  let new_node (n:node_id_t) (info:node_info_t) : node_t = (n,info)
  
  let new_edge_info (et:edge_type_t) (ts:trans_t list) : edge_info_t = (et,ts)
  let new_edge (f:node_id_t) (t:node_id_t) (info:edge_info_t) : edge_t =
    (f, t, info)
  
  let new_box (id:box_id_t) (ns:node_id_t list) (th:E.tid) : box_t =
    (id, ns, th)
  
  let new_acceptance_pair (p:(node_id_t * node_id_t) list)
                          (r:(node_id_t * node_id_t) list)
                          (d:delta_fun_t) : acceptance_pair_t =
    let pSet = List.fold_left (fun s e -> EdgeSet.add e s) EdgeSet.empty p in
    let rSet = List.fold_left (fun s e -> EdgeSet.add e s) EdgeSet.empty r
    in
      (pSet, rSet , d)
  
  
  let new_acceptance_list (l:acceptance_pair_t list) : acceptance_list_t = l
  
  
  
  
  (* VERIFICATION DIAGRAM MANIPULATION FUNCTIONS *)
  let vd_node_list (vd:vd_t) : node_id_t list =
    let ns = ref [] in
    let _  = Hashtbl.iter (fun n _ -> ns := n :: !ns) vd.nodes
    in
      !ns
  
  
  let app_delta (d:delta_fun_t) (n:node_id_t) : E.term =
    try
      Hashtbl.find d n
    with _ -> try
                Hashtbl.find d defaultNodeId
              with _ -> Interface.Err.msg "Impossible to apply ranking function" $
                          sprintf "It was not possible to apply the ranking \
                                   function for node \"%s\". All known function \
                                   points are:\n%s\n"
                                  (PP.node_id_to_str n)
                                  (PP.delta_fun_to_str d);
                        raise(Impossible_apply_function(d,n))
  
  
  
  
  (* VERIFICATION DIAGRAM MODULE *)
  let gen_node_range (min:node_id_t) (max:node_id_t) : node_id_t list =
    LeapLib.rangeList min max
  
  
  let node_mu (vd:vd_t) (n:node_id_t) : E.formula =
    let info = Hashtbl.find vd.nodes n in
      info
  
  
  let edge_nu (vd:vd_t) (e:edge_pair_t) : trans_t list =
    let (_, t_list) = Hashtbl.find vd.edges e in
      t_list
  
  
  let pvd_node_mu (pvd:pvd_t) (n:node_id_t) : E.formula =
    let info = Hashtbl.find pvd.pvd_nodes n in
      info
  
  
  let pvd_edge_nu (pvd:pvd_t) (e:edge_pair_t) : trans_t list =
    let (_, t_list) = Hashtbl.find pvd.pvd_edges e in
      t_list
  
  
  let edge_type (info:edge_info_t) : edge_type_t =
    let (e_type, _) = info
    in
      e_type
  
  
  let edge_trans (info:edge_info_t) : trans_t list =
    let (_, t_list) = info
    in
      t_list
  
  
  let enabled (sys:Sys.system_t) (t:trans_t) : E.formula =
    let (pc,th)      = t in
    let (proc,stm)   = Sys.get_statement_at sys pc in
    let enable_conds = Stm.enabling_condition th stm in
    (* FIX: Until we split "if" transitions into a true and a false transition *)
    let cond         = E.disj_list enable_conds
    in
      cond
  
  
  (* Returns a list with all parameters of boxes where node 'n' belongs to *)
  let node_box_param_list (bTbl:box_table_t) (n:node_id_t) : E.tid list =
    List.map snd (Hashtbl.find_all bTbl n)
  
  (* As before, but returns a set *)
  let node_box_param_set (bTbl:box_table_t) (n:node_id_t) : E.ThreadSet.t =
    List.fold_left (fun s t -> E.ThreadSet.add t s)
      E.ThreadSet.empty (node_box_param_list bTbl n)
  
  
  (* Returns a list with all box identifiers of boxes where node 'n' belongs to *)
  let node_box_id (bTbl:box_table_t) (n:node_id_t) : box_id_t list =
    List.map fst (Hashtbl.find_all bTbl n)
  
  (* Same as before, but returns a set *)
  let node_box_id_set (bTbl:box_table_t) (n:node_id_t) : BoxIdSet.t =
    List.fold_left (fun s t -> BoxIdSet.add t s)
      BoxIdSet.empty (node_box_id bTbl n)
  
  let add_node (bTbl:box_table_t)
               (nTbl:node_table_t)
               (n:node_id_t)
               (info:node_info_t) : E.ThreadSet.t =
    let remains = ref E.ThreadSet.empty in
    let mu_voc = E.voc info in
    let box_param = node_box_param_list bTbl n in
    let _ = List.iter (fun x ->
              remains := E.ThreadSet.add x !remains
            ) (List.filter (fun x -> not (List.mem x box_param)) mu_voc) in
    let _ = if Hashtbl.mem nTbl n then
              begin
                Interface.Err.msg "Already defined node" $
                  sprintf "Another node with id %s has already been defined."
                    (PP.node_id_to_str n);
                  raise(Duplicated_node n)
                end
            else
              Hashtbl.replace nTbl n info
    in
      !remains
  
  
  let is_defined (nTbl:node_table_t) (n:node_id_t) : bool =
    Hashtbl.mem nTbl n
  
  
  let check_all_defined (nTbl:node_table_t) (is:node_id_t list) : unit =
    List.iter (fun i ->
      if not (Hashtbl.mem nTbl i) then
        begin
          Interface.Err.msg "Undefined initial node" $
            sprintf "A node with id \"%s\" has been declared as initial node, \
                     but no node with such id has been previously defined."
                     (PP.node_id_to_str i);
          raise(Undefined_initial_node i)
        end
    ) is
  
  
  let check_transition_range (th_num:int) (tran:trans_t) : unit =
    let (_,t) = tran
    in
      match t with
        E.Shared -> ()
      | E.Local ((E.VarTh v) as th) ->
          if E.is_tid_val th then
            let i = int_of_string (E.var_id v) in
            if i < 1 || th_num < i then
              begin
                Interface.Err.msg "Transition out of bounds" $
                  sprintf "Transition %s is out of the transition range for the \
                           current system, since a system with %i threads has \
                           been specified."
                          (PP.trans_to_str tran) th_num;
                raise(Unknown_transition tran)
              end
      | _ -> ()
  
  
  let check_and_add_edges (th_num:int)
                          (nTbl:node_table_t)
                          (eTbl:edge_table_t)
                          (nxtTbl:next_table_t)
                          (tauTbl:(node_id_t * trans_t, node_id_t) Hashtbl.t)
                          (es:edge_t list) : unit =
    List.iter (fun (f,t,(e_type,ts)) ->
      let _    = is_defined nTbl f in
      let _    = is_defined nTbl t in
      let _    = List.iter (check_transition_range th_num) ts in
      let info = new_edge_info e_type ts in
        Hashtbl.replace eTbl (f,t) info;
        Hashtbl.add nxtTbl f t;
        List.iter (fun x -> Hashtbl.add tauTbl (f,x) t) ts
    ) es
  
  
  let check_transition_param (bTbl:box_table_t) (n:node_id_t) (tran:trans_t) : E.tid list =
    let box_param = node_box_param_list bTbl n in
    let (id,t) = tran
    in
      match t with
        E.Shared -> []
      | E.Local th -> if not (List.mem th box_param) then [th] else []
  
  
  let check_and_add_pvd_edges (nTbl:node_table_t)
                              (eTbl:edge_table_t)
                              (nxtTbl:next_table_t)
                              (tauTbl:(node_id_t * trans_t, node_id_t) Hashtbl.t)
                              (bTbl:box_table_t)
                              (es:edge_t list) : E.ThreadSet.t =
    let remains = ref E.ThreadSet.empty in
    let _ = List.iter (fun (f,t,(e_type,ts)) ->
              let _    = is_defined nTbl f in
              let _    = is_defined nTbl t in
              let _    = List.iter (fun x ->
                           remains := E.ThreadSet.add x !remains
                         ) (List.flatten $ List.map (check_transition_param bTbl f) ts) in
              let info = new_edge_info e_type ts in
                Hashtbl.add eTbl (f,t) info;
                Hashtbl.add nxtTbl f t;
                  List.iter (fun x -> Hashtbl.add tauTbl (f,x) t) ts
            ) es
    in
      !remains
  
  
  let check_defined_edge_set (eTbl:edge_table_t) (s:EdgeSet.t) : unit =
    EdgeSet.iter (fun e -> if not (Hashtbl.mem eTbl e) then
                             begin
                               Interface.Err.msg "Undefined edge" $
                                 sprintf "Edge %s used in an acceptance \
                                          condition, but such edge has not \
                                          been declared as an edge before."
                                          (PP.edge_arrow_to_str e);
                               raise(Undefined_edge(fst e,snd e))
                             end
    ) s
  
  
  let check_acceptance (nTbl:node_table_t)
                       (eTbl:edge_table_t)
                       (acs:acceptance_list_t) : unit =
    let _ = List.iter (fun (pS,rS,_) -> check_defined_edge_set eTbl pS;
                                        check_defined_edge_set eTbl rS ) acs in
    let nSet = Hashtbl.fold (fun n _ s->NodeIdSet.add n s) nTbl NodeIdSet.empty in
    let _ = List.iter ( fun (_,_,dFunc) ->
              let dSet = Hashtbl.fold (fun n _ s -> NodeIdSet.add n s)
                                      dFunc NodeIdSet.empty
              in
                if NodeIdSet.mem defaultNodeId dSet then
                  begin
                    let dSet' = NodeIdSet.remove defaultNodeId dSet in
                    if not (NodeIdSet.subset dSet' nSet) then
                      let one = NodeIdSet.choose $ NodeIdSet.diff dSet' nSet in
                        Interface.Err.msg "Unknown node" $
                          sprintf "Ranking function associates an expression \
                                   to node %s in:\n%s\nBut such node has not \
                                   been declared as a diagram node before."
                                   (PP.node_id_to_str one)
                                   (PP.delta_fun_to_str dFunc);
                        raise(Undefined_node one)
                  end
                else
                  begin
                    if not(NodeIdSet.equal dSet nSet) then
                      let only_d = NodeIdSet.diff dSet nSet in
                      let only_n = NodeIdSet.diff nSet dSet in
                      if not (NodeIdSet.is_empty only_d) then
                        begin
                          let one = NodeIdSet.choose only_d in
                            Interface.Err.msg "Unknown node" $
                            sprintf "Ranking function associates an expression \
                                     to node %s in:\n%s\nBut such node has not \
                                     been declared as a diagram node before."
                                     (PP.node_id_to_str one)
                                     (PP.delta_fun_to_str dFunc);
                          raise(Undefined_node one);
                        end;
                      if not (NodeIdSet.is_empty only_n) then
                        begin
                          let one = NodeIdSet.choose only_n in
                          Interface.Err.msg "Ranking function undefined for node"$
                            sprintf "Ranking function does not cover the case at \
                                     which node %s is considered, in the \
                                     definition:\n%s\n"
                                     (PP.node_id_to_str one)
                                     (PP.delta_fun_to_str dFunc);
                          raise(Uncovered_node one)
                        end
                    end
            ) acs
    in
      ()
  
  
  let check_vd_with_system (vd:vd_t) (sys:Sys.system_t) : unit =
    ()
  
  
  let new_diagram (d   : string)
                  (th  : int)
                  (ns  : node_t list)
                  (is  : node_id_t list)
                  (es  : edge_t list)
                  (acs : acceptance_list_t) : vd_t =
    let nTbl   = Hashtbl.create initNodeNum in
    let eTbl   = Hashtbl.create initEdgeNum in
    let nxtTbl = Hashtbl.create initEdgeNum in
    let tauTbl = Hashtbl.create initEdgeNum in
    let _      = List.iter (fun (n,info) ->
                   ignore $ add_node empty_box_tbl nTbl n info
                 ) ns in
    let _      = check_all_defined nTbl is in
    let _      = check_and_add_edges th nTbl eTbl nxtTbl tauTbl es in
    let _      = check_acceptance nTbl eTbl acs in
    let _ = Printf.printf "Next of node 1: %i" (Hashtbl.find nxtTbl 1) in
      {name    = d;
       threads = th;
       nodes   = nTbl;
       nodes_0 = is;
       next    = nxtTbl;
       tau     = tauTbl;
       edges   = eTbl;
       accept  = acs
      }
  
  
  (* Auxiliary function for gen_vd_vc *)
  let tran_assoc (t:trans_t)
                 (tLst:(int * E.pc_t * E.formula list)list) : E.formula =
    let (pc,th) = match t with
                    (i, E.Local (E.VarTh v as th)) ->
                      if E.is_tid_val th then
                        (i, E.var_val v)
                      else
                        begin
                          Interface.Err.msg "Not a closed thread id" $
                          sprintf "Looking for transition information over a \
                                   closed system, a closed thread identifier was \
                                   expected, but instead %s was provided as \
                                   argument." (E.tid_to_str th);
                          raise(Open_thread_identifier th)
                        end
                  | (_, E.Local t) ->
                    Interface.Err.msg "Not a valid thread identifier" $
                      sprintf "The thread \"%s\" is not valid as identifier"
                              (E.tid_to_str t);
                    raise(No_thread)
                  | (_, E.Shared)                         ->
                    Interface.Err.msg "No thread identifier was provided"
                      "Looking for transition information over a closed system, \
                       a transition with no thread identifier was provided.";
                    raise(No_thread) in
    let rec find i p lst = match lst with
                            [] -> Interface.Err.msg
                              "No transition relation information found" $
                              sprintf "While looking for transition relation \
                                       information for transition %s. No \
                                       information could be found related to \
                                       such transition." (PP.trans_to_str t);
                              raise(Missing_transition_info t)
                           | (i',p',f)::xs -> if i=i' && p=p' then
                                                E.disj_list f
                                              else
                                                find i p xs
    in
      find th pc tLst
  
  
  let cons_less_relation (s:E.sort) (t1:E.term) (t2:E.term)
                              : E.formula =
    match s with
      E.Int ->
        begin
          match (t1,t2) with
            (E.IntT i1, E.IntT i2) -> E.less_form i1 i2
          | _ -> Interface.Err.msg "Unexpected integer format" $
                   sprintf "An expression describing an integer was expected.";
                 raise(Unexpected_format)
        end
    | E.Set ->
        begin
          match (t1,t2) with
            (E.SetT s1, E.SetT s2) -> E.subset_form s1 s2
          | _ -> Interface.Err.msg "Unexpected set format" $
                   sprintf "An expression describing a set of addresses was \
                            expected.";
                 raise(Unexpected_format)
        end
    | E.SetTh ->
        begin
          match (t1,t2) with
            (E.SetThT s1, E.SetThT s2) -> E.subsetth_form s1 s2
          | _ -> Interface.Err.msg "Unexpected set of thread ids format" $
                   sprintf "An expression describing a set of thread identifiers \
                            was expected.";
                 raise(Unexpected_format)
        end
    | E.SetInt ->
        begin
          match (t1,t2) with
            (E.SetIntT s1, E.SetIntT s2) -> E.subsetint_form s1 s2
          | _ -> Interface.Err.msg "Unexpected set of integers format" $
                   sprintf "An expression describing a set of integers was \
                            expected.";
                 raise(Unexpected_format)
        end
    | s' -> Interface.Err.msg "Unexpected sort" $
              sprintf "Up to this moment, order relations are limited to \
                      integers only, while a ranking function of sort %s \
                      is trying to be analyzed."
                      (E.sort_to_str s');
          raise(Unexpected_sort s')
  
  
  let gen_vd_vc (hide_pres:bool) (sys:Sys.system_t) (vd:vd_t) : vd_vc_t =
  
    (* Initilization *)
    let theta     = VCG.gen_theta (Sys.SClosed 1) sys in
    let init_mu   = E.disj_list $ List.map(fun x -> node_mu vd x) vd.nodes_0 in
    let init      = E.Implies(theta, init_mu) in
  
    (* Consecution *)
    let tran_list = [] in
(*  let tran_list = VCG.vcgen_closed hide_pres false sys in *)
  
    let conseq    = ref [] in
    let _ = Hashtbl.iter (fun n info ->
              List.iter (fun (th,pc,f) ->
                let mu_n = node_mu vd n in
                let next = Hashtbl.find_all vd.next n in
                let next_conj  = E.disj_list $
                                   List.map (fun x -> node_mu vd x) next in
                let rho_form   = E.disj_list f in
                let antecedent = E.And (mu_n, rho_form) in
                let consequent = if hide_pres then
                                   E.prime_modified antecedent next_conj
                                 else
                                   E.prime next_conj
                in
                  conseq := (n,
                             (pc, E.Local (E.build_num_tid th)),
                             E.Implies (antecedent, consequent)
                            ) :: !conseq
              ) tran_list
            ) vd.nodes in
  
    (* Acceptance *)
    let accept = ref [] in
    let eSet = Hashtbl.fold (fun e _ s->EdgeSet.add e s) vd.edges EdgeSet.empty in
    let _ = List.iter (fun (pS,rS,d) ->
              let sDiff = EdgeSet.diff pS rS in
              let sComp = EdgeSet.diff eSet (EdgeSet.union pS rS) in
              Hashtbl.iter (fun (n1,n2) _ ->
                List.iter (fun (th,ps,f) ->
                  (* The line below shouldn't be E.conj_list ???? *)
                  let rho_form = E.disj_list f in
                  let mu_n1    = node_mu vd n1 in
                  let mu_n2'   = if hide_pres then
                                   E.prime_modified rho_form (node_mu vd n2)
                                 else
                                   E.prime $ node_mu vd n2 in
                  let pre      = E.And(rho_form, E.And(mu_n1, mu_n2')) in
                  let delta_n1 = app_delta d n1 in
                  let delta_n2'= if hide_pres then
                                   E.prime_modified_term rho_form
                                          (app_delta d n2)
                                 else
                                   E.prime_term $ app_delta d n2 in
                  let s        = E.term_sort delta_n1 in
                  let less     = cons_less_relation s delta_n2' delta_n1
                  in
                    if EdgeSet.mem (n1,n2) sDiff then
                      let eq = E.eq_term delta_n2' delta_n1 in
                      let cond = E.Implies(pre, E.Or(less,eq)) in
                      accept := cond :: !accept
                    else if EdgeSet.mem (n1,n2) sComp then
                      let cond = E.Implies(pre, less) in
                      accept := cond :: !accept
                    else
                      ()
                ) tran_list
              ) vd.edges
            ) vd.accept in
  
  
    (* Fairness *)
    let fair   = ref [] in
    let _ = Hashtbl.iter (fun (n1,n2) (_, edge_tau_list) ->
              let e             = (n1,n2) in
              let n1_mu         = node_mu vd n1
              in
                List.iter (fun t ->
                  let tau_rho  = tran_assoc t tran_list in
                  let t_next   = Hashtbl.find_all vd.tau (n1,t) in
                  let nxt_list = List.map (node_mu vd) t_next in
                  let nxt_mu   = if hide_pres then
                                   E.prime_modified tau_rho
                                      (E.disj_list nxt_list)
                                 else
                                   E.prime (E.disj_list nxt_list)
                  in
                    fair := (e,t,E.Implies (n1_mu, enabled sys t)) ::
                            (e,t,E.Implies (E.And(n1_mu,tau_rho), nxt_mu))::
                            !fair
                ) edge_tau_list
            ) vd.edges in
  
    (* Satisfaction *)
    let satisf = [] in
  
      {initialization = init;
       consecution    = !conseq;
       acceptance     = !accept;
       fairness       = !fair;
       satisfaction   = satisf
      }
  
  
  let vd_initialization (vc:vd_vc_t) : E.formula = vc.initialization
  
  let vd_consecution (vc:vd_vc_t) : (node_id_t * trans_t *E.formula) list =
    vc.consecution
  
  let vd_acceptance (vc:vd_vc_t) : E.formula list = vc.acceptance
  
  let vd_fairness (vc:vd_vc_t) : (edge_pair_t * trans_t * E.formula) list =
    vc.fairness
  
  
  let vd_satisfaction (vc:vd_vc_t) : E.formula list = vc.satisfaction
  
  
  (***************  Parametrized Verification Diagrams ****************)
  
  let check_and_add_boxes (n_list:node_t list) (bs:box_t list) : box_table_t =
    let tbl = Hashtbl.create 40 in
    let n_id_list = List.map fst n_list in
    let _ = List.iter (fun (box_id, ns,th) ->
              List.iter (fun id ->
                if Hashtbl.mem tbl id then
                  Interface.Err.msg "Node already parametrized by box" $
                    sprintf "The node with identifier %s is trying to be \
                             associated to box parameter %s, while it has \
                             already been associated to box parameter %s"
                              (PP.node_id_to_str id)
                              (E.tid_to_str th)
                              (E.tid_to_str (snd (Hashtbl.find tbl id)))
                else if not (List.mem id n_id_list) then
                  Interface.Err.msg "Box defined over unrecognized node" $
                    sprintf "A box is defined over node %s, which has not \
                             been declared before."
                              (PP.node_id_to_str id)
                else
                  Hashtbl.add tbl id (box_id, th)
              ) ns
            ) bs
    in
      tbl
  
  
  let new_param_diagram (d   : string)
                        (fs  : E.formula list)
                        (ns  : node_t list)
                        (is  : node_id_t list)
                        (bs  : box_t list)
                        (es  : edge_t list)
                        (acs : acceptance_list_t) : (pvd_t * E.tid list) =
    let bTbl      = check_and_add_boxes ns bs in
    let nTbl      = Hashtbl.create initNodeNum in
    let eTbl      = Hashtbl.create initEdgeNum in
    let nxtTbl    = Hashtbl.create initEdgeNum in
    let tauTbl    = Hashtbl.create initEdgeNum in
    let remains_n = List.fold_left (fun s (n,info) ->
                      E.ThreadSet.union s (add_node bTbl nTbl n info)
                    ) E.ThreadSet.empty ns in
    let _         = check_all_defined nTbl is in
    let remains_e = check_and_add_pvd_edges nTbl eTbl nxtTbl tauTbl bTbl es in
    let _         = check_acceptance nTbl eTbl acs in
    let remains   = E.ThreadSet.elements (E.ThreadSet.union remains_n remains_e) in
      (
        {
          pvd_name      = d;
          pvd_support   = fs;
          pvd_nodes     = nTbl;
          pvd_nodes_0   = is;
          pvd_boxes     = bs;
          pvd_box_tbl   = bTbl;
          pvd_next      = nxtTbl;
          pvd_tau       = tauTbl;
          pvd_edges     = eTbl;
          pvd_accept    = acs;
          pvd_phi_param = [];
        }, remains)
  
  
  
  let load_pvd_formula_param (pvd:pvd_t)
                             (remains:E.tid list)
                             (ths:E.tid list) : pvd_t =
    if List.for_all (fun x -> List.mem x ths) remains then
      begin
        pvd.pvd_phi_param<-ths;
        pvd
      end
    else
      begin
        let undef = List.filter (fun x -> not (List.mem x ths)) remains in
        Interface.Err.msg "Missing transition parameter" $
          sprintf "Transition parameters [%s] are not introduced as \
                   parameters of the formula neither as box parameters."
                    (String.concat "," $ List.map E.tid_to_str undef);
        raise(Unknown_transition_param undef)
      end
  
  
  let pvd_to_str (pvd:pvd_t) : string =
    sprintf "Diagram: %s\n\n\
             Suporting formulas:\n%s\n\n\
             Nodes:\n%s\n\n\
             Initial:\n{%s}\n\n\
             Boxes:%s\n\n\
             Edges:\n%s\n\
             Acceptance:\n%s\n"
            (pvd.pvd_name)
            (String.concat "\n" $ List.map E.formula_to_str pvd.pvd_support)
            (PP.node_table_to_str pvd.pvd_nodes)
            (String.concat ", " $ List.map PP.node_id_to_str pvd.pvd_nodes_0)
            (List.fold_left (fun str b ->
              let (box_id,ns,th) = b in
              let node_str = String.concat ", " $ List.map PP.node_id_to_str ns
              in
                str ^ (sprintf "\n{%s} : %s" node_str (E.tid_to_str th))
            ) "" pvd.pvd_boxes)
            (PP.edge_table_to_str pvd.pvd_edges)
            (PP.acceptance_list_to_str pvd.pvd_accept)
  
  
  let tvoc (pvd:pvd_t)
           (n1:node_id_t)
           (ns:node_id_t list)
           (f_voc:E.tid list) : E.tid list =
    let _ = if not $ List.for_all (fun n -> Hashtbl.mem pvd.pvd_nodes n) (n1::ns) then
              Interface.Err.msg "Node not found" $
              sprintf "The node identifier %s is not defined in the parametrized \
                       verification diagram, and thus its vocabulary cannot be \
                       determined."
                        (PP.node_id_to_str (List.find (fun n ->
                                           not (Hashtbl.mem pvd.pvd_nodes n)
                                        ) (n1::ns) )) in
    let mu_n1 = Hashtbl.find pvd.pvd_nodes n1 in
    let mu_ns = List.map (Hashtbl.find pvd.pvd_nodes) ns in
    let b     = if Hashtbl.mem pvd.pvd_box_tbl n1 then
                  node_box_param_list pvd.pvd_box_tbl n1
                else
                  [] in
    let voc_n1 = E.voc mu_n1 in
    let voc_ns = List.fold_left (fun xs phi -> xs @ (E.voc phi)) [] mu_ns in
    let voc_set = List.fold_left (fun s t ->
                    E.ThreadSet.add t s
                  ) E.ThreadSet.empty (voc_n1 @ voc_ns @ b @ f_voc)
    in
      E.ThreadSet.elements voc_set
  
  
  let beta (pvd:pvd_t) (n:node_id_t) (n':node_id_t) : E.formula =
    let bTbl = pvd.pvd_box_tbl in
    try
      let e_type        = edge_type (Hashtbl.find pvd.pvd_edges (n,n')) in
      let n_box_id_set  = node_box_id_set bTbl n in
      let n'_box_id_set = node_box_id_set bTbl n' in
      if (BoxIdSet.inter n_box_id_set n'_box_id_set <> BoxIdSet.empty
            && e_type = Normal) then
        let n_box_param_set  = node_box_param_set bTbl n in
        let n'_box_param_set = node_box_param_set bTbl n' in
        let param_list       = E.ThreadSet.elements $
                                E.ThreadSet.union n_box_param_set
                                                     n'_box_param_set in
        E.conj_list $ List.map (fun t ->
                           E.eq_tid (E.prime_tid t) t
                         ) param_list
      else
        E.True
    with _ -> begin
                Interface.Err.msg "No edge info" $
                  sprintf "Could not be found information for edge (%s,%s)"
                    (PP.node_id_to_str n) (PP.node_id_to_str n');
                raise(No_edge_info(n,n'))
              end
    
  
  let gen_fresh_and_build_ineq (ths:E.tid list) : (E.tid * E.formula) =
    let fresh_tid  = E.gen_fresh_tid ths in
    let diff_list  = List.map (fun j -> E.ineq_tid fresh_tid j) ths in
    let diff_conj  = E.conj_list diff_list
    in
      (fresh_tid, diff_conj)
  
  
  let post_process (vc:vd_vc_t) : vd_vc_t =
    let clean phi = VCG.clean_formula phi in
    let clean_cons (n,t,phi) = (n,t,clean phi) in
    let clean_fair (e,t,phi) = (e,t,clean phi)
    in
      if VCG.apply_tll_dp () then
        vc
      else
        {
          initialization = clean vc.initialization;
          consecution    = List.map clean_cons vc.consecution;
          acceptance     = List.map clean vc.acceptance;
          fairness       = List.map clean_fair vc.fairness;
          satisfaction   = List.map clean vc.satisfaction;
        }
  
  
  
  (* Generates the VC for a PVD. Arguments are:
      + sys: The system description
      + pvd: The PVD
      + phi_th : The list of tids parametrizing the formula to be proved
  *)
  let gen_pvd_vc (hide_pres:bool) (sys:Sys.system_t) (pvd:pvd_t) : vd_vc_t =
  
    (* General computations *)
    let pc_list = LeapLib.rangeList 1 (Sys.get_trans_num sys) in
    let phi_th = pvd.pvd_phi_param in
  
    (* Initialization *)
    let init_mu     = E.disj_list $ List.map (fun x ->
                                         pvd_node_mu pvd x
                                       ) pvd.pvd_nodes_0 in
    let init_mu_voc = E.voc init_mu in
    let theta       = VCG.gen_theta (Sys.SOpenArray init_mu_voc) sys in
    let init        = E.Implies(theta, init_mu) in
  
    (* Consecution *)
    let conseq    = ref [] in
  (*
    let _ = Hashtbl.iter (fun n info ->
              let next = Hashtbl.find_all pvd.pvd_next n in
              let next_disj = E.disj_list $
                                List.map (fun n' ->
                                  E.And (E.prime (pvd_node_mu pvd n'),
                                            beta pvd n n')
                                ) next in
              let mu_n = pvd_node_mu pvd n in
              let t_voc = tvoc pvd n next phi_th in
              List.iter (fun pc ->
                List.iter (fun i ->
                  let mode = VCG.new_open_thid_array_mode i [] in
                  let rho = E.conj_list
                              (VCG.gen_rho mode hide_pres false sys t_voc pc) in
                  let antecedent = E.And (mu_n, rho) in
                  let consequent = if hide_pres then
                                     E.disj_list $ List.map (fun n' ->
                                       let p = E.prime_modified antecedent
                                                  (pvd_node_mu pvd n')
                                       in
                                         E.And (p, beta pvd n n')
                                     ) next
                                   else
                                     next_disj in
                  let cond = E.Implies (antecedent, consequent)
                  in
                    conseq := (n, (pc,E.Local i), cond) :: !conseq
                ) t_voc;
                (* The extra condition *)
                let (fresh_tid, diff_conj) = gen_fresh_and_build_ineq t_voc in
                let mode       = VCG.new_open_thid_array_mode fresh_tid [] in
                let ts         = fresh_tid :: t_voc in
                let extra_rho  = E.conj_list
                                   (VCG.gen_rho mode hide_pres false sys ts pc) in
                let antecedent = E.And (mu_n, E.And (extra_rho,diff_conj))in
                let consequent = if hide_pres then
                                   E.disj_list $ List.map (fun n' ->
                                       let p = E.prime_modified antecedent
                                                  (pvd_node_mu pvd n')
                                       in
                                         E.And (p, beta pvd n n')
                                     ) next
                                 else
                                   next_disj in
                let extra_cond = E.Implies (antecedent, consequent)
                in
                  conseq := (n, (pc, E.Local fresh_tid), extra_cond) :: !conseq
              ) pc_list
            ) pvd.pvd_nodes in
*)
  
  
    (* Acceptance *)
    let accept = ref [] in
 (*

    let eSet = Hashtbl.fold (fun e _ s -> EdgeSet.add e s) pvd.pvd_edges 
    EdgeSet.empty in
  
    let _ = List.iter (fun (pS,rS,d) ->
              let sDiff = EdgeSet.diff pS rS in
              let sComp = EdgeSet.diff eSet (EdgeSet.union pS rS) in
              Hashtbl.iter (fun (n1,n2) _ ->
                let t_voc = tvoc pvd n1 [n2] phi_th in
                let mu_n1 = pvd_node_mu pvd n1 in
                let mu_n2' = E.prime $ pvd_node_mu pvd n2 in
                let beta_n1_n2 = beta pvd n1 n2 in
                let delta_n1 = app_delta d n1 in
                let delta_n2' = E.prime_term $ app_delta d n2 in
                let s = E.term_sort delta_n1 in
                let less = cons_less_relation s delta_n2' delta_n1 in
                List.iter (fun pc ->
                  List.iter (fun i ->
                    let mode      = VCG.new_open_thid_array_mode i [] in
                    let rho       = E.conj_list
                                     (VCG.gen_rho mode hide_pres false sys t_voc pc)in
                    let modif     = E.And(rho, beta_n1_n2) in
                    let mu_n2'    = if hide_pres then
                                      E.prime_modified modif (pvd_node_mu pvd n2)
                                    else
                                      mu_n2' in
                    let delta_n2' = if hide_pres then
                                      E.prime_modified_term modif (app_delta d n2)
                                    else
                                      delta_n2' in
                    let less      = if hide_pres then
                                      cons_less_relation s delta_n2' delta_n1
                                    else
                                      less in
                    let eq        = E.eq_term delta_n2' delta_n1 in
  
                    let pre       = E.conj_list [rho;mu_n1;mu_n2';beta_n1_n2]
                    in
                      if EdgeSet.mem (n1,n2) sDiff then
                        let cond = E.Implies(pre, E.Or(less,eq)) in
                          accept := cond :: !accept
                      else if EdgeSet.mem (n1,n2) sComp then
                        let cond = E.Implies(pre, less) in
                          accept := cond :: !accept
                      else
                        ()
                  ) t_voc;
                  let (fresh_tid, diff_conj) = gen_fresh_and_build_ineq t_voc in
                  let mode      = VCG.new_open_thid_array_mode fresh_tid [] in
                  let ts        = fresh_tid :: t_voc in
                  let extra_rho = E.conj_list
                                    (VCG.gen_rho mode hide_pres false sys ts pc) in
                  let modif   = E.conj_list [extra_rho;diff_conj;beta_n1_n2] in
                  let mu_n2'    = if hide_pres then
                                    E.prime_modified modif (pvd_node_mu pvd n2)
                                  else
                                    mu_n2' in
                  let delta_n2' = if hide_pres then
                                    E.prime_modified_term modif (app_delta d n2)
                                  else
                                    delta_n2' in
                  let less      = if hide_pres then
                                    cons_less_relation s delta_n2' delta_n1
                                  else
                                    less in
                  let eq        = E.eq_term delta_n2' delta_n1 in
                  let pre = E.conj_list [extra_rho;diff_conj;
                                            mu_n1;mu_n2';beta_n1_n2] in
                  if EdgeSet.mem (n1,n2) sDiff then
                    let extra_cond = E.Implies (pre, E.Or(less,eq)) in
                      accept := extra_cond :: !accept
                  else if EdgeSet.mem (n1,n2) sComp then
                    let extra_cond = E.Implies (pre, less) in
                      accept := extra_cond :: !accept
                  else
                    ()
                ) pc_list
              ) pvd.pvd_edges
            ) pvd.pvd_accept in
  *)
  
    (* Fairness *)
    let fair   = ref [] in

(*
    let _ = Hashtbl.iter (fun (n1,n2) (_,edge_tau_list) ->
              let e             = (n1,n2) in
              let n1_mu         = pvd_node_mu pvd n1
              in
                List.iter (fun t ->
                  let (pc,th_opt) = match t with
                                      (pc,E.Local th_opt) -> (pc, th_opt)
                                    | (_, E.Shared) -> raise(Unparametrized_transition) in
                  let mode        = VCG.new_open_thid_array_mode th_opt [] in
                  let ts          = [th_opt] in
                  let tau_rho     = E.conj_list
                                      (VCG.gen_rho mode hide_pres false sys ts pc) in
                  let t_next      = Hashtbl.find_all pvd.pvd_tau (n1,t) in
                  let next_list   = List.map (pvd_node_mu pvd) t_next in
                  let next_mu     = E.disj_list next_list in
                  (* Preservation of box parameters *)
                  let box_params  = node_box_param_list pvd.pvd_box_tbl n1 in
                  let box_pres    = List.map (fun t ->
                                      E.eq_tid (E.prime_tid t) t
                                    ) box_params in
                  (* Preservation of box parameters *)
                  let pre_fair_1  = E.conj_list (n1_mu::box_pres) in
                  let pre_fair_2  = E.conj_list (n1_mu::tau_rho::box_pres) in
                  let next_mu'    = if hide_pres then
                                      E.prime_modified pre_fair_2 next_mu
                                    else
                                      E.prime next_mu
                  in
                    fair := (e,t,E.Implies (pre_fair_1, enabled sys t)) ::
                            (e,t,E.Implies (pre_fair_2, next_mu')) ::
                            !fair
                ) edge_tau_list
            ) pvd.pvd_edges in
  
*)
    (* Satisfaction *)
    let satisf = [] in
  
    (* Clean heap occurrences? *)
    let _ = if Sys.mem_var (Sys.get_global sys) Sys.heap_name then
      VCG.enable_tll_dp ()
    else
      VCG.enable_num_dp () in
  
    (* Result *)
    let res = { initialization = init;
                consecution    = !conseq;
                acceptance     = !accept;
                fairness       = !fair;
                satisfaction   = satisf;
              }
    in
      post_process res
  
  
  (* Verification conditions check *)
  
  
  let check_pvd (sys : Sys.system_t) (pvd : pvd_t) : bool =
    let dec_proc = VCG.apply_dp_on_table in
    (* Support auxiliary function *)
    let support_if_needed already_valid tbl label =
      if already_valid then true
      else
        let _ = print_endline ("Adding support for: " ^ label) in
        let new_tbl = VCG.support_formula_table pvd.pvd_support tbl in
          dec_proc new_tbl (label ^ " with support:\n")
    in
 
    (* Erases output file, if exists *)
    let _ = if OcamlSys.file_exists (VCG.out_file ()) then
              OcamlSys.remove (VCG.out_file ()) in
  
    (* Verification conditions generation *)
    let new_sys = VCG.filter_system sys in
  
    let vc  = gen_pvd_vc (VCG.hide_pres ()) new_sys pvd in
  
    let vc_info      = { VCG.pc = 0;
                         VCG.smp = VCG.cutoff();
                         VCG.supps = [];
                         VCG.try_pos = true; } in
    let init_tbl     = VCG.formula_list_to_table
                         [(vc.initialization, vc_info)] in

    let cons_tbl     = VCG.formula_list_to_table $
                         List.map (fun (_,_,f) -> (f,vc_info)) vc.consecution in
  (*
    let accept_tbl   = VCG.formula_list_to_table vc.acceptance in
  *)
    let fair_tbl     = VCG.formula_list_to_table $
                         List.map (fun (_,_,f) -> (f,vc_info)) vc.fairness in
  (*
    let satis_tbl    = VCG.formula_list_to_table vc.satisfaction in
  *)
    let _            = print_endline "Analyzing initialization..." in
    let init_res     = dec_proc init_tbl "Initialization:\n" in
    let _            = print_endline "Analyzing consecution..." in
    let cons_res     = dec_proc cons_tbl "\n\nConsecution:\n" in
  (*
    let _            = print_endline "Analyzing acceptance..." in
    let accept_res   = dec_proc accept_tbl info "\n\nAcceptance:\n" in
  *)
    let _            = print_endline "Analyzing fairness..." in
    let fair_res     = dec_proc fair_tbl "\n\nFairness:\n" in
  (*
    let _            = print_endline "Analyzing satisfaction..." in
    let satis_res    = dec_proc satis_tbl info "\n\nSatisfaction:\n" in
  *)
    let all_verified = init_res && cons_res (* && accept_res *) &&
                       fair_res (* && satis_res *)
    in
      if all_verified then begin
        print_endline "All VCs verified. No need for support...";
        true
      end else begin
        let _ = print_endline "---- Adding support to unverified VCs..." in
        let init_res' = support_if_needed init_res init_tbl "Initialization" in
        let cons_res' = support_if_needed cons_res cons_tbl "Consecution" in
        (* let accept_res' = support_if_needed accept_res accept_tbl "Acceptance" in *)
        let fair_res' = support_if_needed fair_res fair_tbl "Fairness" in
        (* let satis_res' = support_if_needed satis_res satis_tbl "Satisfaction" in *)
        init_res' && cons_res' (*&& accept_res' *) && fair_res' (* && satis_res'*)
      end
end
