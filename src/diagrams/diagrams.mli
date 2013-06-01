(* File Diagrams.mli *)

(* Type declarations *)
type trans_id_t
type trans_t
type node_t
type node_id_t
type box_id_t = int
type box_t
type edge_type_t = Normal | Large
type edge_pair_t
type edge_info_t
type edge_t
type acceptance_pair_t
type delta_range_t =
  | Single of node_id_t
  | Range of node_id_t * node_id_t
  | Default
type delta_fun_t = (node_id_t, Expression.term) Hashtbl.t
type acceptance_list_t
type vd_t
type pvd_t
type vd_vc_t

(* EdgeSet export *)
module EdgeSet : Set.S with type elt = edge_pair_t

(* Configuration *)
val initNodeNum   : int
val initEdgeNum   : int
val defaultNodeId : node_id_t

(* Printig functions *)
module PP : sig
  val node_id_to_str : node_id_t -> string
  val vd_to_str : vd_t -> string
  val vc_to_str : vd_vc_t -> string
end

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

module Make : functor (VCG : VCGen.S) -> S
