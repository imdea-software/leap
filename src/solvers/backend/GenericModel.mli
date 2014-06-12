
type id = string

type sort = string

type typeDecl = Const of sort | Fun of sort list * sort list

type sort_map_t

(** Type for variables in the model *)
type var = Var of id | Function of id * (id option) list

type vals = string

type value = Single of string | Record of (id * (id * vals) list)

type fun_t = ((id option) list, value) Hashtbl.t

type t

(* sort names *)
val bool_s    : string
val int_s     : string
val addr_s    : string
val set_s     : string
val elem_s    : string
val tid_s     : string
val cell_s    : string
val setth_s   : string
val setelem_s : string
val path_s    : string
val level_s   : string
val heap_s    : string
val unk_s     : string
val loc_s     : string

(* sort_map functions *)
val new_sort_map : unit -> sort_map_t
(** Creates a new empty sort map *)

val clear_sort_map : sort_map_t -> unit
(** [clear_sort_map sm] clears the information in [sm] *)

val copy_sort_map : sort_map_t -> sort_map_t
(** [copy_sort_map sm] returns a duplicated of [sm] *)

val sm_decl_const : sort_map_t -> id -> sort -> unit
(** [sm_decl_const m i s] declares in the sort map [m] that id [i] has
     sort [s] *)

val sm_decl_fun : sort_map_t -> id -> sort list -> sort list -> unit
(** [sm_decl_fun m i ds cs] declares in the sort map [m] that id [i] has
     sort of function from [ds] to [cs] *)

val sm_dom : sort_map_t -> id list
(** [sm_dom sm] returns the list of id in the domain of [sm] *)

val sm_codom : sort_map_t -> typeDecl list
(** [sm_dom sm] returns the list of types declared in the codomain of [sm] *)


val sm_dom_of_type : sort_map_t -> typeDecl -> id list
(** [sm_dom_of_type sm t] returns the list of identifiers with type [t]
    in [sm] *)

(* Generic model functions *)

val new_model : unit -> t
(** [new_model ()] return a new empty generic model *)


val is_empty_model : t -> bool
(** [is_empty_model m] return true if [m] is empty. Otherwise, false. *)


val clear_model : t -> unit
(** [clear_model m] removes all information within model [m] *)


val copy_model : t -> t
(** [copy_model m] returns a new copy of model [m] *)


val decl_const : t -> id -> value -> unit
(** [decl_const m c v] loads into model [m] an assignment of constant [c]
    to value [v] *)

val decl_fun : t -> id -> (id option) list -> value -> unit
(** [decl_const m f ps v] maps into model [m] function [f] with parameters
    [ps] to value [v] *)

val unify : t -> var -> var -> unit
(** [unify m id1 id2] unifies the values associated to [id1] and [id2]
    into model [m], putting them into the same equivalence class *)

val get_const : t -> id -> value
(** [get_const m c] returns the value associated to constant [c]. Raises
    [undefined] if [c] is not defined in [m] *)

val get_fun_def : t -> id -> value option
(** [get_fun_def m f] returns the default value for function [f] in
    model [m] *)

val get_fun : t -> id -> fun_t
(** [get_fun m f] returns the information related to function [f]
    in model [m] *)


val model_to_str : t -> string
(** [model_to_str m] generates a string representation of model [m] *)

val model_with_sorts_to_str : t -> sort_map_t -> string
(** [model_with_sorts_to_str m sm] generates a string representation of
    model [m], using sort map [sm] to order the elements *)

val id_to_str : t -> id -> string
(** [id_to_str m i] searches all definitions of [i] in model [m] and returns
    a string representation of all values *)

val id_list_to_str : t -> id list -> string
(** [id_list_to_str m ids] searches all definitions of identifiers in list [ids]
    in model [m] and returns a string representation of all values *)

val conv_sort : Expression.sort -> sort
(** [conv_sort s] returns the generic model representation of sort [s] *)


val search_type_to_str : t -> sort_map_t -> sort -> string
(** [search_type_to_str m sm s] returns a string representation of all elements
    of sort [s] (in addition to functions from thread identifiers to sort [s])
    in model [m] according to sort map [sm] *)


val search_sets_to_str : t -> sort_map_t -> sort -> string
(** [search_type_to_str m sm s] returns a string representation of all elements
    of sort [s] (in addition to functions from thread identifiers to sort [s])
    in model [m] according to sort map [sm], representing all returning elements
    as sets *)
