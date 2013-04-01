
open NumQuery
open TllQuery
open TslkQuery

(** [set_smt_usage b] flags the usage of SMT-LIB translation if available
    to [b] *)
val set_smt_usage : bool -> unit


(** [get_num_query id] returns an appropriate numeric query module for the
    backend solver identified by [id] depending on the status previously set
    through a call to [set_smt_usage] *)
val get_num_query : string -> (module NUM_QUERY)


(** [get_tll_query id] returns an appropriate TLL query module for the
    backend solver identified by [id] depending on the status previously set
    through a call to [set_smt_usage] *)
val get_tll_query : string -> (module TLL_QUERY)


(** [get_tslk_query id] returns an appropriate TSLK query module for the
    backend solver identified by [id] depending on the status previously set
    through a call to [set_smt_usage] *)
(*val get_tslk_query : string -> (module Z3TslkQuery.Make) *)
