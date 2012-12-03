
type inv_t = System.var_table_t * Tag.f_tag option * Expression.formula
type results_t =int * int * int * int * int * int * int * int *
                int * int * int * int * string

type vc_status = Unverified | NotValid | Valid | Unneeded

val report_inv_cand : Expression.formula -> unit
val report_system : System.system_t -> unit
val report_sup_inv : inv_t list -> unit
val report_gen_sup_inv : Expression.formula -> unit
val report_results : results_t -> unit

val report_vc_run_header : unit -> unit
val report_vc_run : int -> vc_status -> float ->
                           vc_status -> float ->
                           vc_status -> float ->
                           vc_status -> float ->
                           vc_status -> float -> string -> string -> unit
val report_analysis_time : float -> unit
val report_labels : System.label_table_t -> unit

(* TODO: I must extend this function to get values from TSLK and TSL *)
val report_details_to_file : string -> string -> string ->
                             (int * Expression.pc_t * int) -> Tag.f_tag list ->
                             bool -> (string * float) list -> unit
