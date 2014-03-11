
type results_t =int * int * int * int * int * int * int * int *
                int * int * int * int * string

type vc_status = NotVerified | NotValid | IsValid | Unneeded

type status_t = Unverified | Invalid | Valid of DP.t

val report_generated_vcs : Tactics.vc_info list -> int -> unit
val report_system : System.t -> unit
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
                             (int * int * int) -> Tag.f_tag list ->
                             bool -> (string * float) list -> unit


val report_vc_header : int -> Tactics.vc_info -> int -> unit
val report_vc_tail : int -> Result.info_t -> Result.info_t list -> DP.call_tbl_t -> unit
val report_obligation_tail : Result.status_t -> float -> unit
val report_summary : int -> Result.info_t list -> DP.call_tbl_t -> unit


module type S =
  sig
    type formula

    type inv_t = System.var_table_t * Tag.f_tag option * formula

    val report_inv_cand : formula -> unit
    val report_sup_inv : inv_t list -> unit
    val report_gen_sup_inv : formula -> unit
    val report_obligation_header : int -> formula -> unit
  end

module Make (E:GenericExpression.S) : S
  with type formula = E.formula
