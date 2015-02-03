
val sat_to_valid : Sat.t -> Valid.t
(** [sat_to_valid r] converts [r] from satisfiability to validity. *)

val valid_to_sat : Valid.t -> Sat.t
(** [valid_to_sat r] converts [r] from validity to satisfiability. *)
