(******************************************************************************)
(* @file LeapDebug.mli                                                        *)
(* Provides functions for debugging.                                          *)
(*                                                                            *)
(******************************************************************************)

val enable_verbose : unit -> unit
val enable_verbose_up_to : int -> unit
val disable_verbose : unit -> unit
val flush : unit -> unit

val verb : ('a, Format.formatter, unit) format -> 'a
val verbl : int -> ('a, Format.formatter, unit) format -> 'a
val verbstr : string -> unit

val is_verbose_enabled : unit -> bool
