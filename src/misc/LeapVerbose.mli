(******************************************************************************)
(* @file LeapDebug.mli                                                        *)
(* Provides functions for debugging.                                          *)
(*                                                                            *)
(******************************************************************************)

val _SHORT_INFO : int
val _LONG_INFO : int


val enable_verbose : unit -> unit
val enable_verbose_up_to : int -> unit
val disable_verbose : unit -> unit
val flush : unit -> unit

val verb : ('a, Format.formatter, unit) format -> 'a
val verbl : int -> ('a, Format.formatter, unit) format -> 'a
val verbstr : string -> unit
val verblstr : int -> string -> unit

val is_verbose_enabled : unit -> bool
val is_verbose_level_enabled : int -> bool
