(******************************************************************************)
(* @file LeapDebug.mli                                                        *)
(* Provides functions for debugging.                                          *)
(*                                                                            *)
(******************************************************************************)

val enable_debug : unit -> unit
val disable_debug : unit -> unit
val flush : unit -> unit

val debug : ('a, Format.formatter, unit) format -> 'a

val is_debug_enabled : unit -> bool
