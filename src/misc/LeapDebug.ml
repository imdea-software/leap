(******************************************************************************)
(* @file LeapDebug.ml                                                         *)
(* Provides functions for debugging.                                          *)
(*                                                                            *)
(******************************************************************************)


let debug_enabled = ref false

let enable_debug () = debug_enabled := true
let disable_debug () = debug_enabled := false
let flush () = if !debug_enabled then
  Pervasives.flush Pervasives.stderr

let debug (msg : ('a, Format.formatter, unit) format) : 'a  =
  if !debug_enabled then Format.eprintf msg
  else Format.ifprintf Format.err_formatter msg

let is_debug_enabled () : bool =
  !debug_enabled

let _testing_ : bool ref = ref false

let _testing_smp_ () : ModelSize.t =
  let ms = ModelSize.create () in
  ModelSize.set ms ModelSize.Addr 10;
  ModelSize.set ms ModelSize.Elem 5;
  ModelSize.set ms ModelSize.Tid 5;
  ms
