
let verbose_enabled = ref false
let verbose_level = ref 999


let enable_verbose () =
  verbose_enabled := true


let enable_verbose_up_to (l:int) =
  enable_verbose(); verbose_level := l


let disable_verbose () =
  verbose_enabled := false


let flush () =
  if !verbose_enabled then Pervasives.flush Pervasives.stdout

let verb (msg : ('a, Format.formatter, unit) format) : 'a  =
  if !verbose_enabled then Format.printf msg
  else Format.ifprintf Format.std_formatter msg


let verbl (l:int) (msg : ('a, Format.formatter, unit) format) : 'a  =
  if (!verbose_enabled && l <= !verbose_level) then Format.printf msg
  else Format.ifprintf Format.std_formatter msg


let is_verbose_enabled () : bool =
  !verbose_enabled

