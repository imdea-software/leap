
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


let verb (msg : ('a, Format.formatter, unit) format) : 'a =
  if !verbose_enabled then
    let res = Format.printf msg in
      Pervasives.flush Pervasives.stdout; res
  else
    Format.ifprintf Format.std_formatter msg


let verbl (l:int) (msg : ('a, Format.formatter, unit) format) : 'a  =
  if (!verbose_enabled && l <= !verbose_level) then
    let res = Format.printf msg in
      Pervasives.flush Pervasives.stdout; res
  else
    Format.ifprintf Format.std_formatter msg


let verbstr (msg:string) : unit =
  if !verbose_enabled then
    Pervasives.print_string msg
  else
    ()


let is_verbose_enabled () : bool =
  !verbose_enabled

