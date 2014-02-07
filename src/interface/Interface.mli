(* Interface.mli *)


module File :
sig
  val readFile : string -> string
  val writeFile : string -> string -> unit
  val readChannel : Pervasives.in_channel -> string

end


module Err :
sig

  val msg  : string -> string -> unit
  val smsg : string -> string -> unit

end

module Msg :
sig
  val div : string -> string
  val info : string -> string -> string
end
