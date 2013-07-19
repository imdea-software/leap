
(** [set_logFile filename] configures [filename] to be the log file. *)
val set_logFile : string -> unit

(** [get_logFile ()] returns the name of the current log file *)
val get_logFile : unit -> string

(** [print label str] prints [str] to the current log file using [label]
    to label the entry. *)
val print : string -> string -> unit

(** [print_ocaml str] prints [str] into the current log file using "ocaml"
    as label *)
val print_ocaml : string -> unit

(** [print_cfg str] prints [str] into the current log file using "prog 
    configuration" as label *)
val print_cfg : string -> unit
