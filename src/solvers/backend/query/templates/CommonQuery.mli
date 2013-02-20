module type COMMON_QUERY =
sig

  val set_prog_lines : int -> unit
  (** [set_prog_lines n] sets the number of program lines to [n]. *)

  val get_sort_map : unit -> GenericModel.sort_map_t
  (** Gets the declared mapping from elements to sorts *)

end
