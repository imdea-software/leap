
exception Unknown_dp_str of string

(** Declares all possibilities of available decision procedures *)
type t =
  | NoDP
  | Loc
  | Num
  | Tll
  | Tsl
  | Tslk of int

val def_dp_list : t list
(** The list of default decision procedures available to the user *)


val to_str : t -> string
(** [to_str dp] returns a string representation of [dp] *)


val from_str : string -> t
(** [from_str s] parses [s] and returns the decision procedure it represents. It
    it cannot match any decision procedure, then [NoDP] is returned. *)


val get_tslk_param : t -> int
(** [get_tslk_param dp] returns the TSLK parameter, if [dp] is tslk. Otherwise,
    it returns 1. *)
