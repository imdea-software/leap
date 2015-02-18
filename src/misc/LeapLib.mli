(* LeapLib.mli *)

exception Empty_list;;


(** Timeing wrapper to time portions of code.  Basic usage:
    
    [let mytimer = new timer in
    ...
    mytimer#start;
    ... code to time ...
    mytimer#stop;
    
    Printf.printf "Elapsed time: %f" mytimer#elapsed_time]
  
  {Note:} If method [elapsed_time] is called before the timer is stopped,
  it returns the partial elapsed time without stopping the timer.
*)
class timer : object 
  method start : unit
  method stop : unit
  method elapsed_time : float
    (** @return the execution time of the wrapped code, 
        including the execution time for children processes. *)  
  
  method proc_elapsed_time : float
    (** @return the execution time of the wrapped code,
        excluding any other execution time. *)

  method timeIt : ('a -> 'b) -> 'a -> 'b
    (** [timeIt f x] computes [f x] and times it. 
        
        @return [f x]
    *)
end

val ($) : ('a -> 'b) -> 'a -> 'b
val (<<) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
val (>>) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val id : 'a -> 'a

val lastElem : 'a list -> 'a
val first_n : int -> 'a list -> 'a list
val rangeList : int -> int -> int list
val insert_at : 'a -> 'a list -> int -> 'a list
val list_of : int -> 'a -> 'a list
(** [split_at xs a] splits [xs] into two lists. The first list contains all
    elements in [xs] until [a] inclusive. The second list contains all
    elements in [xs] coming after [a]. If [a] is not in [xs] then [xs] is
    returned as first list and the second list is returned empty *)
val split_at : 'a list -> 'a -> 'a list * 'a list
val apply_if_not_empty : ('a list -> 'b) -> 'b -> 'a list -> 'b
val match_last_n_chars : int -> string -> string -> bool
val comb           : 'a list -> int -> 'a list list
val comb_range     : 'a list -> int -> int -> 'a list list
val mid_comb_tuple : 'a list -> int -> int -> ('a list * 'a list) list
val mid_comb       : 'a list -> int -> 'a -> int -> 'a list list
val choose         : 'a list -> int -> 'a list list
val choose_range   : 'a list -> int -> int -> 'a list list

val concat_map     : string -> ('a -> string) -> 'a list -> string

(** [print_list f l] prints the list [l] after applying [f] to each argument. *)
val print_list     : ('a -> string) -> 'a list -> string

(* Returns the used memory expressed in bytes *)
val used_mem       : unit -> int
val report_mem     : unit -> string

val _debug_ : bool ref

module Option :
sig

  val default : 'a -> 'a option -> 'a
  val map_default : ('a -> 'b) -> 'b -> 'a option -> 'b
  val lift : ('a -> 'b) -> 'a option -> 'b option

end

class counter : int -> object 
  method reset : unit
  method get : int 
  method incr : unit 
end

