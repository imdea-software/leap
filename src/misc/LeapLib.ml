(* LeapLib.ml *)


exception Empty_list
exception Negative_position of int
exception Negative_number of int


(* Functions related with time *)
class timer = object (self)
  val mutable started = Unix.times ()
  val mutable ended = Unix.times ()
  val mutable running = false
  
  method start =
    running <- true;
    started <- Unix.times()
  
  method stop =
    ended <- Unix.times();
    running <- false              
  
  method elapsed_time =
    let ended' = if running then Unix.times() else ended in
    (ended'.Unix.tms_utime +. ended'.Unix.tms_cutime) 
      -. (started.Unix.tms_utime +. started.Unix.tms_cutime)
      
  method proc_elapsed_time =
    let ended' = if running then Unix.times() else ended in
    ended'.Unix.tms_utime -. started.Unix.tms_utime
  
  method timeIt : 'a 'b. ('a -> 'b) -> 'a -> 'b = fun f x ->
    self#start;
    let f_x = f x in
    self#stop;
    f_x
end

(* Auxiliary composition *)
let ($) f v = f v

(* Identity function *)
let id x = x

let (<<) f g = fun x -> f (g x)

let (>>) f g = fun x -> g (f x)

let rec rangeList l u = if u < l then [] else l::(rangeList (l+1) u)

let rec insert_at x l i =
  if ( i = 0 ) then x::(List.tl l) else
  match l with
    []  -> []
  | h::t  -> h::( insert_at x t ( i - 1 ) )


let rec list_of n e =
  if n = 0 then
    []
  else if n < 0 then
    raise(Negative_number n)
  else
    e::(list_of (n-1) e)


let split_at (xs:'a list) (a:'a) : 'a list * 'a list =
  let found = ref false in
  List.fold_left (fun (preds,succs) e ->
    if !found then
      (preds,succs @ [e])
    else begin
      found := (e = a);
      (preds @ [e], succs)
    end
  ) ([],[]) xs


let rec lastElem l = match l with
                       [] -> raise(Empty_list)
                     | x::[] -> x
                     | _::xs -> lastElem xs


let rec first_n n lst =
  if n < 0 then
    raise(Negative_position n)
  else
    match (n,lst) with
    | (0,_) -> []
    | (n,[]) -> []
    | (n,x::xs) -> x :: first_n (n-1) xs


let apply_if_not_empty (f:'a list -> 'b) (def:'b) (xs:'a list) : 'b =
  match xs with
    _::_ -> f xs
  | []   -> def

let match_last_n_chars (n:int) (exp:string) (str:string) : bool =
  let len = String.length str in
  let suffix = String.sub str (len - n) n in
  (String.lowercase exp) = (String.lowercase suffix)

let rec comb (xs:'a list) (n:int) : 'a list list =
  let _ = assert (n >= 0) in
  match n with
    0 -> [[]]
  | 1 -> List.map (fun x -> [x]) xs
  | _ -> List.flatten $
           List.map (fun a -> List.map (fun x -> a::x) (comb xs (n-1))) xs


let comb_range (xs:'a list) (n:int) (m:int) : 'a list list =
    List.flatten $ List.map (comb xs) (rangeList n m)


let mid_comb_tuple (xs:'a list) (size:int) (pos:int) : ('a list * 'a list) list=  
  let _ = assert (0 <= pos && pos < size)
  in
    List.flatten $
      List.map (fun pre ->
        List.map (fun post ->
          (pre, post)
        ) (comb xs (size - pos - 1))
      ) (comb xs pos)


let mid_comb (xs:'a list) (size:int) (elem:'a) (pos:int) : 'a list list =
  let _ = assert (0 <= pos && pos < size) in
  let pos_list = mid_comb_tuple xs size pos
  in
    List.map (fun (pre,post) -> pre @ [elem] @ post) pos_list


let rec choose (xs:'a list) (n:int) : 'a list list =
  match (xs,n) with
    (_,0) -> [[]]
  | ([],k) -> []
  | (y::ys,k) -> List.map (fun zs -> y::zs) (choose ys (k-1)) @ choose ys k


let choose_range (xs:'a list) (n:int) (m:int) : 'a list list =
  List.flatten $ List.map (choose xs) (rangeList n m)


let concat_map (sep:string) (f:'a -> string) (xs:'a list) : string =
  String.concat sep (List.map f xs)


let print_list (print_f:'a -> string) (xs:'a list) : string =
  match xs with
    []    -> ""
  | y::[] -> print_f y
  | y::ys -> List.fold_left (fun str elem ->
               str ^ ", " ^ (print_f elem)
             ) (print_f y) ys

let used_mem () : int =
  let stat = Gc.stat() in
  let words = stat.Gc.minor_words +.
              stat.Gc.major_words -.
              stat.Gc.promoted_words in
  (int_of_float words) * Sys.word_size


let report_mem () : string =
  let size = used_mem () in
  if size < 1024 then
    (string_of_int size) ^ " B"
  else if 1024 <= size && size < 1048576 then
    (string_of_int (size/1024)) ^ " KB"
  else
    (string_of_int (size/1048576)) ^ " MB"


let human_readable_byte_count () : string =
  let bytes = Gc.allocated_bytes () in
  let unit = 1024. in
  if bytes < unit then Format.sprintf "%.0fB" bytes
  else
    let exp = int_of_float (log bytes /. log unit) in
    Format.sprintf "%.2f%sB" (bytes /. (unit ** (float_of_int exp)))
      (match (exp-1) with
      | 0 -> "K" | 1 -> "M" | 2 -> "G"
      | 3 -> "T" | 4 -> "P" | 5 -> "E"
      | _ -> "Ouch! This number is too big!")


let _debug_ = ref false


module Option =
struct

  let default d o =
    match o with
      Some v -> v
    | None -> d


  let map_default f b o =
    match o with
      Some v -> f v
    | None -> b


  let lift f o =
    match o with
      Some v -> Some (f v)
    | None -> None
  
end

(** A simple counter. *)
class counter i = object
  val mutable n = i
  method reset = n <- i
  method incr = n <- n + 1
  method get = n
end


