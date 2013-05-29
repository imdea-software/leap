type 'a t = int array

exception Out_of_bounds
exception Diff_length

let int_size = 32

let empty (n:int) : 'a t =
  Array.make (n/int_size + 1) 0


let copy (v:'a t) : 'a t =
  Array.copy v


let add (f:'a -> int) (v:'a t) (a:'a) : unit =
  try
    let id = f a in
    let arr_id = id / int_size in
    let mask = 1 lsl (id mod int_size) in
      v.(arr_id) <- (mask lor (v.(arr_id)))
  with _ -> raise(Out_of_bounds)


let apply_bin_op ((op):int -> int -> int) (v:'a t) (w:'a t) : 'a t =
  let size = Array.length v in
  let new_arr = Array.make size 0 in
  try
    for i = 0 to (size-1) do
      new_arr.(i) <- (op v.(i) w.(i))
    done;
    new_arr
  with _ -> raise(Diff_length)


let apply_unary_op ((op):int -> int) (v:'a t) : 'a t =
  let size = (Array.length v) in
  let new_arr = Array.make size 0 in
  let _ = for i = 0 to (size-1) do
            new_arr.(i) <- (op v.(i))
          done in
    new_arr


let union (v:'a t) (w:'a t) : 'a t =
  apply_bin_op (lor) v w


let intersect (v:'a t) (w:'a t) : 'a t =
  apply_bin_op (land) v w


let complement (v:'a t) : 'a t =
  apply_unary_op lnot v


let disjoint (v:'a t) (w:'a t) : bool =
  try
    let res = ref true in
    for i = 0 to (Array.length v) - 1 do
      res := !res && (v.(i) land w.(i) = 0)
    done;
    !res
  with _ -> raise(Diff_length)


let to_str (v:'a t) : string =
  let print_int (i:int) : string =
    let buf = ref "" in
    let _ = for j = 0 to (int_size - 1) do
              if (i land (1 lsl j) = 0) then
                buf := "0" ^ !buf
              else
                buf := "1" ^ !buf
            done in
      !buf in
  Array.fold_left (fun str i ->
    (print_int i) ^ str
  ) "" v
