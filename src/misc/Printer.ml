let generic (aprinter:'a -> string) (x:'a) : unit =
  Printf.printf "%s" (aprinter x)

