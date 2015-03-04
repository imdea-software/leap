
type t = Pos | Neg | Both


let invert (p:t) : t =
  match p with
  | Pos  -> Neg
  | Neg  -> Pos
  | Both -> Both


let is_pos (p:t) : bool =
  p = Pos

let is_neg (p:t) : bool =
  p = Neg



