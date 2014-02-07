
module type S =
  sig
    type t
    val atom_to_str : t -> string
  end
