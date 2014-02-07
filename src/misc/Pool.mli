
module type PoolType =
  sig
    type t
    val compare : t -> t -> int
  end

module type S =
  sig
    type elt
    type t

    val empty : t
    val tag   : t -> elt -> int
  end

module Make (PType:PoolType) : S with type elt = PType.t

