
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

module Make(PType: PoolType) =
  struct
    type elt = PType.t
    type t = (elt, int) Hashtbl.t

    let empty : t =
      Hashtbl.create 30

    let tag (p:t) (e:elt) : int =
      if Hashtbl.mem p e then
        Hashtbl.find p e
      else
        let c = Hashtbl.length p in
        let _ = Hashtbl.add p e c in
          c
  end
