
module type S =
  sig

    type term
    type formula
    module V : Variable.S
    type t

    val new_norm : formula -> t

    val add_term_map : t -> term -> V.t -> unit
    val remove_term_map : t -> term -> unit
    val find_term_map : t -> term -> V.t
    val term_map_size : t -> int
    val iter_term_map : (term -> V.t -> unit) -> t -> unit

    val add_proc_term_map : t -> term -> V.t -> unit
    val find_proc_term : t -> term -> V.t

    val gen_fresh_var : t -> V.sort -> V.t

  end


module Make (Opt:NormSpec.S) =
  struct

    type atom = Opt.norm_atom
    type term = Opt.norm_term
    type formula = Opt.norm_formula
    module V = Opt.VS

    type t =
      {
        term_map : (term, V.t) Hashtbl.t ;
        processed_term_map : (term, V.t) Hashtbl.t ;
        fresh_gen_info : V.fresh_var_gen_t ;
      }


    let new_fresh_gen_from_formula (phi:formula) : V.fresh_var_gen_t =
      let vars = V.VarSet.fold (fun v s ->
                   V.VarIdSet.add (V.id v) s
                 ) (Opt.norm_varset phi) V.VarIdSet.empty in
      V.new_fresh_gen vars



    let new_norm (phi:formula) : t =
      {
        term_map = Hashtbl.create 10 ;
        processed_term_map = Hashtbl.create 10 ;
        fresh_gen_info = new_fresh_gen_from_formula phi ;
      }



    let add_term_map (info:t) (t:term) (v:V.t) : unit =
      Hashtbl.add info.term_map t v

    let remove_term_map (info:t) (t:term) : unit =
      Hashtbl.remove info.term_map t

    let find_term_map (info:t) (t:term) : V.t =
      Hashtbl.find info.term_map t

    let term_map_size (info:t) : int =
      Hashtbl.length info.term_map

    let iter_term_map (f:term -> V.t -> unit) (info:t) : unit =
      Hashtbl.iter f info.term_map


    let add_proc_term_map (info:t) (t:term) (v:V.t) : unit =
      Hashtbl.add info.processed_term_map t v

    let find_proc_term (info:t) (t:term) : V.t =
      Hashtbl.find info.processed_term_map t


    let gen_fresh_var (info:t) (s:V.sort) : V.t =
      V.gen_fresh_var Opt.norm_fresh_vname (Opt.norm_fresh_vinfo()) info.fresh_gen_info s

      

  end

