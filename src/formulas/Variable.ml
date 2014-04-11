module type S =
  sig
    type t

    type id = string
    type sort
    type info
    type shared_or_local = Shared | Local of t
    type procedure_name  = GlobalScope | Scope of string

    type fresh_var_gen_t
    type subst_t

    module VarIdSet : Set.S with type elt = id
    module VarSet : Set.S with type elt = t

    (**********************)
    (**   Constructors   **)
    (**********************)

    val build : ?fresh:bool ->
                id ->
                sort ->
                bool ->
                shared_or_local ->
                procedure_name ->
                info ->
                t

    val build_global : id -> sort -> info -> t

    val dupp : t -> t



    (****************)
    (**   Getters  **)
    (****************)

    val id : t -> id
    val sort : t -> sort
    val is_primed : t -> bool
    val parameter : t-> shared_or_local
    val scope : t -> procedure_name
    val info : t -> info


    (****************)
    (**   Setters  **)
    (****************)

    val set_sort : t -> sort -> t
    val set_param : t -> shared_or_local -> t
    val set_info : t -> info -> t
    val unparam : t -> t



    (***********************)
    (**  Extra functions  **)
    (***********************)

    val same_var : t -> t -> bool
    val is_local : t -> bool
    val is_global : t -> bool
    val prime : t -> t
    val unprime : t -> t
    val prime_var_id : id -> id
    val is_fresh : t -> bool
    val localize : t -> t
    val localize_var_id : id -> string -> id
    val localize_var_id_with_procedure : id -> procedure_name -> id
    val localize_with_underscore : id -> procedure_name -> id


    (*********************************)
    (**  Fresh variable generators  **)
    (*********************************)

    val new_fresh_gen : VarIdSet.t -> fresh_var_gen_t
    val gen_fresh_var :(sort -> string) -> info -> fresh_var_gen_t -> sort -> t



    (*****************************)
    (**  Variable substitution  **)
    (*****************************)

    val new_subst : unit -> subst_t
    val add_subst : subst_t -> t -> t -> unit
    val subst : subst_t -> t -> t
    val subst_shared_or_local : subst_t -> shared_or_local -> shared_or_local


    (****************************)
    (**  Sets of variable ids  **)
    (****************************)

    val varidset_to_str : VarIdSet.t -> string
    val print_varidset : VarIdSet.t -> unit
    val varidset_from_list : id list -> VarIdSet.t


    (*****************************)
    (**  Lists of variable ids  **)
    (*****************************)

    val varidlist_to_str : id list -> string
    val print_varidlist : id list -> unit


    (***********************************)
    (**  Lists of typed variable ids  **)
    (***********************************)

    val typed_varidlist_to_str  : (sort -> string) -> (id * sort) list -> string
    val print_typed_varidlist : (sort -> string) -> (id * sort) list -> unit


    (*************************)
    (**  Sets of variables  **)
    (*************************)

    val typed_variable_set_to_str : (sort -> string) -> VarSet.t -> string
    val print_typed_variable_set : (sort -> string) -> VarSet.t -> unit
    val varset_of_sort : VarSet.t -> sort -> VarSet.t
    val split_by_sort : VarSet.t -> (sort, VarSet.t) Hashtbl.t
    val find_in_table_sort : (sort, VarSet.t) Hashtbl.t -> sort -> VarSet.t
    val varset_from_list : t list -> VarSet.t

    val varidlist_of_sort :t list -> sort -> id list


    (****************)
    (**  Printers  **)
    (****************)

    val shared_or_local_to_str : shared_or_local -> string
    val procedure_name_to_str : procedure_name -> string
    val to_str : t -> string
    val to_simple_str : t -> string
    val to_full_str : (sort -> string) -> (info -> string) -> t -> string
  end


module Make (VS : VarSpec.S) =
  struct

    type id = string
    type sort = VS.sort_t
    type info = VS.info_t

    type shared_or_local = Shared | Local of t

    and procedure_name  = GlobalScope | Scope of string

    and t =
      {
        id        : id              ;
        sort      : sort            ;
        is_primed : bool            ;
        parameter : shared_or_local ;
        scope     : procedure_name  ;
        fresh     : bool            ;
        info      : info            ;
      }

    type var = t

    module VarIdSet = Set.Make(
      struct
        let compare = Pervasives.compare
        type t = id
      end )
 
    let var_compare (x:t) (y:t) : int =
      let same_var (x:t) (y:t) : bool =
        let is_global (v:t) : bool =
          x.scope = GlobalScope || x.scope = Scope "" in
        is_global x && is_global y &&
        x.id = y.id && x.sort = y.sort && x.parameter = y.parameter &&
        x.is_primed && y.is_primed && x.info = y.info
      in
        if same_var x y then 0
        else Pervasives.compare x y

    module VarSet = Set.Make(
      struct
        let compare = var_compare
        type t = var
      end )

    type fresh_var_gen_t =
      {
        tbl : (sort, int) Hashtbl.t;
        vars : VarIdSet.t;
      }

    type subst_t = (t, t) Hashtbl.t


    (**********************)
    (**   Constructors   **)
    (**********************)

    let build ?(fresh=false)
              (id:id)
              (s:sort)
              (pr:bool)
              (th:shared_or_local)
              (p:procedure_name)
              (info:info) : t =
      {
        id = id;
        sort = s;
        is_primed = pr;
        parameter = th;
        scope = p;
        info = info;
        fresh = fresh;
      }


    let build_global (id:id) (s:sort) (i:info) : t =
      build id s false Shared GlobalScope i


    let dupp (v:t) : t =
      build v.id v.sort v.is_primed v.parameter v.scope v.info ~fresh:(v.fresh)


    (****************)
    (**   Getters  **)
    (****************)


    let id (v:t) : id =
      v.id


    let sort (v:t) : sort =
      v.sort


    (* Not sure if some part uses the second condition of the disjunction *)
    let is_primed (v:t) : bool =
(*      v.is_primed || (Str.string_match (Str.regexp ".+_prime.*") (id v) 0) *)
      v.is_primed


    let parameter (v:t) : shared_or_local =
      v.parameter


    let scope (v:t) : procedure_name =
      v.scope


    let info (v:t) : 'info =
      v.info


    let fresh (v:t) : bool =
      v.fresh



    (****************)
    (**   Setters  **)
    (****************)

    let set_sort (v:t) (s:sort) : t =
      build v.id s v.is_primed v.parameter v.scope v.info ~fresh:v.fresh


    let set_param (v:t) (th:shared_or_local) : t =
      build v.id v.sort v.is_primed th v.scope v.info ~fresh:v.fresh


    let set_info (v:t) (info:info) : t =
      build v.id v.sort v.is_primed v.parameter v.scope info ~fresh:v.fresh


    let unparam (v:t) : t =
      build v.id v.sort v.is_primed Shared v.scope v.info ~fresh:v.fresh




    (***********************)
    (**  Extra functions  **)
    (***********************)

    let same_var (v1:t) (v2:t) : bool =
      var_compare v1 v2 = 0


    let is_local (v:t) : bool =
      match scope v with
      | Scope proc  -> proc <> ""
      | GlobalScope -> false


    let is_global (v:t) : bool =
      not (is_local v)


    let prime (v:t) : t =
      build v.id v.sort true v.parameter v.scope v.info ~fresh:v.fresh


    let unprime (v:t) : t =
      build v.id v.sort false v.parameter v.scope v.info ~fresh:v.fresh


    let prime_var_id (v:id) : id =
      v ^ "'"

    let is_fresh (v:t) : bool =
    (*    Correct way *)
    (*    v.info.fresh *)
      (v.id.[0] = '$' || v.fresh)


    let localize (v:t) : t =
      match v.scope with
      | GlobalScope -> v
      | Scope proc -> build (proc ^"_"^ v.id) v.sort v.is_primed
                            Shared GlobalScope v.info ~fresh:v.fresh


    let localize_var_id (id:id) (p_name:string) : id =
      p_name ^"::"^ id


    let localize_var_id_with_procedure (id:id) (p_name:procedure_name) : id =
      match p_name with
      | GlobalScope -> id
      | Scope "" -> id
      | Scope p -> localize_var_id id p


    let localize_with_underscore (id:id) (p_name:procedure_name) : id =
      match p_name with
      | GlobalScope
      | Scope "" -> id
      | Scope proc  -> proc ^ "_" ^ id


    (*********************************)
    (**  Fresh variable generators  **)
    (*********************************)

    let new_fresh_gen (vset:VarIdSet.t) : fresh_var_gen_t =
      let tbl = Hashtbl.create(20) in
      { tbl = tbl; vars = vset; }


    let gen_fresh_var (sort_to_str:sort -> string)
                      (basic_info:info)
                      (gen:fresh_var_gen_t)
                      (s:sort) : t =
      let var_prefix = "$" ^ sort_to_str s in
      let initial = try
                      Hashtbl.find gen.tbl s
                    with Not_found -> (Hashtbl.add gen.tbl s 1; 1) in
      let rec find n =
        let var_cand_id = Printf.sprintf "%s_%i" var_prefix n in
          if VarIdSet.mem var_cand_id gen.vars then
            find (n+1)
          else
            begin
              Hashtbl.replace gen.tbl s (n+1);
              build var_cand_id s false Shared GlobalScope basic_info ~fresh:true
            end
      in
        find initial



    (*****************************)
    (**  Variable substitution  **)
    (*****************************)

    let new_subst () : subst_t =
      Hashtbl.create 10


    let add_subst (subs:subst_t) (v:t) (v':t) : unit =
      Hashtbl.add subs v v'


    let subst (subs:subst_t) (v:t) : t =
      try
        Hashtbl.find subs v
      with Not_found -> v


    let subst_shared_or_local (subs:subst_t)
                              (th:shared_or_local)
      : shared_or_local =
      match th with
      | Shared -> Shared
      | Local t -> Local (subst subs t)



    (****************************)
    (**  Sets of variable ids  **)
    (****************************)

    let varidset_to_str (varset:VarIdSet.t) : string =
      VarIdSet.fold (fun v str -> str ^ v ^ "\n") varset ""


    let print_varidset (varset:VarIdSet.t) : unit =
      Printer.generic varidset_to_str varset


    let varidset_from_list (xs:id list) : VarIdSet.t =
      List.fold_left (fun s t -> VarIdSet.add t s) (VarIdSet.empty) xs



    (*****************************)
    (**  Lists of variable ids  **)
    (*****************************)

    let varidlist_to_str (varlist:id list) : string =
      List.fold_left (fun v str -> str ^ v ^ "\n") "" varlist


    let print_varidlist (varlist:id list) : unit =
      Printer.generic varidlist_to_str varlist



    (***********************************)
    (**  Lists of typed variable ids  **)
    (***********************************)

    let typed_varidlist_to_str (sort_to_str:sort -> string)
                               (tvarlist:(id * sort) list) : string =
      let pr str (v,s) = (str ^ v ^ ": " ^ (sort_to_str s) ^ "\n") in
        List.fold_left pr "" tvarlist


    let print_typed_varidlist (sort_to_str:sort -> string)
                              (tvarlist:(id * sort) list) : unit =
      Printer.generic (typed_varidlist_to_str sort_to_str) tvarlist



    (*************************)
    (**  Sets of variables  **)
    (*************************)

    let typed_variable_set_to_str (sort_to_str:sort -> string)
                                  (tvarset:VarSet.t) : string =
      let pr v str = (str ^ v.id ^ ": " ^ (sort_to_str v.sort) ^ "\n") in
        VarSet.fold pr tvarset ""

    let print_typed_variable_set (sort_to_str:sort -> string)
                                 (tvarset:VarSet.t) : unit =
      Printer.generic (typed_variable_set_to_str sort_to_str) tvarset


    let varset_of_sort (all:VarSet.t) (s:sort) : VarSet.t =
      let filt v res =
        if (sort v) = s then
          VarSet.add (set_param v Shared) res
        else
          res in
        VarSet.fold filt all VarSet.empty


    let split_by_sort (all:VarSet.t) : (sort, VarSet.t) Hashtbl.t =
      let tbl = Hashtbl.create 10 in
      VarSet.iter (fun v ->
        try
          let set = Hashtbl.find tbl v.sort in
          Hashtbl.replace tbl v.sort (VarSet.add v set)
        with Not_found -> Hashtbl.add tbl v.sort (VarSet.singleton v)
      ) all;
      tbl


    let find_in_table_sort (tbl:(sort, VarSet.t) Hashtbl.t) (s:sort) : VarSet.t =
      try
        Hashtbl.find tbl s
      with Not_found -> VarSet.empty


    let varset_from_list (xs:t list) : VarSet.t =
      List.fold_left (fun s t -> VarSet.add t s) (VarSet.empty) xs



    let varidlist_of_sort (varlist:t list) (s:sort) : id list =
      let is_s v = (v.sort=s) in
      List.map (fun v -> (localize_with_underscore v.id v.scope))
               (List.filter is_s varlist)



    (****************)
    (**  Printers  **)
    (****************)

    let rec shared_or_local_to_str (th:shared_or_local) : string =
      match th with
      | Shared -> ""
      | Local t -> to_str t


    and procedure_name_to_str (p:procedure_name) : string =
      match p with
      | GlobalScope -> ""
      | Scope proc -> proc


    and to_str (v:t) : string =
      let v_str = Printf.sprintf "%s%s"
                    (match v.scope with
                     | GlobalScope -> v.id
                     | Scope proc  -> localize_var_id v.id proc)
                    (match v.parameter with
                     | Shared -> ""
                     | Local t -> "(" ^ to_str t ^ ")")
      in
        if v.is_primed then v_str ^ "'" else v_str


    and to_simple_str (v:t) : string =
      let p_str = match scope v with
        | GlobalScope -> ""
        | Scope proc -> proc ^ "_" in
      let pr_str = if is_primed v then "_prime" else "" in
      let th_str = match parameter v with
        | Shared -> ""
        | Local t -> "_" ^ (to_simple_str t)
      in
        p_str ^ (id v) ^ pr_str ^ th_str


    let to_full_str (sort_to_str:sort -> string)
                    (info_to_str:info -> string)
                    (v:t)
        : string =
      "V " ^ to_str v^ " information\n" ^
      "Id:              " ^id v^ "\n" ^
      "Sort:            " ^sort_to_str (sort v)^ "\n" ^
      "Primed:          " ^if is_primed v then "true" else "false"^ "\n" ^
      "Thread:          " ^ (match v.parameter with | Shared -> "" | Local t -> to_str t) ^ "\n" ^
      "Parent:          " ^ procedure_name_to_str v.scope ^ "\n" ^
      (info_to_str v.info)

  end
