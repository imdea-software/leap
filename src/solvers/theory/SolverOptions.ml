
type t =
  {
    mutable lines : int;
    mutable cutoff_strategy : Smp.cutoff_strategy_t;
    mutable use_quantifiers : bool;
    mutable use_arrangement_generator : bool;
  }

(** The type of the theory solver options *)

let new_opt () : t =
  {
    lines = 1;
    cutoff_strategy = Smp.Dnf;
    use_quantifiers = false;
    use_arrangement_generator = false;
  }
  

let set_lines (opt:t) (l:int) : unit =
  opt.lines <- l

let set_cutoff_strategy (opt:t) (co:Smp.cutoff_strategy_t) : unit =
  opt.cutoff_strategy <- co

let set_use_quantifiers (opt:t) (b:bool) : unit =
  opt.use_quantifiers <- b

let set_use_arrangement_generator (opt:t) (b:bool) : unit =
  opt.use_arrangement_generator <- b

let lines (opt:t) : int =
  opt.lines

let cutoff_strategy (opt:t) : Smp.cutoff_strategy_t =
  opt.cutoff_strategy

let use_quantifiers (opt:t) : bool =
  opt.use_quantifiers

let use_arrangement_generator (opt:t) : bool =
  opt.use_arrangement_generator
