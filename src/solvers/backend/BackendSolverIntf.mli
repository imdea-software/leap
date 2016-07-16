
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


open ExpressionTypes
open NumQuery
open PairsQuery
open TllQuery

module type BackendCommon =
(** Minimum signature for a Backend Solver. *)
sig
  type t
  (** Type for internal data structures. *)
  
  val identifier : string
  (** Unique identifier for this solver. *)

  val reset_calls : unit -> unit
  (** [reset_calls ()] resets the calls counter to [0]. *)
  
  val calls_count : unit -> int
  (** [calls_count ()] returns the number of calls performed to the Solver. *)

  val calls_force_incr : unit -> unit
  (** [calls_force_incr ()] forces to increment by one the number of calls
      performed to the Solver. *)
  
  val check_sat : t -> Sat.t
  (** Tests whether the formula is satisfiable. *)

  val compute_model : bool -> unit
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)

  val get_model : unit -> GenericModel.t
  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
end


module type GeneralBackend =
sig
  type t

  val set_prog_lines : int -> unit
  (** [set_prog_lines n] sets the number of lines of the program to be
      analyzed at [n]. *)
end


module type PosBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support Position Reasoning. *)
sig
  type t
  
  module Pos : 
  (** Translation of Pos expressions. *)
  sig
    include GeneralBackend with type t := t

    module Exp : POSEXP

    val expression : Exp.expression -> t
    (** [expression exp] translates the expression [exp] into its 
        corresponding data structure in the Solver program. *)
  end
end


module type TllBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support TLL. *)
sig
  type t
  
  module Tll :
  (** Translation of TLL expressions. *)
  sig
    module Exp : TLLEXP

    module Query (Q : TLL_QUERY) :
    sig
      include GeneralBackend with type t := t

      val literal_list : bool -> Exp.literal list -> t
      (** [literal_list useq ls] translates the list [ls] of literals into its 
          internal representation. [useq] determines whether quantifiers should
          be used in the generated query. *)
     
      val formula      : Smp.cutoff_strategy_t ->
                         Smp.cutoff_options_t ->
                         bool ->
                         Exp.formula -> t
      (** [formula stat strat useq f] translates the formula [f] following the
          strategy [strat] to compute the SMP cutoff and tactic [stat] to
          decide whether or not to include extra information to help the
          future satisfiability analysis of the formula. [useq] determines 
          whether quantifiers should be used in the generated query. *)

      val conjformula  : bool -> Exp.conjunctive_formula -> t
      (** [conjformula useq f] tranlates the conjunctive formula [f]. [useq]
          determines whether quantifiers should be used in the generated
          query. *)

      val sort_map : unit -> GenericModel.sort_map_t
      (** [sort_map ()] returns the sort mapping obtained from the last
          call to a formula translation *)
    end
  end
end


module type TslkBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support TSLK. *)
sig
  type t
  
  module Tslk (K : Level.S) :
    (** Translation of TSLK expressions. *)
    sig
      include GeneralBackend with type t := t

      module Exp : TSLKEXP

      val literal_list : bool -> Exp.literal list -> t
      (** [literal_list useq ls] translates the list [ls] of literals into its
          internal internal representation. [useq] determines whether
          quantifiers should be used in the generated query. *)

      val formula      : Smp.cutoff_strategy_t ->
                         Smp.cutoff_options_t ->
                         bool ->
                         Exp.formula -> t
      (** [formula stat strat copt useq f] translates the formula [f] following
          the strategy [strat] to compute the SMP cutoff and tactic [stat] to
          decide whether or not to include extra information to help the
          future satisfiability analysis of the formula. When computing the SMP
          it considers the options passes in [copt]. [useq] determines whether
          quantifiers should be used in the generated query. *)
          
      val conjformula  : bool -> Exp.conjunctive_formula -> t
      (** [conjformula useq f] tranlates the conjunctive formula [f]. [useq]
          determines whether quantifiers should be used in the generated query. *)

      val sort_map : unit -> GenericModel.sort_map_t
      (** [sort_map ()] returns the sort mapping obtained from the last
          call to a formula translation *)
    end
end




module type NumBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support Numeric Reasoning. *)
sig
  type t
  
  module Num :
  (** Translation of numeric expressions. *)
  sig
    module Exp : NUMEXP

    module Query (Q : NUM_QUERY) :
    sig
      include GeneralBackend with type t := t

      val int_varlist  : Exp.V.t list -> t
      (** [int_varlist vs] tranlates the list [vs] of intege/r variables
          into its corresponding internal representation. *)
      
      val formula      : Exp.formula -> t
      (** Tranlation of a numeric formula into its related data structure. *)
      
      val literal      : Exp.literal -> t
      (** Translation of a literal into an internal representation. *)
      
      val int_formula  : Exp.formula -> t
      (** [int_formula f] translates the integer formula [f]. *)
      
      val int_formula_with_lines : Exp.formula -> t
      (** [int_formula_with_lines f] translate the integer formula [f] taking into 
          account the number of lines previously passed through [set_prog_lines].
          *)
      
      val std_widening : Exp.V.t list -> Exp.formula -> Exp.literal -> t
      (** [std_widening vars f l] constructs an internal representation of 
          a standard widening. *)

      val sort_map : unit -> GenericModel.sort_map_t
      (** [sort_map ()] returns the sort mapping obtained from the last
          call to a formula translation *)
    end
  end
end


module type PairsBackend =
(** Signatures of the functions the Solver needs to implement in order
    to fully support Pairs Reasoning. *)
sig
  type t
  
  module Pairs :
  (** Translation of pairs expressions. *)
  sig
    module Exp : PAIRSEXP

    module Query (Q : PAIRS_QUERY) :
    sig
      include GeneralBackend with type t := t

      val pairs_formula  : Exp.formula -> t
      (** [pairs_formula f] translates the formula [f] in the theory of
       *  pairs into a representation according to a solver. *)
      
      val pairs_formula_with_lines : Exp.formula -> t
      (** [pairs_formula_with_lines f] translate the formula [f] in the
       *  theory of pairs into a representation according to a solver,
       *  bearing in mind the number of lines previously passed through
       *  [set_prog_lines]. *)
      
      val sort_map : unit -> GenericModel.sort_map_t
      (** [sort_map ()] returns the sort mapping obtained from the last
          call to a formula translation *)
    end
  end
end



module type CUSTOM_BACKEND_SOLVER = 
(** Signature of a full backend solver. *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
        
    include PosBackend    with type t := t
    include TllBackend    with type t := t
    include NumBackend    with type t := t
    include PairsBackend  with type t := t
    include TslkBackend   with type t := t
  end
end

module type BACKEND_SOLVER = CUSTOM_BACKEND_SOLVER
  with module Translate.Pos.Exp    = PosExpression
  and  module Translate.Tll.Exp    = TLLExpression
  and  module Translate.Num.Exp    = NumExpression
  and  module Translate.Pairs.Exp  = PairsExpression


module type CUSTOM_BACKEND_POS =
(** Signature of solver that supports position reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that the Solver 
      the Solver understands. *)
  
    include PosBackend with type t := t  
  end
end

module type BACKEND_POS = CUSTOM_BACKEND_POS
  with module Translate.Pos.Exp = PosExpression




module type CUSTOM_BACKEND_TLL =
(** Signature of solver that supports TLL reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include TllBackend with type t := t  
  end
end

module type BACKEND_TLL = CUSTOM_BACKEND_TLL
  with module Translate.Tll.Exp = TLLExpression




module type CUSTOM_BACKEND_TSLK =
(** Signature of solver that supports TSLK reasoning *)
sig
  include BackendCommon
  
  module Translate :
    sig
    (** Translation of expressions into internal data structures that the
        Solver understands. *)

       include TslkBackend with type t := t
    end
end

module type BACKEND_TSLK = CUSTOM_BACKEND_TSLK
(*    with  module Translate.Tslk.Smp = SmpTslk *)




module type CUSTOM_BACKEND_NUM =
(** Signature of solver that supports numeric reasoning *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include NumBackend with type t := t  
  end
end

module type BACKEND_NUM = CUSTOM_BACKEND_NUM
  with module Translate.Num.Exp = NumExpression


module type CUSTOM_BACKEND_PAIRS =
(** Signature of solver that supports reasoning over pairs *)
sig
  include BackendCommon
  
  module Translate : sig
  (** Translation of expressions into internal data structures that 
      the Solver understands. *)
  
    include PairsBackend with type t := t  
  end
end

module type BACKEND_PAIRS = CUSTOM_BACKEND_PAIRS
  with module Translate.Pairs.Exp = PairsExpression


