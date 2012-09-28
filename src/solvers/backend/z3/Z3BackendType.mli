open BackendSolverIntf

module type CUSTOM_BACKEND_POS_TLL_TSLK =
  sig
  include BackendCommon
  module Translate : sig
    include PosBackend  with type t := t
    include TllBackend  with type t := t
    include TslkBackend with type t := t
  end
end

module type BACKEND_POS_TLL_TSLK = CUSTOM_BACKEND_POS_TLL_TSLK
  with module Translate.Pos.Exp  = PosExpression
  and  module Translate.Tll.Exp  = TllExpression
  and  module Translate.Tll.Smp  = SmpTll
  and  module Translate.Tslk.Smp = SmpTslk
(*  and  module Translate.Tslk =
        functor (E : TSLKExpression.S) ->
          module Smp = SmpTslk
*)

(*  and  module Translate.Tslk().Exp = TSLKExpression.S*)
(*  and  module Translate.Tslk.Smp = SmpTslk *)

