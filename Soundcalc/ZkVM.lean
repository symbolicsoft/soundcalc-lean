import Mathlib
import Soundcalc.Field
import Soundcalc.Circuit.Jagged
import Soundcalc.Circuit.DeepAli

open Soundcalc

/-!
  # `Soundcalc.ZkVM`
  A specification of supported zkVM configurations.
  Current support: JaggedVM, DeepAliVM.
-/

namespace Soundcalc

structure JaggedVM where
  name        : String
  version     : Option String
  field       : FieldParams
  circuits    : List JaggedCfg := []
  /-- Every circuit must run over the same field as the zkVM itself
    (same guard as `JaggedCfg.h_densePCS_field` / `h_lookups_field`). -/
  h_circuits_field : circuits.all (·.field == field) = true := by decide

structure DeepAliVM where
  name        : String
  version     : Option String
  field       : FieldParams
  circuits    : List DeepAliCfg := []
  h_circuits_field : circuits.all (·.field == field) = true := by decide

end Soundcalc
