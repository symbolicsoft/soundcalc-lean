import Mathlib
import Soundcalc.Field
import Soundcalc.Circuit.Jagged

open Soundcalc

/-!
  # `Soundcalc.ZkVM`
  A specification of what a ZkVM configuration is, as per the
  structure specified in `.toml` reference files.
-/

/-
  *TODO*: This structure is currently tailored to ZkVMs running
  Jagged circuits (SP1-like). Generalizing comes later in the roadmap.
-/

namespace Soundcalc

structure ZkVMCfg where
  name         : String
  protoFamily  : String
  field        : FieldParams
  version      : String
  hashSizeBits : ℕ
  circuits     : List JaggedCfg
  /-- Every circuit must run over the same field as the zkVM itself
      (same guard as `JaggedCfg.h_densePCS_field` / `h_lookups_field`). -/
  h_circuits_field : circuits.all (·.field == field) = true := by decide

end Soundcalc
