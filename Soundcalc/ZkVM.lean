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

end Soundcalc
