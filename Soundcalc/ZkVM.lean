import Soundcalc.Field.Core
import Soundcalc.Circuit.Circuit

open Soundcalc

/-!
  # `Soundcalc.ZkVM`
  Specification of a zkVM structure containing generic circuits.

  Supported circuits are specified in `Soundcalc.Circuit.Circuit`.
-/

namespace Soundcalc

structure ZkVM where
  name        : String
  version     : Option String
  field       : FieldParams
  circuits    : List Circuit := [] -- heterogeneous list of circuits

end Soundcalc
