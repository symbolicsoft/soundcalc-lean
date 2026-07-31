import Mathlib
import Soundcalc.Lookup
import Soundcalc.PCS.PCS

namespace Soundcalc

/- Structure containing fields shared among different circuits. -/
structure GenericCircuit where
  name             : String
  field            : FieldParams
  proofSystName    : String
  densePCS         : PCS
  gapToRadius      : Option ℚ       := none -- gapToRadius is defined at circuit level
  lookups          : List LookupCfg := []
  /- Flags for supported regimes -/
  isUDR            : Bool
  isJBR            : Bool
  /- The theorems below enforce coherency between fields
      included in different data structures. -/
  h_densePCS_field : densePCS.field = field                := by rfl
  h_lookups_field  : lookups.all (·.field == field) = true := by decide
  /- A circuit must support at least one regime. -/
  h_regime_exists  : (isUDR || isJBR) = true               := by decide

end Soundcalc
