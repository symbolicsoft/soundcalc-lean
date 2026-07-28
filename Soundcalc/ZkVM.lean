import Soundcalc.Field
import Soundcalc.Circuit.CircuitVM

open Soundcalc

/-!
  # `Soundcalc.ZkVM`
  Specification of a zkVM structure containing generic circuits.

  Supported circuits are specified in `Soundcalc.Circuit.CircuitVM`.
-/

namespace Soundcalc

structure ZkVM where
  name        : String
  version     : Option String
  field       : FieldParams
  circuits    : List CircuitVM := [] -- eterogeneous list of circuits
  /- Every circuit included in the zkVM must run over the same field. -/
  h_circuits_field : circuits.all (·.toGenericCircuit.field == field) = true := by decide

end Soundcalc
