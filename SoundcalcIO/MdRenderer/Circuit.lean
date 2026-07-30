import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Jagged
import SoundcalcIO.MdRenderer.DeepAli

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `Circuit` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/--
  Returns a string containing all the circuit parameters of a generic Circuit.
-/
def Circuit.circParamsStr : Circuit → IO String
  | .jagged c => c.renderCircParams
  | .deepali c => c.renderCircParams
/--
  Returns a [header, secbits] list containing all the UDR security bits of a generic Circuit.
-/
def Circuit.secParamsUDR : Circuit → IO (List (String × Nat))
  | .jagged c => c.getSecurityLevels
  | .deepali c => c.getSecurityLevels (UDR c.field)

/--
  Returns a [header, secbits] list containing all the JBR security bits of a generic Circuit.
-/
def Circuit.secParamsJBR : Circuit → IO (List (String × Nat))
  | .jagged _ => pure []         -- unsupported; *TODO* ìmprove representation.
  | .deepali c => c.getSecurityLevels (JBR c.field (2^40) c.gapToRadius)

end Soundcalc
