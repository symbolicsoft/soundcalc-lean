import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Circuit.Jagged
import SoundcalcIO.MdRenderer.Circuit.DeepAli
import SoundcalcIO.MdRenderer.Circuit.SWIRL

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
  | .jagged c  => c.renderCircParams
  | .deepali c => c.renderCircParams
  | .swirl c   => c.renderCircParams
/--
  Returns a [header, secbits] list containing all the UDR security bits of a generic Circuit.
-/
def Circuit.secParamsUDR : Circuit → IO (List (String × Nat))
  | .jagged c  => c.getSecurityLevels
  | .deepali c => c.getSecurityLevels (UDR c.field)
  | .swirl c   => c.getSecurityLevels -- regimes are internally handled by `explicit_m`

/--
  Returns a [header, secbits] list containing all the JBR security bits of a generic Circuit.
-/
def Circuit.secParamsJBR : Circuit → IO (List (String × Nat))
  | .jagged _  => pure []             -- unsupported; **FEAT TODO** ìmprove representation,
                                      -- in line with refactoring of regimes.
  | .deepali c => c.getSecurityLevels (JBR c.field (2^40) c.gapToRadius)
  | .swirl c   => c.getSecurityLevels -- regimes are internally handled by `explicit_m`


end Soundcalc
