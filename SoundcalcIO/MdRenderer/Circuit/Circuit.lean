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
  Returns a string containing all the circuit parameters of a generic `Circuit`.
-/
def Circuit.circParamsStr : Circuit → IO String
  | .jagged c  => c.renderCircParams
  | .deepali c => c.renderCircParams
  | .swirl c   => c.renderCircParams
/--
  Returns a [header, secbits] list containing all the UDR security bits of a generic `Circuit`.
  If the regime is unsupported, return `none` instead.
-/
def Circuit.secParamsUDR : Circuit → IO (Option (List (String × Nat)))
  | .jagged c  => c.getSecurityLevels
  | .deepali c => let gc : Circuit := .deepali c
                  if gc.isUDR then c.getSecurityLevels (UDR c.field)
                  else pure none
  | .swirl c   => let gc : Circuit := .swirl c
                  if gc.isUDR then c.getSecurityLevels -- regimes are internally handled by `explicit_m`
                  else pure none
/--
  Returns a [header, secbits] list containing all the JBR security bits of a generic `Circuit`.
  If the regime is unsupported, return `none` instead.
-/
def Circuit.secParamsJBR : Circuit → IO (Option (List (String × Nat)))
  | .jagged _  => pure none           -- unsupported
  | .deepali c => let gc : Circuit := .deepali c
                  if gc.isJBR then c.getSecurityLevels (JBR c.field (2^40) c.gapToRadius)
                  else pure none
  | .swirl c   => let gc : Circuit := .swirl c
                  if gc.isJBR then c.getSecurityLevels -- regimes are internally handled by `explicit_m`
                  else pure none


end Soundcalc
