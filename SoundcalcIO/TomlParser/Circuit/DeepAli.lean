import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml
/-
  We work in the `Soundcalc` namespace to extend `DeepAliCfg` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc

/--
  Returns a `DeepAliCfg` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.
  The output `DeepAliCfg` also bundles the list of lookups it contains
  (`lookupList`), as well as its PCS configuration (`PCSconfig`).

  Raises an error if any core fields are missing.
-/
def DeepAliCfg.parseFromToml (circTab : Table)
                             (zkvmTab : Table)
                             (lookupList : List LookupCfg)
                             (PCSconfig : PCS) : IO DeepAliCfg := do
  /- Global zkVM values -/
  let zkvm_field ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)

  let circ_name ← orExit (getString circTab "name")
  let circ_num_constraints ← orExit (getNat circTab "num_constraints")
  let circ_air_max_degree ← orExit (getNat circTab "air_max_degree")

  /- If the grinding_deep bits field is defined in the `.toml`, use it.
      Else, default to `0`. `soundcalc`'s reference:
      https://github.com/ethereum/soundcalc/blob/809896fb8d3aba4fd8f657c781601e3ef2b968dd/soundcalc/zkvms/zkvm.py#L110
  -/
  let circ_grinding_deep ← orExit (getNatD circTab "grinding_deep" 0)

  /-
    `max_combo` and `opening_points` appear to be the same field.
    The Python `soundcalc` parses `opening_points` as `max_combo`:
    https://github.com/ethereum/soundcalc/blob/809896fb8d3aba4fd8f657c781601e3ef2b968dd/soundcalc/zkvms/zkvm.py#L108
  -/
  -- let circ_max_combo ← orExit (getNat circTab "max_combo")
  let circ_max_combo ← orExit (getNat circTab "opening_points")

  /- Proofs of consistency ensuring that the `FieldParams` within
     the DEEP-ALI circuit are coherent with each other. -/
  let h_lookups_lifted : PLift (lookupList.all (·.field == zkvm_field) = true) ←
  match decEq (lookupList.all (·.field == zkvm_field)) true with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Lookup field mismatch: not all lookups share the circuit's field"; IO.Process.exit 1

  let h_densePCS_field : PLift (PCSconfig.field = zkvm_field) ←
  match decEq PCSconfig.field zkvm_field with
  | .isTrue h  => pure (PLift.up h : PLift (PCSconfig.field = zkvm_field))
  | .isFalse _ => IO.eprintln "PCS field mismatch: densePCS.field ≠ circuit field"; IO.Process.exit 1

  let circ_gap_to_radius_cond ← orExit (getOptFloat circTab "gap_to_radius")
  let circ_gap_to_radius ← orExit (gapToRadiusRat circ_gap_to_radius_cond)

  let circ_explicit_regime ← orExit (getOptRegime circTab "explicit_regime")

  let dacfg: DeepAliCfg := {
    name              := circ_name
    field             := zkvm_field
    densePCS          := PCSconfig
    numConstraints    := circ_num_constraints
    airMaxDegree      := circ_air_max_degree
    maxCombo          := circ_max_combo
    grindDeep         := circ_grinding_deep
    lookups           := lookupList
    h_densePCS_field  := PLift.down (α := PCSconfig.field = zkvm_field) h_densePCS_field
    h_lookups_field   := PLift.down (α := lookupList.all (·.field == zkvm_field) = true) h_lookups_lifted
    gapToRadius       := circ_gap_to_radius
    explicitRegime    := circ_explicit_regime
  }

  pure dacfg

end Soundcalc
