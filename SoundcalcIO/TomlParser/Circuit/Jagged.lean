import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml

/-
  We work in the `Soundcalc` namespace to extend `JaggedCfg` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc

/--
  Returns a `JaggedCfg` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.
  The output `JaggedCfg` also bundles the list of lookups it contains
  (`lookupList`), as well as its PCS configuration (`PCSConfig`).

  Raises an error if any core fields are missing.
-/
def JaggedCfg.parseFromToml (circTab : Table)
                            (zkvmTab : Table)
                            (lookupList : List LookupCfg)
                            (PCSconfig : PCS) : IO JaggedCfg := do
  /- Global zkVM values -/
  let zkvm_field ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)

  /- Circuit-specific fields -/
  let circ_name ← orExit (getString circTab "name")
  let circ_trace_length ← orExit (getNat circTab "trace_length")
  let circ_trace_columns ← orExit (getNat circTab "trace_columns")
  let circ_num_constraints ← orExit (getNat circTab "num_constraints")
  let circ_air_max_degree ← orExit (getNat circTab "air_max_degree")

  /- Proofs of consistency ensuring that the `FieldParams` within
     the Jagged circuit are coherent with each other. -/
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

  let jcfg: JaggedCfg := {
    name              := circ_name
    field             := zkvm_field
    densePCS          := PCSconfig
    traceLength       := circ_trace_length
    traceWidth        := circ_trace_columns
    numConstraints    := circ_num_constraints
    airMaxDegree      := circ_air_max_degree
    lookups           := lookupList
    h_densePCS_field  := PLift.down (α := PCSconfig.field = zkvm_field) h_densePCS_field
    h_lookups_field   := PLift.down (α := lookupList.all (·.field == zkvm_field) = true) h_lookups_lifted
    gapToRadius       := circ_gap_to_radius
  }

  pure jcfg

end Soundcalc
