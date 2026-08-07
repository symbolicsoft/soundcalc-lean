import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common
import SoundcalcIO.TomlParser.PCS.FRI
import SoundcalcIO.TomlParser.PCS.WHIR
import SoundcalcIO.TomlParser.Circuit.Jagged
import SoundcalcIO.TomlParser.Circuit.DeepAli
import SoundcalcIO.TomlParser.Circuit.SWIRL
import SoundcalcIO.TomlParser.Lookup

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml

/-
  We work in the `Soundcalc` namespace to extend `Circuit` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc

/--
  Returns a `Circuit` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is nested in a table `tomlTab`
  parsed from a `.toml` file of a ZkVM configuration.

  Raises an error if any core fields are missing.
-/
def Circuit.parseFromToml (circTab : Table)
                          (zkvmTab : Table)
                          (tomlTab : Table) : IO Circuit := do
  /-
    We loop over all the [[circuit.lookups]]
    If no lookups are defined, we return an empty array instead of an error.
    If lookups is defined not as an array, we still error out.
  -/
  let circ_lookups ← orExit (getArrayD circTab "lookups" #[])
  let mut lookup_list : List LookupCfg := []

  for lookup in circ_lookups do
    match lookup with
    | .table' _ lookup_tab =>
      let lookupcfg ← LookupCfg.parseFromToml lookup_tab zkvmTab
      lookup_list := lookup_list.concat lookupcfg
    |_ => IO.eprintln "Unexpected non-table lookup item"; IO.Process.exit 1

  let circ_protocol_family ← orExit (getString circTab "protocol_family")

  /- The last boolean parameter signals the FRIConfig should be parsed
  as per a Jagged circuit. (i.e., dense FRI params)

  Following soundcalc, SWIRL circuits are ALWAYS bundled with WHIR, whereas in zkVMs
  captured by the summarizer, Jagged and DeepAli circuits are ALWAYS bundled with FRI.
  Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L89
  **TODO** Revise the above in line with WHIR.

  **SOUNDCALC TODO** Allow for switching of PCS schemes.
  |-> Possible solution: add a PCS field explicitly within .toml files.
  -/
  let circuit ← match circ_protocol_family with
  | "JAGGED"    => let fcfg ← FRIConfig.parseFromToml circTab zkvmTab true
                    let jaggedCirc ← (JaggedCfg.parseFromToml circTab zkvmTab lookup_list (.fri fcfg))
                    pure (.jagged jaggedCirc)
  | "FRI_STARK" => let fcfg ← FRIConfig.parseFromToml circTab zkvmTab false
                    let deepAliCirc ← (DeepAliCfg.parseFromToml circTab zkvmTab lookup_list (.fri fcfg))
                    pure (.deepali deepAliCirc)
  | "SWIRL"     => let wcfg ← WHIRConfig.parseFromToml circTab zkvmTab
                    let swirl_tab ← orExit (getTable tomlTab "swirl")
                    let swirlCirc ← (SWIRLCfg.parseFromToml circTab zkvmTab swirl_tab wcfg)
                    pure (.swirl swirlCirc)
  | _           =>  IO.eprintln "Unsupported circuit family."; IO.Process.exit 1
  pure circuit

end Soundcalc
