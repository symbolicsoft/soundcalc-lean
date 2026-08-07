import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml
/-
  We work in the `Soundcalc` namespace to extend `LookupCfg` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc

/--
  Returns a `LookupCfg` from a lookup table `lookupTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.

  Raises an error if any core fields are missing.
-/
def LookupCfg.parseFromToml (lookupTab : Table)
                            (zkvmTab : Table) : IO LookupCfg := do
  /- Global zkVM values -/
  let zkvm_field ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)

  /- Lookup specific values -/
  let lookup_name ← orExit (getString lookupTab "name")
  /- `false = univariate`; `true = multivariate` -/
  let lookup_logup_type ← orExit (getLogUpBoolFromStr lookupTab "logup_type")
  let lookup_rows_L ← orExit (getNat lookupTab "rows_L")
  let lookup_rows_T ← orExit (getNat lookupTab "rows_T")
  /-
    Fields with a default value, parsed as per `soundcalc`'s Python.
    https://github.com/ethereum/soundcalc/blob/809896fb8d3aba4fd8f657c781601e3ef2b968dd/soundcalc/zkvms/zkvm.py#L28
  -/
  let lookup_num_columns_S ← orExit (getNatD lookupTab "num_columns_S" 1)
  let lookup_num_lookups_M ← orExit (getNatD lookupTab "num_lookups_M" 1)
  let lookup_grinding_bits_lookup ← orExit (getNatD lookupTab "grinding_bits_lookup" 0)

  /- Mirrors the __post_init__ of
    https://github.com/ethereum/soundcalc/blob/main/soundcalc/lookups/logup.py#L45:
    if `multilinear_fingerprint` is missing, it matches the
    boolean associated with `logup_type`:
    (`"multivariate"` -> `multilinear_fingerprint=true`;
    `"univariate"`   -> `multilinear_fingerprint=false`) -/
  let lookup_multilinear_fingerprint ← orExit (getBoolD lookupTab "multilinear_fingerprint" lookup_logup_type)

  let lcfg: LookupCfg := {
    name                   := lookup_name
    field                  := zkvm_field
    isLogUpMultivar        := lookup_logup_type
    rowsL                  := lookup_rows_L
    rowsT                  := lookup_rows_T
    numColumnsS            := lookup_num_columns_S
    numLookupsM            := lookup_num_lookups_M
    grindBitsLookup        := lookup_grinding_bits_lookup
    multilinearFingerprint := lookup_multilinear_fingerprint
  }

  pure lcfg

end Soundcalc
