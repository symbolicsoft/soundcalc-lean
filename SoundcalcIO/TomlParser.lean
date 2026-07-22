import Lake.Toml.Load
import Lake.Toml.Data.Value
import Lean.Parser.Types
import SoundcalcIO.Common

import Soundcalc

open Lake.Toml Lean Parser
open Soundcalc
open SoundcalcIO

namespace SoundcalcIO

/-
  Auxiliary methods to parse `.toml` files robustly.
  Current strategy: if a field is missing, is incomplete, or it
  does not match the expected type within the `.toml`, the Parser
  errors out. If a field is optional, a separate `get*` combinator
  returns a default value instead.
-/

private def getString (tbl : Table) (key : String) : Except String String :=
  match tbl.find? (.mkSimple key) with
  | some (.string _ s)  => .ok s
  | some _              => .error s!"key '{key}' exists but is not a string"
  | none                => .error s!"key '{key}' not found"

private def getLogUpBoolFromStr (tbl : Table) (key : String) : Except String Bool :=
  let s := getString tbl key
  match s with
  | .ok "univariate"   => .ok false
  | .ok "multivariate" => .ok true
  | _ => .error s!"key '{key}' is an invalid LogUp string."

private def getNat (tbl : Table) (key : String) : Except String Nat :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .error s!"key '{key}' not found"

private def getBool (tbl : Table) (key : String) : Except String Bool :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .error s!"key '{key}' not found"

private def getBoolOrNone (tbl : Table) (key : String) : Except String (Option Bool) :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .ok none

private def getFloat (tbl : Table) (key : String) : Except String Float :=
  match tbl.find? (.mkSimple key) with
  | some (.float _ f)   => .ok f
  | some _              => .error s!"key '{key}' exists but is not a float"
  | none                => .error s!"key '{key}' not found"

private def getArray (tbl : Table) (key : String) : Except String (Array Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .error s!"key '{key}' not found"

private def getArrayOrNone (tbl : Table) (key : String) : Except String (Option (Array Value)) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .ok none

private def getList (tbl : Table) (key : String) : Except String (List Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a.toList
  | some _              => .error s!"key '{key}' exists but is not a List"
  | none                => .error s!"key '{key}' not found"

private def getListNat (tbl : Table) (key : String) : Except String (List Nat) := do
  let l ← getList tbl key
  l.mapM fun
  | .integer _ i =>
      if i ≥ 0 then .ok i.toNat
      else .error s!"The List indexed by '{key}' contains a negative integer"
  | _ => .error s!"The List indexed by '{key}' contains non-integer values"

private def getTable (tbl : Table) (key : String) : Except String (RBDict Name Value Name.quickCmp) :=
  match tbl.find? (.mkSimple key) with
  | some (.table' _ t)  => .ok t
  | some _              => .error s!"key '{key}' exists but is not a Table"
  | none                => .error s!"key '{key}' not found"

/- More parsing auxiliary methods. -/

/--
  Map of supported `String` -> `FieldParams`.
-/
private def mapStrToFieldParams : List (String × FieldParams) := [
  ("KoalaBear^4", koalaBear4),
]

/--
  Maps strings to supported `FieldParams`.
-/
private def strToFieldParams (map : List (String × FieldParams)) (s : String) : Except String FieldParams :=
  match map.lookup s with
  | some fp => .ok fp
  | none    => .error s!"no FieldParams defined for '{s}')"

/--
  Parses a `.toml` file into a `ZkVMCfg` structure.
-/
def tomlToZkVMCfg (inTomlFile: String) : IO ZkVMCfg := do
  let inToml ← IO.FS.readFile inTomlFile
  let ictx : InputContext := mkInputContext inToml inTomlFile
  let .ok tbl ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  /- Parsing [zkevm]-/
  let zkvm_tab ← orExit (getTable tbl "zkevm")

  let zkvm_name ← orExit (getString zkvm_tab "name")
  let zkvm_protocol_family ← orExit (getString zkvm_tab "protocol_family")
  let zkvm_field ← orExit (getString zkvm_tab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)
  let zkvm_version ← orExit (getString zkvm_tab "version")
  let zkvm_hash_size_bits ← orExit (getNat zkvm_tab "hash_size_bits")

  let zkvm_circs ← orExit (getArray tbl "circuits")

  /- We incrementally build the list of Jagged circuits contained in SP1 -/
  let mut circuit_list : List JaggedCfg := []

  /- We parse all the [[circuits]] -/
  for circ in zkvm_circs do
    match circ with
    | .table' _ circ_tab =>
      /- Parsing all the fields found within SP1 -/
      let circ_name ← orExit (getString circ_tab "name")
      let circ_udr_only ← orExit (getBool circ_tab "udr_only")
      let circ_blowup_factor ← orExit (getNat circ_tab "blowup_factor")
      /- We interpret the float as an exact rational according
         to the `mapFloatstrToRat` map. Note: if the float is
         malformed, the conversion fails. -/
      let circ_rho ← orExit (getFloat circ_tab "rho")
      let circ_rho ← orExit (floatToRate mapFloatToRate circ_rho)
      let circ_trace_length ← orExit (getNat circ_tab "trace_length")
      let circ_trace_columns ← orExit (getNat circ_tab "trace_columns")
      let circ_dense_length ← orExit (getNat circ_tab "dense_length")
      let circ_dense_batch ← orExit (getNat circ_tab "dense_batch")
      let circ_num_constraints ← orExit (getNat circ_tab "num_constraints")
      let circ_air_max_degree ← orExit (getNat circ_tab "air_max_degree")
      let circ_opening_points ← orExit (getNat circ_tab "opening_points")
      let circ_power_batching ← orExit (getBool circ_tab "power_batching")
      let circ_multilinear_batching ← orExit (getBool circ_tab "multilinear_batching")
      let circ_multilinear_zerocheck ← orExit (getBool circ_tab "multilinear_zerocheck")
      let circ_num_queries ← orExit (getNat circ_tab "num_queries")
      /- We interpret the folding factors as a list of Naturals. -/
      let circ_fri_folding_factors ← orExit (getListNat circ_tab "fri_folding_factors")
      let circ_fri_early_stop_degree ← orExit (getNat circ_tab "fri_early_stop_degree")
      let circ_grinding_batching_phase ← orExit (getNat circ_tab "grinding_batching_phase")
      let circ_grinding_query_phase ← orExit (getNat circ_tab "grinding_query_phase")

      /-
        We loop over all the [[circuit.lookups]]
        If no lookups are defined, we return an empty array instead of an error.
        If lookups is defined not as an array, we still error out.
      -/
      let circ_lookups_opt ← orExit (getArrayOrNone circ_tab "lookups")
      let circ_lookups := circ_lookups_opt.getD #[]
      let mut lookup_list : List LookupCfg := []

      for lookup in circ_lookups do
        match lookup with
        | .table' _ lookup_tab =>
          let lookup_name ← orExit (getString lookup_tab "name")
          /- `false = univariate`; `true = multivariate` -/
          let lookup_logup_type ← orExit (getLogUpBoolFromStr lookup_tab "logup_type")
          let lookup_rows_L ← orExit (getNat lookup_tab "rows_L")
          let lookup_rows_T ← orExit (getNat lookup_tab "rows_T")
          let lookup_num_columns_S ← orExit (getNat lookup_tab "num_columns_S")
          let lookup_num_lookups_M ← orExit (getNat lookup_tab "num_lookups_M")
          let lookup_grinding_bits_lookup ← orExit (getNat lookup_tab "grinding_bits_lookup")

          /- Mirrors the __post_init__ of
             https://github.com/ethereum/soundcalc/blob/main/soundcalc/lookups/logup.py#L45:
             if `lookup_multilinear_fingerprint_opt` is missing, it matches the
             boolean associated with `logup_type`:
             (`"multivariate"` -> `multilinear_fingerprint=true`;
              `"univariate"`   -> `multilinear_fingerprint=false`) -/
          let lookupcfg: LookupCfg := {
            name            := lookup_name
            field           := zkvm_field
            isLogUpMultivar := lookup_logup_type
            rowsL           := lookup_rows_L
            rowsT           := lookup_rows_T
            numColumnsS     := lookup_num_columns_S
            numLookupsM     := lookup_num_lookups_M
            grindBitsLookup := lookup_grinding_bits_lookup
          }
          lookup_list := lookup_list.concat lookupcfg
        |_ => IO.eprintln "Unexpected non-table lookup item"; IO.Process.exit 1

      let fri_lhs : Q := (circ_dense_length : Q) / (circ_rho : Q) /
                         ((circ_fri_folding_factors.foldl (· * ·) 1 : N) : Q)
      let fri_rhs : Q := circ_fri_early_stop_degree
      let h_lifted : PLift (fri_lhs = fri_rhs) ←
        match decEq fri_lhs fri_rhs with
        | .isTrue h  => pure (PLift.up h : PLift (fri_lhs = fri_rhs))
        | .isFalse _ => do IO.eprintln "FRI early-stop check failed: denseLen/ρ/∏folds ≠ earlyStopDeg"
                           IO.Process.exit 1
      let h_eta_lifted : PLift (zkvm_field.card ≤ 2 ^ 150 ∧ 1 / 25 < (circ_rho : Q)) ←
        if h : zkvm_field.card ≤ 2 ^ 150 ∧ 1 / 25 < (circ_rho : Q) then
          pure (PLift.up h)
        else
          IO.eprintln "JBR gap guard failed: need field.card ≤ 2^150 and 1/25 < ρ"; IO.Process.exit 1

      let friconfig: FRIConfig := {
        hashBits          := zkvm_hash_size_bits
        ρ                 := circ_rho
        traceLen          := circ_trace_length
        field             := zkvm_field
        denseLen          := circ_dense_length
        batchSize         := circ_dense_batch
        powerBatch        := circ_power_batching
        multilinBatch     := circ_multilinear_batching
        numQueries        := circ_num_queries
        foldingFactors    := circ_fri_folding_factors
        earlyStopDeg      := circ_fri_early_stop_degree
        h_earlyStop       := PLift.down (α := fri_lhs = fri_rhs) h_lifted
        h_eta             := PLift.down (α := zkvm_field.card ≤ 2 ^ 150 ∧ 1 / 25 < (circ_rho : Q)) h_eta_lifted
        grindQuery        := circ_grinding_query_phase
        grindBatch        := circ_grinding_batching_phase
      }

      let h_lookups_lifted : PLift (lookup_list.all (·.field == zkvm_field) = true) ←
        match decEq (lookup_list.all (·.field == zkvm_field)) true with
        | .isTrue h  => pure (PLift.up h)
        | .isFalse _ => IO.eprintln "Lookup field mismatch: not all lookups share the circuit's field"; IO.Process.exit 1

      let jaggedcfg: JaggedCfg := {
        name              := circ_name
        field             := zkvm_field
        proofSystName     := "Jagged"
        densePCS          := friconfig
        traceLength       := circ_trace_length
        traceWidth        := circ_trace_columns
        numConstraints    := circ_num_constraints
        airMaxDegree      := circ_air_max_degree
        lookups           := lookup_list
        h_lookups_field   := PLift.down (α := lookup_list.all (·.field == zkvm_field) = true) h_lookups_lifted
      }
      circuit_list := circuit_list.concat jaggedcfg
    | _ => IO.eprintln "Unexpected non-table circuit item"; IO.Process.exit 1

  let h_circuits_lifted : PLift (circuit_list.all (·.field == zkvm_field) = true) ←
    match decEq (circuit_list.all (·.field == zkvm_field)) true with
    | .isTrue h  => pure (PLift.up h)
    | .isFalse _ => IO.eprintln "Circuit field mismatch: not all circuits share the zkVM's field"; IO.Process.exit 1

  let zkvmcfg: ZkVMCfg := {
    name         := zkvm_name
    protoFamily  := zkvm_protocol_family
    field        := zkvm_field
    version      := zkvm_version
    hashSizeBits := zkvm_hash_size_bits
    circuits     := circuit_list
    h_circuits_field := PLift.down (α := circuit_list.all (·.field == zkvm_field) = true) h_circuits_lifted
  }
  pure (zkvmcfg)

end SoundcalcIO
