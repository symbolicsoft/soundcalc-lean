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

private def getOptString (tbl : Table) (key : String) : Except String (Option String) :=
  match tbl.find? (.mkSimple key) with
  | some (.string _ s)  => .ok s
  | some _              => .error s!"key '{key}' exists but is not a string"
  | none                => .ok none

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

/--
  Returns the natural indexed by `key` if it exists in `tbl`.
  If it does not exist, return `d` instead.
  If a value is indexed by `key` but it is not a natural, return an error.
-/
private def getNatD (tbl : Table) (key : String) (d : Nat) : Except String Nat :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .ok d

private def getOptNat (tbl : Table) (key : String) : Except String (Option Nat) :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .ok none

private def getBool (tbl : Table) (key : String) : Except String Bool :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .error s!"key '{key}' not found"

/--
  Returns the bool indexed by `key` if it exists in `tbl`.
  If it does not exist, return `d` instead.
  If a value is indexed by `key` but it is not a bool, return an error.
-/
private def getBoolD (tbl : Table) (key : String) (d : Bool) : Except String Bool :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .ok d

private def getOptBool (tbl : Table) (key : String) : Except String (Option Bool) :=
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

/--
  Returns the array indexed by `key` if it exists in `tbl`.
  If it does not exist, return `d` instead.
  If a value is indexed by `key` but it is not an array, return an error.
-/
private def getArrayD (tbl : Table) (key : String) (d: Array Value) : Except String (Array Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .ok d

private def getOptArray (tbl : Table) (key : String) : Except String (Option (Array Value)) :=
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
  ("M31^4", mersenne31_4),
]

/--
  Maps strings to supported `FieldParams`.
-/
private def strToFieldParams (map : List (String × FieldParams)) (s : String) : Except String FieldParams :=
  match map.lookup s with
  | some fp => .ok fp
  | none    => .error s!"no FieldParams defined for '{s}')"

/--
  Returns a `FRIConfig` from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.
  The `isJagged` boolean signals whether the FRIConfig should be initialized
  as per a Jagged VM (i.e., using `dense_length`, `dense_batch`) or not
  (`trace_length`, `batch_size`).

  Raises an error if any core fields are missing.
-/
private def parseFRIConfig (circTab : Table)
                           (zkvmTab : Table)
                           (isJagged : Bool) : IO FRIConfig := do
  /- Global zkVM values -/
  let zkvm_hash_size_bits ← orExit (getNat zkvmTab "hash_size_bits")
  let zkvm_field ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)

  /- We interpret the float as an exact rational according
    to the `mapFloatstrToRat` map. Note: if the float is
    malformed, the conversion fails. -/
  let circ_rho ← orExit (getFloat circTab "rho")
  let circ_rho ← orExit (floatToRate mapFloatToRate circ_rho)

  /- Jagged circuits and FRI-STARK circuits encode
     `FRIConfig`'s `traceLen` and `batchSize` differently:
    - https://github.com/ethereum/soundcalc/blob/809896fb8d3aba4fd8f657c781601e3ef2b968dd/soundcalc/zkvms/zkvm.py#L90
    - https://github.com/ethereum/soundcalc/blob/809896fb8d3aba4fd8f657c781601e3ef2b968dd/soundcalc/zkvms/zkvm.py#L182
  -/
  let circ_trace_length ←
    if isJagged then orExit (getNat circTab "dense_length")
    else             orExit (getNat circTab "trace_length")

  let circ_batch_size ←
    if isJagged then orExit (getNat circTab "dense_batch")
    else             orExit (getNat circTab "batch_size")

  let circ_power_batching ← orExit (getBool circTab "power_batching")
  let circ_num_queries ← orExit (getNat circTab "num_queries")


  /- We interpret the folding factors as a list of Naturals. -/
  let circ_fri_folding_factors ← orExit (getListNat circTab "fri_folding_factors")
  let circ_fri_early_stop_degree ← orExit (getNat circTab "fri_early_stop_degree")

  /- Optional FRI fields that yield a default value if missing, as per `soundcalc`:
     https://github.com/ethereum/soundcalc/blob/809896fb8d3aba4fd8f657c781601e3ef2b968dd/soundcalc/zkvms/zkvm.py#L96
  -/
  let circ_multilinear_batching ← orExit (getBoolD circTab "multilinear_batching" false)
  let circ_grinding_batching_phase ← orExit (getNatD circTab "grinding_batching_phase" 0)
  let circ_grinding_commit_phase ← orExit (getNatD circTab "grinding_commit_phase" 0)
  let circ_grinding_query_phase ← orExit (getNatD circTab "grinding_query_phase" 0)

  /- We evaluate a proof certifying that the parsed values lead to a legal FRIConfig structure. -/
  let fri_lhs : Q := (circ_trace_length : Q) / (circ_rho : Q) /
                    ((circ_fri_folding_factors.foldl (· * ·) 1 : N) : Q)
  let fri_rhs : Q := circ_fri_early_stop_degree
  let h_lifted : PLift (fri_lhs = fri_rhs) ←
    match decEq fri_lhs fri_rhs with
    | .isTrue h  => pure (PLift.up h : PLift (fri_lhs = fri_rhs))
    | .isFalse _ => do IO.eprintln "FRI early-stop check failed: denseLen/ρ/∏folds ≠ earlyStopDeg"
                      IO.Process.exit 1

  let fcfg: FRIConfig := {
    hashBits          := zkvm_hash_size_bits
    ρ                 := circ_rho
    traceLen          := circ_trace_length
    field             := zkvm_field
    denseLen          := circ_trace_length  -- dense_length in SP1
    batchSize         := circ_batch_size    -- dense_batch in SP1
    powerBatch        := circ_power_batching
    multilinBatch     := circ_multilinear_batching
    numQueries        := circ_num_queries
    foldingFactors    := circ_fri_folding_factors
    earlyStopDeg      := circ_fri_early_stop_degree
    grindQuery        := circ_grinding_query_phase
    grindBatch        := circ_grinding_batching_phase
    grindCommit       := circ_grinding_commit_phase
    h_earlyStop       := PLift.down (α := fri_lhs = fri_rhs) h_lifted
  }

  pure fcfg

/--
  Returns a `LookupCfg` from a lookup table `lookupTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.

  Raises an error if any core fields are missing.
-/
private def parseLookupCfg (lookupTab : Table)
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

  let lcfg: LookupCfg := {
    name            := lookup_name
    field           := zkvm_field
    isLogUpMultivar := lookup_logup_type
    rowsL           := lookup_rows_L
    rowsT           := lookup_rows_T
    numColumnsS     := lookup_num_columns_S
    numLookupsM     := lookup_num_lookups_M
    grindBitsLookup := lookup_grinding_bits_lookup
  }

  pure lcfg

/--
  Returns a `JaggedCfg` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.
  The output `JaggedCfg` also bundles the list of lookups it contains
  (`lookupList`), as well as its FRI configuration (`friConfig`).

  Raises an error if any core fields are missing.
-/
private def parseJaggedCfg (circTab : Table)
                           (zkvmTab : Table)
                           (lookupList : List LookupCfg)
                           (friConfig : FRIConfig) : IO JaggedCfg := do
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
  let h_lookups_lifted : PLift (lookup_list.all (·.field == zkvm_field) = true) ←
  match decEq (lookupList.all (·.field == zkvm_field)) true with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Lookup field mismatch: not all lookups share the circuit's field"; IO.Process.exit 1

  let h_densePCS_field : PLift (friConfig.field = zkvm_field) ←
  match decEq friConfig.field zkvm_field with
  | .isTrue h  => pure (PLift.up h : PLift (friConfig.field = zkvm_field))
  | .isFalse _ => IO.eprintln "FRI field mismatch: densePCS.field ≠ circuit field"; IO.Process.exit 1

  let jcfg: JaggedCfg := {
    name              := circ_name
    field             := zkvm_field
    proofSystName     := "Jagged"
    densePCS          := friConfig
    traceLength       := circ_trace_length
    traceWidth        := circ_trace_columns
    numConstraints    := circ_num_constraints
    airMaxDegree      := circ_air_max_degree
    lookups           := lookupList
    h_densePCS_field  := PLift.down (α := friConfig.field = zkvm_field) h_densePCS_field
    h_lookups_field   := PLift.down (α := lookupList.all (·.field == zkvm_field) = true) h_lookups_lifted
  }

  pure jcfg

/--
  Returns a `DeepAliCfg` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.
  The output `DeepAliCfg` also bundles the list of lookups it contains
  (`lookupList`), as well as its FRI configuration (`friConfig`).

  Raises an error if any core fields are missing.
-/
private def parseDeepAliCfg (circTab : Table)
                            (zkvmTab : Table)
                            (lookupList : List LookupCfg)
                            (friConfig : FRIConfig) : IO DeepAliCfg := do
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
  let h_lookups_lifted : PLift (lookup_list.all (·.field == zkvm_field) = true) ←
  match decEq (lookupList.all (·.field == zkvm_field)) true with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Lookup field mismatch: not all lookups share the circuit's field"; IO.Process.exit 1

  let h_densePCS_field : PLift (friConfig.field = zkvm_field) ←
  match decEq friConfig.field zkvm_field with
  | .isTrue h  => pure (PLift.up h : PLift (friConfig.field = zkvm_field))
  | .isFalse _ => IO.eprintln "FRI field mismatch: densePCS.field ≠ circuit field"; IO.Process.exit 1

  let dacfg: DeepAliCfg := {
    name              := circ_name
    field             := zkvm_field
    proofSystName     := "DEEP-ALI"
    densePCS          := friConfig
    numConstraints    := circ_num_constraints
    airMaxDegree      := circ_air_max_degree
    maxCombo          := circ_max_combo
    grindDeep         := circ_grinding_deep
    lookups           := lookupList
    h_densePCS_field  := PLift.down (α := friConfig.field = zkvm_field) h_densePCS_field
    h_lookups_field   := PLift.down (α := lookupList.all (·.field == zkvm_field) = true) h_lookups_lifted
  }

  pure dacfg

/--
  Parse a `JaggedVM` from an input `.toml` file.
  If the `.toml` is invalid, the process errors out with an error message.
-/
def tomlToJaggedVM (inTomlFile: String) : IO JaggedVM := do
  let inToml ← IO.FS.readFile inTomlFile
  let ictx : InputContext := mkInputContext inToml inTomlFile
  let .ok tbl ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  /- Parsing [zkevm]-/
  let zkvm_tab ← orExit (getTable tbl "zkevm")

  let zkvm_name ← orExit (getString zkvm_tab "name")
  let zkvm_field ← orExit (getString zkvm_tab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)
  let zkvm_protocol_family ← orExit (getString zkvm_tab "protocol_family")
  let zkvm_version ← orExit (getOptString zkvm_tab "version")

  match zkvm_protocol_family with
  | "JAGGED"    =>
    let zkvm_circs ← orExit (getArray tbl "circuits")

    /-  List of Jagged circuits contained within the ZkVM -/
    let mut circuit_list : List JaggedCfg := []

    /- We parse all the [[circuits]] -/
    for circ in zkvm_circs do
      match circ with
      | .table' _ circ_tab =>
        /-
          We loop over all the [[circuit.lookups]]
          If no lookups are defined, we return an empty array instead of an error.
          If lookups is defined not as an array, we still error out.
        -/
        let circ_lookups ← orExit (getArrayD circ_tab "lookups" #[])
        let mut lookup_list : List LookupCfg := []

        for lookup in circ_lookups do
          match lookup with
          | .table' _ lookup_tab =>
            let lookupcfg ← parseLookupCfg lookup_tab zkvm_tab
            lookup_list := lookup_list.concat lookupcfg
          |_ => IO.eprintln "Unexpected non-table lookup item"; IO.Process.exit 1

        /- The last boolean parameter signals the FRIConfig should be parsed
           as per a Jagged circuit. (i.e., dense FRI params) -/
        let friConfig ← parseFRIConfig circ_tab zkvm_tab true
        let jaggedCfg ← parseJaggedCfg circ_tab zkvm_tab lookup_list friConfig
        circuit_list := circuit_list.concat jaggedCfg
      | _ => IO.eprintln "Unexpected non-table circuit item"; IO.Process.exit 1

    /- We compute a proof showing that the fields contained in all the
       circuits of the zkVM are consistent with each other. -/
    let h_circuits_lifted : PLift (circuit_list.all (·.field == zkvm_field) = true) ←
      match decEq (circuit_list.all (·.field == zkvm_field)) true with
      | .isTrue h  => pure (PLift.up h)
      | .isFalse _ => IO.eprintln "Circuit field mismatch: not all circuits share the zkVM's field"; IO.Process.exit 1

    let jaggedVM: JaggedVM := {
      name             := zkvm_name
      field            := zkvm_field
      version          := zkvm_version
      circuits         := circuit_list
      h_circuits_field := PLift.down (α := circuit_list.all (·.field == zkvm_field) = true) h_circuits_lifted
    }

    return jaggedVM
  | _           => IO.eprintln "The input toml does not contain a JAGGED zkVM."; IO.Process.exit 1

/--
  Parse a `DeepAliVM` from an input `.toml` file.
  If the `.toml` is invalid, the process errors out with an error message.
-/
def tomlToDeepAliVM (inTomlFile: String) : IO DeepAliVM := do
  let inToml ← IO.FS.readFile inTomlFile
  let ictx : InputContext := mkInputContext inToml inTomlFile
  let .ok tbl ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  /- Parsing [zkevm]-/
  let zkvm_tab ← orExit (getTable tbl "zkevm")

  let zkvm_name ← orExit (getString zkvm_tab "name")
  let zkvm_field ← orExit (getString zkvm_tab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)
  let zkvm_protocol_family ← orExit (getString zkvm_tab "protocol_family")
  let zkvm_version ← orExit (getOptString zkvm_tab "version")

  match zkvm_protocol_family with
  | "FRI_STARK"    =>
    let zkvm_circs ← orExit (getArray tbl "circuits")

    /-  List of DeepAli circuits contained within the ZkVM -/
    let mut circuit_list : List DeepAliCfg := []

    /- We parse all the [[circuits]] -/
    for circ in zkvm_circs do
      match circ with
      | .table' _ circ_tab =>
        /-
          We loop over all the [[circuit.lookups]]
          If no lookups are defined, we return an empty array instead of an error.
          If lookups is defined not as an array, we still error out.
        -/
        let circ_lookups ← orExit (getArrayD circ_tab "lookups" #[])
        let mut lookup_list : List LookupCfg := []

        for lookup in circ_lookups do
          match lookup with
          | .table' _ lookup_tab =>
            let lookupcfg ← parseLookupCfg lookup_tab zkvm_tab
            lookup_list := lookup_list.concat lookupcfg
          |_ => IO.eprintln "Unexpected non-table lookup item"; IO.Process.exit 1

        let friConfig ← parseFRIConfig circ_tab zkvm_tab false
        let deepAliCfg ← parseDeepAliCfg circ_tab zkvm_tab lookup_list friConfig
        circuit_list := circuit_list.concat deepAliCfg
      | _ => IO.eprintln "Unexpected non-table circuit item"; IO.Process.exit 1

    /- We compute a proof showing that the fields contained in all the
       circuits of the zkVM are consistent with each other. -/
    let h_circuits_lifted : PLift (circuit_list.all (·.field == zkvm_field) = true) ←
      match decEq (circuit_list.all (·.field == zkvm_field)) true with
      | .isTrue h  => pure (PLift.up h)
      | .isFalse _ => IO.eprintln "Circuit field mismatch: not all circuits share the zkVM's field"; IO.Process.exit 1

    let deepAliVM: DeepAliVM := {
      name         := zkvm_name
      version      := zkvm_version
      field        := zkvm_field
      circuits     := circuit_list
      h_circuits_field := PLift.down (α := circuit_list.all (·.field == zkvm_field) = true) h_circuits_lifted
    }
    return deepAliVM
  | _           => IO.eprintln "The input toml does not contain a DEEP-ALI (FRI-STARK) zkVM."; IO.Process.exit 1


/--
  Returns the zkVM family from an input `.toml` file.

  Errors out if the `.toml` is malformed.
-/
def tomlToVMFamily (inTomlFile: String) : IO String := do
  let inToml ← IO.FS.readFile inTomlFile
  let ictx : InputContext := mkInputContext inToml inTomlFile
  let .ok tbl ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  let zkvm_tab ← orExit (getTable tbl "zkevm")
  let zkvm_protocol_family ← orExit (getString zkvm_tab "protocol_family")

  pure zkvm_protocol_family

end SoundcalcIO
