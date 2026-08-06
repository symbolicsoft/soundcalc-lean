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

/--
  Returns an encoding of the LogUp string indexed by `key` if it exists in `tbl`.
  If a value is indexed by `key` but it is not a LogUp string or it does not exist, return an error.
-/
private def getLogUpBoolFromStr (tbl : Table) (key : String) : Except String Bool :=
  let s := getString tbl key
  match s with
  | .ok "univariate"   => .ok false
  | .ok "multivariate" => .ok true
  | _ => .error s!"key '{key}' is an invalid LogUp string."

/--
  Returns an encoding of the supported regime variable indexed by `key` if it exists in `tbl`.
  If a value is indexed by `key` but it is not a valid regime string, return an error.
-/
private def getOptRegime (tbl : Table) (key : String) : Except String (Option SupportedRegime) :=
  let s := getOptString tbl key
  match s with
  | .ok "unique" => .ok (SupportedRegime.UDR)
  | .ok "list"   => .ok (SupportedRegime.JBR)
  | .ok none     => .ok none
  | _ => .error s!"key '{key}' is an invalid supported regime string."

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

private def getOptFloat (tbl : Table) (key : String) : Except String (Option Float) :=
  match tbl.find? (.mkSimple key) with
  | some (.float _ f)   => .ok f
  | some _              => .error s!"key '{key}' exists but is not a float"
  | none                => .ok none

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
  ("BabyBear^4", babyBear4),
  ("Goldilocks^3", goldilocks3),
  ("KoalaBear^5", koalaBear5),
]

/--
  Maps strings to supported `FieldParams`.
-/
private def strToFieldParams (map : List (String × FieldParams)) (s : String) : Except String FieldParams :=
  match map.lookup s with
  | some fp => .ok fp
  | none    => .error s!"no FieldParams defined for '{s}'"

/--
  Returns the field from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.

  If any circuit-level conf is specified for `field`,
  it overrides the global zkVM configs.
  Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L85
-/
private def getCircField (circTab : Table)
                         (zkvmTab : Table) : IO FieldParams := do
  let zkvm_field_str ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field_str)

  let circ_field_str ← orExit (getOptString circTab "field")
  let circ_field ← match circ_field_str with
  | some s => orExit (strToFieldParams mapStrToFieldParams s)
  | none   => pure zkvm_field

  pure circ_field

/--
  Returns the hash bits from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.

  If any circuit-level conf is specified for `hash_size_bits`,
  it overrides the global zkVM configs.
  Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L81
-/
private def getCircHashBits (circTab : Table)
                            (zkvmTab : Table) : IO Nat := do
  let zkvm_hash_size_bits ← orExit (getNat zkvmTab "hash_size_bits")
  let circ_hash_size_bits ← orExit (getNatD circTab "hash_size_bits" zkvm_hash_size_bits)

  pure circ_hash_size_bits


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

  let circ_field ← getCircField circTab zkvmTab
  let circ_hash_bits ← getCircHashBits circTab zkvmTab

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
    hashBits          := circ_hash_bits
    ρ                 := circ_rho
    field             := circ_field
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
  Returns a `WHIRConfig` from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.

  Raises an error if any core fields are missing.
-/
private def parseWHIRConfig (circTab : Table)
                            (zkvmTab : Table) : IO WHIRConfig := do

  let circ_field ← getCircField circTab zkvmTab
  let circ_hash_bits ← getCircHashBits circTab zkvmTab

  let circ_l_skip ← orExit (getNat circTab "l_skip")
  let circ_n_stack ← orExit (getNat circTab "n_stack")

  let circ_w_stack ← orExit (getNat circTab "w_stack") -- aka: batch_size
  let h_batch_size : PLift (1 ≤ circ_w_stack) ←
  match Nat.decLe 1 circ_w_stack with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Condition violated: w_stack (aka batchSize) < 1"; IO.Process.exit 1

  let circ_log_blowup ← orExit (getNat circTab "log_blowup") -- aka: log_inv_rate
  let h_log_blowup : PLift (0 < circ_log_blowup) ←
  match Nat.decLt 0 circ_log_blowup with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Condition violated: log_blowup (aka logInv) ≤ 0"; IO.Process.exit 1

  let circ_whir_folding_pow_bits ← orExit (getNat circTab "whir_folding_pow_bits")
  let circ_whir_mu_pow_bits ← orExit (getNat circTab "whir_mu_pow_bits")
  let circ_whir_num_queries ← orExit (getListNat circTab "whir_num_queries")

  let circ_constraint_degree ← orExit (getNat circTab "constraint_degree")
  let h_constraint_degree : PLift (3 ≤ constraintDegree) ←
  match Nat.decLe 3 circ_constraint_degree with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Condition violated: constraint_degree < 3"; IO.Process.exit 1

  /- We dispense of Python's SWIRLWhirRoundConfig class. -/
  let rounds := circ_whir_num_queries

  let numIterations := rounds.length
  let h_num_iterations : PLift (1 ≤ numIterations) ←
  match Nat.decLe 1 numIterations with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Condition violated: numIterations < 1"; IO.Process.exit 1

  /-
    k = 4 is hardcoded in soundcalc. Ref:
    https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/circuits/swirl/calculator.py#L678  -/
  let foldingFactors := List.replicate numIterations 4
  let logDegree := circ_l_skip + circ_n_stack
  let h_sum_folding : PLift (foldingFactors.sum ≤ logDegree) ←
  match Nat.decLe foldingFactors.sum logDegree with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "sumFolding violation: foldingFactors.sum > circ_l_skip + circ_n_stack"; IO.Process.exit 1

  let field := circ_field
  let logInvRate := circ_log_blowup

  let h_two_adicity : PLift (logDegree + logInvRate - foldingFactors.headD 0 ≤ field.twoAdicity) ←
  match Nat.decLe (logDegree + logInvRate - foldingFactors.headD 0) field.twoAdicity with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "twoAdicity violation: logDegree + logInvRate - foldingFactors.headD 0 > field.twoAdicity"; IO.Process.exit 1

  let wcfg : WHIRConfig := {
    hashBits         := circ_hash_bits
    field            := field
    logInvRate       := logInvRate
    numIterations    := numIterations

    foldingFactors   := foldingFactors
    logDegree        := logDegree
    batchSize        := circ_w_stack
    /- Always power batches. Ref:
       https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L224
    -/
    powerBatch       := true
    grindBatch       := circ_whir_mu_pow_bits
    constraintDegree := circ_constraint_degree

    grindFolding     := List.replicate numIterations (List.replicate 4 circ_whir_folding_pow_bits) -- : List (List ℕ)
    numQueries       := rounds

    /- query_phase_pow_bits = 20 is hardcoded in soundcalc. Ref:
       https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/circuits/swirl/calculator.py#L681
    -/
    grindQueries     := List.replicate numIterations 20
    numOodSamples    := List.replicate (max (numIterations-1) (0)) 1
    grindOod         := List.replicate (max (numIterations-1) (0)) 0
    /- Trivial simp theorems are obtained by how the respective fields are constructed. -/
    h_constraintDegree   := PLift.down (α := 3 ≤ circ_constraint_degree) h_constraint_degree
    h_batchSize          := PLift.down (α := 1 ≤ circ_w_stack) h_batch_size
    h_logInvRate         := PLift.down (α := 0 < circ_log_blowup) h_log_blowup
    h_numIterations      := PLift.down (α := 1 ≤ numIterations) h_num_iterations
    h_foldingFactors_len := by simp [foldingFactors] -- foldingFactors.length = numIterations
    h_foldingFactors_pos := by simp [foldingFactors] -- ∀ k ∈ foldingFactors, 1 ≤ k
    h_sumFolding         := PLift.down (α := foldingFactors.sum ≤ logDegree) h_sum_folding -- foldingFactors.sum ≤ logDegree
    h_twoAdicity         := PLift.down (α := logDegree + logInvRate - foldingFactors.headD 0 ≤ field.twoAdicity) h_two_adicity -- logDegree + logInvRate - foldingFactors.headD 0 ≤ field.twoAdicity
    h_numOodSamples_len  := by simp  -- numOodSamples.length = numIterations - 1
    h_numQueries_len     := by simp [numIterations] -- numQueries.length = numIterations
    h_grindOod_len       := by simp  -- grindOod.length = numIterations - 1
    h_grindQueries_len   := by simp  -- grindQueries.length = numIterations
    h_grindFolding_len   := by simp  -- grindFolding.length = numIterations
    h_grindFolding_inner := fun i hi => by -- ∀ i < numIterations, (grindFolding.getD i []).length = foldingFactors.getD i 0
                              simp only [foldingFactors]
                              rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi),
                              List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi)]
                              simp
  }
  pure wcfg

/--
  Return a `Bounded` structure (as specified in `Soundcalc/Circuit/SWIRL/Circuit.lean`)
  for the `varName` field, which contains:
  - The actual value parsed from `varName`;
  - The soundness envelope value parsed from `soundness_{varName}` (if existing);
  - The proof size envelope value parsed from `proof_size_{varName}` (if existing);
  - A proof showing that `actual ≤ soundEnvelope`.
  - A proof showing that `actual ≤ proofEnvelope`.

  If no soundness envelope is specified, `soundcalc` defaults to the actual value.
  If no proof envelope is specified, `soundcalc` defaults to the soundness envelope value.
  Ref:
  https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L246
-/
private def getBoundedEnvelope (circTab: Table)
                               (varName: String) : IO Bounded := do
  let circ_actual ← orExit (getNat circTab varName)
  let circ_sound_envelope ← orExit (getNatD circTab s!"soundness_{varName}" circ_actual)
  let circ_proof_envelope ← orExit (getNatD circTab s!"proof_size_{varName}" circ_sound_envelope)

  let h_le_sound : PLift (circ_actual ≤ circ_sound_envelope) ←
  match Nat.decLe circ_actual circ_sound_envelope with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln s!"{varName} exceeds soundness_{varName}"; IO.Process.exit 1

  let h_le_proof : PLift (circ_actual ≤ circ_proof_envelope) ←
  match Nat.decLe circ_actual circ_proof_envelope with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln s!"{varName} exceeds proof_size_{varName}"; IO.Process.exit 1

  let bounded : Bounded := {
    actual := circ_actual
    soundEnvelope := circ_sound_envelope
    proofEnvelope := circ_proof_envelope
    h_le_sound := (PLift.down (α := circ_actual ≤ circ_sound_envelope)) h_le_sound
    h_le_proof := (PLift.down (α := circ_actual ≤ circ_proof_envelope)) h_le_proof
  }

  pure bounded

/--
  Return a `BoundedSound` structure (as specified in `Soundcalc/Circuit/SWIRL/Circuit.lean`)
  for the `varName` field, which contains:
  - The actual value parsed from `varName`;
  - The soundness envelope value parsed from `soundness_{varName}` (if existing);
  - A proof showing that `actual ≤ soundEnvelope`.

  If no soundness envelope is specified, `soundcalc` defaults to the actual value.
  Ref:
  https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L246
-/
private def getBoundedSoundEnvelope (circTab: Table)
                                    (varName: String) : IO BoundedSound := do
  let circ_actual ← orExit (getNat circTab varName)
  let circ_sound_envelope ← orExit (getNatD circTab s!"soundness_{varName}" circ_actual)

  let h_le_sound : PLift (circ_actual ≤ circ_sound_envelope) ←
  match Nat.decLe circ_actual circ_sound_envelope with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln s!"{varName} exceeds soundness_{varName}"; IO.Process.exit 1

  let boundedSound : BoundedSound := {
    actual := circ_actual
    soundEnvelope := circ_sound_envelope
    h_le_sound := (PLift.down (α := circ_actual ≤ circ_sound_envelope)) h_le_sound
  }

  pure boundedSound

/--
  Returns a `SWIRLCfg` from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, plus a general-config SWIRL table
  `swirlTab`, both parsed from a `.toml` file.
  The output `SWIRLCfg` also bundles its WHIR configuration (`wcfg`).

  soundcalc strictly ties SWIRL to WHIR (including, e.g., in some
  well-formedness checks).
  Ref:
  https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/circuits/swirl/circuit.py#L21
  **SOUNDCALC TODO**: generalize SWIRL to support arbitrary PCS schemes.

  Raises an error if any core fields are missing.
-/
private def parseSWIRLCfg (circTab : Table)
                          (zkvmTab : Table)
                          (swirlTab : Table)
                          (wcfg : WHIRConfig): IO SWIRLCfg := do
  /- Global zkVM values -/
  let zkvm_field ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)

  let circ_l_skip ← orExit (getNat circTab "l_skip")

  /- `explicit_m` is parsed only if explicit_regime is "list" -/
  let circ_explicit_regime ← orExit (getOptString circTab "explicit_regime")
  let circ_explicit_m ← match circ_explicit_regime with
  | some "list" => let explicit_m ← orExit (getNat circTab "explicit_m")
                   pure (some explicit_m)
  | _           => pure (none)

  let swirl_max_interaction_count ← orExit (getNat swirlTab "logup_max_interaction_count")
  let swirl_log_max_message_length ← orExit (getNat swirlTab "logup_log_max_message_length")
  let swirl_pow_bits ← orExit (getNat swirlTab "logup_pow_bits")

  /- If a circuit-specific `swirl_pow_bits` is specified, override the global configuration. -/
  let circ_pow_bits ← orExit (getNatD circTab "logup_pow_bits" swirl_pow_bits)

  let logupcfg : LogUpParams := {
    maxInteractionCount := swirl_max_interaction_count
    logMaxMessageLength := swirl_log_max_message_length
    powBits             := circ_pow_bits
  }

  let h_lskip_log : PLift (circ_l_skip ≤ wcfg.logDegree) ←
  match Nat.decLe circ_l_skip wcfg.logDegree with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "lskip_log violation: circ_l_skip > wcfg.logDegree"; IO.Process.exit 1


  let h_whir_fold : PLift (wcfg.numIterations * wcfg.foldingFactors.headD 0 ≤ wcfg.logDegree) ←
  match Nat.decLe (wcfg.numIterations * wcfg.foldingFactors.headD 0) wcfg.logDegree with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "whir_fold violation: wcfg.numIterations * wcfg.foldingFactors.headD 0 > wcfg.logDegree"; IO.Process.exit 1

  let circ_name ← orExit (getString circTab "name")

  /- Python supports full `Bounded` envelopes (i.e., `soundness_*` + `proof_size_*`)
     for all the fields below. -/
  let circ_num_airs ← getBoundedEnvelope circTab "num_airs"
  let circ_max_log_trace_height ← getBoundedEnvelope circTab "max_log_trace_height"
  let circ_num_trace_columns ← getBoundedEnvelope circTab "num_trace_columns"
  let circ_max_interactions_per_air ← getBoundedEnvelope circTab "max_interactions_per_air"

  /- Python supports only `BoundedSound` envelopes (i.e., `soundness_*` only)
     for the field below. -/
  let circ_max_constraints_per_air ← getBoundedSoundEnvelope circTab "max_constraints_per_air"

  /- We also require circ_num_airs ≥ 1. -/
  let h_airs : PLift (1 ≤ circ_num_airs.actual) ←
  match Nat.decLe 1 circ_num_airs.actual with
  | .isTrue h  => pure (PLift.up h)
  | .isFalse _ => IO.eprintln "Condition violated: circ_num_airs.actual < 1"; IO.Process.exit 1

  let circ_proof_size_num_public_values ← orExit (getNatD circTab "proof_size_num_public_values" 0)

  let h_wcfg_field : PLift (wcfg.field = zkvm_field) ←
  match decEq wcfg.field zkvm_field with
  | .isTrue h  => pure (PLift.up h : PLift (wcfg.field = zkvm_field))
  | .isFalse _ => IO.eprintln "WHIR field mismatch: wcfg.field ≠ circuit field"; IO.Process.exit 1

  let scfg : SWIRLCfg := {
    name := circ_name
    field := zkvm_field
    whir := wcfg
    h_whir_field := PLift.down (α := wcfg.field = zkvm_field) h_wcfg_field
    lSkip := circ_l_skip
    airs := circ_num_airs
    constraints := circ_max_constraints_per_air
    logTraceHeight := circ_max_log_trace_height
    traceColumns := circ_num_trace_columns
    interactions := circ_max_interactions_per_air
    logup := logupcfg
    explicitM := circ_explicit_m
    numPublicValues := circ_proof_size_num_public_values
    h_airs := PLift.down (α := 1 ≤ circ_num_airs.actual) h_airs
    h_lskip_log := PLift.down (α := circ_l_skip ≤ wcfg.logDegree) h_lskip_log
    h_whir_fold := PLift.down (α := wcfg.numIterations * wcfg.foldingFactors.headD 0 ≤ wcfg.logDegree) h_whir_fold
  }
  pure scfg

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

/--
  Returns a `JaggedCfg` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.
  The output `JaggedCfg` also bundles the list of lookups it contains
  (`lookupList`), as well as its PCS configuration (`PCSConfig`).

  Raises an error if any core fields are missing.
-/
private def parseJaggedCfg (circTab : Table)
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

/--
  Returns a `DeepAliCfg` from a lookup table `circTab` contained
  in a table `zkvmTab`, which is obtained from parsing a `.toml`
  file of a ZkVM configuration.
  The output `DeepAliCfg` also bundles the list of lookups it contains
  (`lookupList`), as well as its PCS configuration (`PCSconfig`).

  Raises an error if any core fields are missing.
-/
private def parseDeepAliCfg (circTab : Table)
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

/--
  Parse a `ZkVM` from an input `.toml` file.
  If the `.toml` is invalid, the process errors out with an error message.
-/
def tomlToZkVM (inTomlFile: String) : IO ZkVM := do
  let inToml ← IO.FS.readFile inTomlFile
  let ictx : InputContext := mkInputContext inToml inTomlFile
  let .ok tbl ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  /- Parsing [zkevm]-/
  let zkvm_tab ← orExit (getTable tbl "zkevm")

  let zkvm_name ← orExit (getString zkvm_tab "name")
  let zkvm_field ← orExit (getString zkvm_tab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)
  let zkvm_version ← orExit (getOptString zkvm_tab "version")
  let zkvm_circs ← orExit (getArray tbl "circuits")

  /-  List of Circuits contained within the ZkVM -/
  let mut circuit_list : List Circuit := []

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

      let circ_protocol_family ← orExit (getString circ_tab "protocol_family")

      /- The last boolean parameter signals the FRIConfig should be parsed
      as per a Jagged circuit. (i.e., dense FRI params)

      Following soundcalc, Jagged and DeepAli circuits are ALWAYS bundled with FRI,
      whereas SWIRL circuits are ALWAYS bundled with WHIR.
      Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L89

      **SOUNDCALC TODO** Allow for switching of PCS schemes.
      |-> Possible solution: add a PCS field explicitly within .toml files.
      -/
      let circuit ← match circ_protocol_family with
      | "JAGGED"    => let fcfg ← parseFRIConfig circ_tab zkvm_tab true
                       let jaggedCirc ← (parseJaggedCfg circ_tab zkvm_tab lookup_list (.fri fcfg))
                       pure (.jagged jaggedCirc)
      | "FRI_STARK" => let fcfg ← parseFRIConfig circ_tab zkvm_tab false
                       let deepAliCirc ← (parseDeepAliCfg circ_tab zkvm_tab lookup_list (.fri fcfg))
                       pure (.deepali deepAliCirc)
      | "SWIRL"     => let wcfg ← parseWHIRConfig circ_tab zkvm_tab
                       let swirl_tab ← orExit (getTable tbl "swirl")
                       let swirlCirc ← (parseSWIRLCfg circ_tab zkvm_tab swirl_tab wcfg)
                       pure (.swirl swirlCirc)
      | _           =>  IO.eprintln "Unsupported circuit family."; IO.Process.exit 1


      circuit_list := circuit_list.concat circuit
    | _ => IO.eprintln "Unexpected non-table circuit item"; IO.Process.exit 1

  /- We compute a proof showing that the fields contained in all the
      circuits of the zkVM are consistent with each other. -/
  let h_circuits_lifted : PLift (circuit_list.all (·.field == zkvm_field) = true) ←
    match decEq (circuit_list.all (·.field == zkvm_field)) true with
    | .isTrue h  => pure (PLift.up h)
    | .isFalse _ => IO.eprintln "Circuit field mismatch: not all circuits share the zkVM's field"; IO.Process.exit 1

  let zkVM : ZkVM := {
    name             := zkvm_name
    field            := zkvm_field
    version          := zkvm_version
    circuits         := circuit_list
    h_circuits_field := PLift.down (α := circuit_list.all (·.field == zkvm_field) = true) h_circuits_lifted
  }
  pure zkVM

end SoundcalcIO
