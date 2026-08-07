import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml

/-
  We work in the `Soundcalc` namespace to extend `SWIRLCfg` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc


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

def SWIRLCfg.parseFromToml (circTab : Table)
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

end Soundcalc
