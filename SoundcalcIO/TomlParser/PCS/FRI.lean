import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml

/-
  We work in the `Soundcalc` namespace to extend `FRIConfig` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc

/--
  Returns a `FRIConfig` from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.
  The `isJagged` boolean signals whether the FRIConfig should be initialized
  as per a Jagged VM (i.e., using `dense_length`, `dense_batch`) or not
  (`trace_length`, `batch_size`).

  Raises an error if any core fields are missing.
-/
def FRIConfig.parseFromToml (circTab : Table)
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

end Soundcalc
