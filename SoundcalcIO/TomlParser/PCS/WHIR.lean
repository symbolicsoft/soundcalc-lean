
import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common

import Lake.Toml.Data.Value

open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

open Lake.Toml

/-
  We work in the `Soundcalc` namespace to extend `WHIRConfig` with appropriate parsing methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `TomlParser`.
 -/
namespace Soundcalc

/--
  Returns a `WHIRConfig` from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.

  Raises an error if any core fields are missing.
-/
def WHIRConfig.parseFromToml (circTab : Table)
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


end Soundcalc
