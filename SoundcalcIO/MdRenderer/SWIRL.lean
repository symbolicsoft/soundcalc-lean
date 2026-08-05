import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Common

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `SWIRLCfg` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/--
  Output the first element of `c.whir.grindQueries`.
  This is always safe, as per the structural theorems of `WHIRConfig`.
-/
private def SWIRLCfg.getQueryPoWBits (c: SWIRLCfg) : Nat :=
  let grindQueries := c.whir.grindQueries

  let h_grindQueries_len := c.whir.h_grindQueries_len
  let h_numIterations := c.whir.h_numIterations
  let h_grindQueries_ne : grindQueries ≠ [] := by
    unfold grindQueries
    intro h
    rw [h] at h_grindQueries_len
    simp at h_grindQueries_len
    omega

  grindQueries.head h_grindQueries_ne

/--
  Output the first element of the first list of `c.whir.grindFolding`.
  This is always safe, as per the structural theorems of `WHIRConfig`.
-/
private def SWIRLCfg.getFoldingPoWBits (c: SWIRLCfg) : Nat :=
  let grindFolding := c.whir.grindFolding
  let foldingFactors := c.whir.foldingFactors

  let h_numIterations := c.whir.h_numIterations

  let h_grindFolding_len := c.whir.h_grindFolding_len
  let h_grindFolding_ne : grindFolding ≠ [] := by
    unfold grindFolding
    intro h
    rw [h] at h_grindFolding_len
    simp at h_grindFolding_len
    omega

  let h_grindFolding_inner := c.whir.h_grindFolding_inner
  let h_foldingFactors_pos := c.whir.h_foldingFactors_pos
  let h_foldingFactors_len := c.whir.h_foldingFactors_len

  /-
    We want to prove that `(grindFolding.head h_grindFolding_ne).head` is safe to call
    (i.e., that `grindFolding.head h_grindFolding_ne` is non-empty by construction).
    This boils down to prove `h_grindFolding_inner_ne` below.

    As part of the proof, we want to leverage `h_grindFolding_inner`:
      `∀ i < numIterations, (grindFolding.getD i []).length = foldingFactors.getD i 0`

    This requires multiple intermediate theorems to safely get rid of the `.getD`.
  -/

  -- Step 1: `grindFolding.getD 0 []` and `grindFolding.head h_v_ne` coincide in our setting.
  let h_get_eq : grindFolding.getD 0 [] = grindFolding.head h_grindFolding_ne := by
    match grindFolding, h_grindFolding_ne with
    | h :: t, _ => rfl

  -- Step 2: use `h_grindFolding_ne` at `i = 0`
  let h_grindFolding_inner_len : (grindFolding.head h_grindFolding_ne).length = foldingFactors.getD 0 0 := by
    rw [← h_get_eq]
    exact h_grindFolding_inner 0 h_numIterations

  -- Step 3: `factors.getD 0 0` is an actual member of `foldingFactors`
  let h_firstFactor_membership : foldingFactors.getD 0 0 ∈ foldingFactors := by
    have h_foldingFactors_lenpositive : 0 < foldingFactors.length := by
      rw [h_foldingFactors_len]; exact h_numIterations
    match foldingFactors, h_foldingFactors_lenpositive with
    | h :: t, _ => simp

  -- Step 4: the inner list has always positive length.
  let h_grindFolding_inner_lenpositive : 1 ≤ (grindFolding.head h_grindFolding_ne).length := by
    rw [h_grindFolding_inner_len]
    exact h_foldingFactors_pos (foldingFactors.getD 0 0) h_firstFactor_membership

  -- Step 5: we cast the theorem above to obtain our non-emptiness theorem.
  let h_grindFolding_inner_ne : (grindFolding.head h_grindFolding_ne) ≠ [] := by
    intro h
    rw [h] at h_grindFolding_inner_lenpositive
    simp at h_grindFolding_inner_lenpositive

  let foldingPowBits := (grindFolding.head h_grindFolding_ne).head h_grindFolding_inner_ne
  foldingPowBits

/--
  Mirrors Python's `get_report_parameter_lines` for SWIRL circuits.
  Currently-supported PCS: WHIR (as per `soundcalc`).
-/
def SWIRLCfg.renderCircParams (c: SWIRLCfg) : IO String := do
  let mut outStr := ""

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname c.whir.field)

  /- We interpret `c` as a generic `Circuit` to access dot-methods shared
     among multiple circuits (`gc.isUDR`, `gc.proofSysName`). -/
  let gc : Circuit := .swirl c

  let regimeStr := if gc.isUDR then "UDR" else "JBR"

  /- Mirrors Python's `_uses_soundness_bounds`. -/
  let soundnessBoundsStr :=
    if (c.constraints.actual, c.airs.actual, c.logTraceHeight.actual, c.traceColumns.actual, c.interactions.actual)
    != (c.constraints.soundEnvelope, c.airs.soundEnvelope, c.logTraceHeight.soundEnvelope, c.traceColumns.soundEnvelope, c.interactions.soundEnvelope)
    then
      s!"- Soundness max constraints per AIR: {c.constraints.soundEnvelope}\n" ++
      s!"- Soundness number of AIRs bound: {c.airs.soundEnvelope}\n" ++
      s!"- Soundness max log trace height bound: {c.logTraceHeight.soundEnvelope}\n" ++
      s!"- Soundness trace columns bound: {c.traceColumns.soundEnvelope}\n" ++
      s!"- Soundness max interactions per AIR bound: {c.interactions.soundEnvelope}\n"
    else
      ""

  /- Mirrors Python's `_uses_proof_size_bounds`. -/
  let proofSizeBoundsStr :=
    if (c.airs.actual, c.logTraceHeight.actual, c.traceColumns.actual, c.interactions.actual)
    != (c.airs.proofEnvelope, c.logTraceHeight.proofEnvelope, c.traceColumns.proofEnvelope, c.interactions.proofEnvelope)
    then
      s!"- Proof-size number of AIRs bound: {c.airs.proofEnvelope}\n" ++
      s!"- Proof-size max log trace height bound: {c.logTraceHeight.proofEnvelope}\n" ++
      s!"- Proof-size trace columns bound: {c.traceColumns.proofEnvelope}\n" ++
      s!"- Proof-size max interactions per AIR bound: {c.interactions.proofEnvelope}\n"
    else
      ""

  let mStr := match c.explicitM with
  | some m => s!"- `m`: {m}\n"
  | none   => ""

  outStr := outStr ++
  s!"- Proof system: {gc.proofSysName}\n" ++
  s!"- PCS: WHIR\n" ++
  s!"- Field: {fieldDisplayName}\n" ++
  s!"- Regime: {regimeStr}\n" ++
  s!"{mStr}" ++
  s!"- `l_skip`: {c.lSkip}\n" ++
  s!"- `n_stack`: {c.nStack}\n" ++
  s!"- `w_stack`: {c.wStack}\n" ++
  s!"- Log blowup: {c.logBlowup}\n" ++
  s!"- WHIR queries per round: {c.whir.numQueries}\n" ++
  s!"- WHIR folding PoW (bits): {c.getFoldingPoWBits}\n" ++
  s!"- WHIR query-phase PoW (bits): {c.getQueryPoWBits}\n" ++
  s!"- WHIR μ PoW (bits): {c.whir.grindBatch}\n" ++
  s!"- Max constraints per AIR: {c.constraints.actual}\n" ++
  s!"- Number of AIRs: {c.airs.actual}\n" ++
  s!"- Max log trace height: {c.logTraceHeight.actual}\n" ++
  s!"- Number of trace columns: {c.traceColumns.actual}\n" ++
  s!"- Max interactions per AIR: {c.interactions.actual}\n" ++
  s!"{soundnessBoundsStr}" ++
  s!"{proofSizeBoundsStr}" ++
  s!"- Proof-size public values bound: {c.numPublicValues}\n"

  pure outStr

/--
  Mirrors Python's `get_security_levels` for SWIRL circuits.
  Currently-supported PCS: WHIR (as per `soundcalc`).
-/
def SWIRLCfg.getSecurityLevels (c: SWIRLCfg) : IO (List (String × Nat)) := do
  let mut l : List (String × Nat) := []

  /- Minimum overall secBits -/
  l := l ++ [("total", (secBits (c.totalErr)))]
  l := l ++ [("constraint_batching", (secBits (c.constraintBatchingErr)))]
  l := l ++ [("gkr_batching", (secBits (c.gkrBatchingErr)))]
  l := l ++ [("gkr_sumcheck", (secBits (c.gkrSumcheckErr)))]
  l := l ++ [("logup", (secBits (c.logupErr)))]
  l := l ++ [("stacked_reduction", (secBits (c.stackedReductionErr)))]

  /-
   `soundcalc` encodes the rbr error as "whir"
   Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/circuits/swirl/calculator.py#L489
  -/
  l := l ++ [("whir", (secBits (c.whirErrs.rbr)))] --
  l := l ++ [("whir_fold_rbr", (secBits (c.whirErrs.foldRbr)))]
  l := l ++ [("whir_gamma_batching", (secBits (c.whirErrs.gammaBatching)))]
  if (c.wStack > 1) then l := l ++ [("whir_mu_batching", (secBits (c.whirErrs.muBatching)))]
  l := l ++ [("whir_ood_rbr", (secBits (c.whirErrs.ood)))]
  l := l ++ [("whir_proximity_gaps", (secBits (c.whirErrs.proxGaps)))]
  l := l ++ [("whir_query", (secBits (c.whirErrs.query)))]
  l := l ++ [("whir_shift_rbr", (secBits (c.whirErrs.shiftRbr)))]
  l := l ++ [("whir_sumcheck", (secBits (c.whirErrs.sumcheck)))]
  l := l ++ [("zerocheck_sumcheck", (secBits (c.zerocheckErr)))]
  pure l

end Soundcalc
