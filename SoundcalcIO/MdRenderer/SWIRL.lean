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
open Soundcalc

/--
  Mirrors Python's `get_report_parameter_lines` for SWIRL circuits.
  Currently-supported PCS: WHIR (as per soundcalc).
-/
def SWIRLCfg.renderCircParams (c: SWIRLCfg) : IO String := do
  let mut outStr := ""

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname c.whir.field)

  /- We interpret `c` as a generic Circuit to access dot-methods shared
     among multiple circuits (`gc.isUDR`, `gc.proofSysName`). -/
  let gc : Circuit := .swirl c

  let regimeStr := if gc.isUDR then "UDR" else "JBR"

  /- Mirrors Python's `_uses_soundness_bounds` and `_uses_proof_size_bounds`. -/
  let soundnessBoundsStr :=
    if (c.constraints.actual, c.airs.actual, c.logTraceHeight.actual, c.traceColumns.actual, c.interactions.actual)
    != (c.constraints.envelope, c.airs.envelope, c.logTraceHeight.envelope, c.traceColumns.envelope, c.interactions.envelope)
    then
      s!"- Soundness max constraints per AIR: {c.constraints.envelope}\n" ++
      s!"- Soundness number of AIRs bound: {c.airs.envelope}\n" ++
      s!"- Soundness max log trace height bound: {c.logTraceHeight.envelope}\n" ++
      s!"- Soundness trace columns bound: {c.traceColumns.envelope}\n" ++
      s!"- Soundness max interactions per AIR bound: {c.interactions.envelope}\n" ++
      /- **TODO** Refactor once we introduce the values below in the SWIRLCfg structure. -/
      s!"- Proof-size number of AIRs bound: {c.airs.envelope}\n" ++
      s!"- Proof-size max log trace height bound: {c.logTraceHeight.envelope}\n" ++
      s!"- Proof-size trace columns bound: {c.traceColumns.envelope}\n" ++
      s!"- Proof-size max interactions per AIR bound: {c.interactions.envelope}\n"
    else
      ""

  /- *TODO*: minor polish. -/
  let queryPhasePowBits := c.whir.grindQueries.getD 0 0
  let foldingPowBitsStr := (c.whir.grindFolding.getD 0 [0]).getD 0 0

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
  s!"- WHIR folding PoW (bits): {foldingPowBitsStr}\n" ++
  s!"- WHIR query-phase PoW (bits): {queryPhasePowBits}\n" ++
  s!"- WHIR μ PoW (bits): {c.whir.grindBatch}\n" ++
  s!"- Max constraints per AIR: {c.constraints.actual}\n" ++
  s!"- Number of AIRs: {c.airs.actual}\n" ++
  s!"- Max log trace height: {c.logTraceHeight.actual}\n" ++
  s!"- Number of trace columns: {c.traceColumns.actual}\n" ++
  s!"- Max interactions per AIR: {c.interactions.actual}\n" ++
  s!"{soundnessBoundsStr}" ++
  s!"- Proof-size public values bound: {c.numPublicValues}\n"

  pure outStr

/--
  Mirrors Python's `get_security_levels` for SWIRL circuits.
  Currently-supported PCS: WHIR (as per soundcalc).
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
   soundcalc encodes the rbr error as "whir"
   Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/circuits/swirl/calculator.py#L489
  -/
  l := l ++ [("whir", (secBits (c.whirErrs.rbr)))] --
  l := l ++ [("whir_fold_rbr", (secBits (c.whirErrs.foldRbr)))]
  l := l ++ [("whir_gamma_batching", (secBits (c.whirErrs.gammaBatching)))]
  l := l ++ [("whir_mu_batching", (secBits (c.whirErrs.muBatching)))]
  l := l ++ [("whir_ood_rbr", (secBits (c.whirErrs.ood)))]
  l := l ++ [("whir_proximity_gaps", (secBits (c.whirErrs.proxGaps)))]
  l := l ++ [("whir_query", (secBits (c.whirErrs.query)))]
  l := l ++ [("whir_shift_rbr", (secBits (c.whirErrs.shiftRbr)))]
  l := l ++ [("whir_sumcheck", (secBits (c.whirErrs.sumcheck)))]
  l := l ++ [("zerocheck_sumcheck", (secBits (c.zerocheckErr)))]
  pure l

end Soundcalc
