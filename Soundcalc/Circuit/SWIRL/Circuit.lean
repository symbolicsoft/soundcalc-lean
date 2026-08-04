import Mathlib
import Soundcalc.PCS.WHIR

open Soundcalc

/-!
# SWIRL circuit — configuration

Port of `soundcalc/circuits/swirl/circuit.py` (config shape) with the parameter plumbing from
`zkvms/zkvm.py`. SWIRL is the OpenVM2 proof system — LogUp-GKR + ZeroCheck + a stacked reduction,
opened with a **WHIR** PCS. This file defines the circuit config `SWIRLCfg` and the derived
accessors that mirror the `zkvm.py` construction; the proof-size and soundness formulas live in
`SWIRL/ProofSize.lean` and `SWIRL/ComputeError.lean`.

References:
- SWIRL paper: https://openvm.dev/swirl.pdf
- OpenVM2 soundness: https://github.com/openvm-org/stark-backend/blob/develop-v2/crates/stark-backend/src/soundness.rs
-/

namespace Soundcalc

/-- An actual circuit value with the conservative `envelope` the formulas use, certified
`actual ≤ envelope` (a check Python omits). -/
structure Bounded where
  /-- Actual value (Python MAIN; display-only, feeds no formula). -/
  actual   : ℕ
  /-- Envelope (Python `soundness_*` = `proof_size_*`); every formula reads this. -/
  envelope : ℕ
  h_le     : actual ≤ envelope := by decide

/-- LogUp interaction soundness params (`[swirl]` table / `SWIRLLogUpSecurityParameters`). -/
structure LogUpParams where
  /-- interaction-count cap (`logup_max_interaction_count`). -/
  maxInteractionCount : ℕ
  /-- `log₂` of the max message length (`logup_log_max_message_length`). -/
  logMaxMessageLength : ℕ
  /-- proof-of-work bits (`logup_pow_bits`). -/
  powBits             : ℕ

/-- A SWIRL circuit: its WHIR PCS instance plus the SWIRL-specific shape. Each AIR/trace bound is
a `Bounded` — the actual circuit value together with the soundness/proof-size *envelope* the
formulas use. Every soundness-error and proof-size formula reads the `.envelope`; computing
against the upper bound is the conservative claim. Parameters the WHIR PCS already carries
(rates, degrees, pow bits, …) are read back through the accessors below, not duplicated. -/
structure SWIRLCfg where
  name             : String
  field            : FieldParams
  /-- The WHIR PCS instance (`zkvm.py`): `logInvRate = log_blowup`, `logDegree = l_skip+n_stack`,
      `batchSize = w_stack`, `foldingFactors = [k]*rounds`, pow bits in the grinding arrays. -/
  whir          : WHIRConfig
  /-- `l_skip`: log-size of the univariate "skip" coset. -/
  lSkip         : ℕ
  /-- Number of AIRs (actual + envelope). -/
  airs          : Bounded
  /-- Maximum `log₂(trace height)` (actual + envelope). -/
  logTraceHeight : Bounded
  /-- Total trace columns opened in the stacked reduction (actual + envelope). -/
  traceColumns  : Bounded
  /-- Maximum interactions per AIR / LogUp-GKR width (actual + envelope). -/
  interactions  : Bounded
  /-- Maximum constraints per AIR (actual + envelope). -/
  constraints   : Bounded
  /-- LogUp interaction soundness params (`SWIRLLogUpSecurityParameters`). -/
  logup         : LogUpParams
  /-- Public values (base-field elements) in the proof preamble. -/
  numPublicValues : ℕ := 0
  /-- Decoding regime: `none` = unique (UDR); `some m` = list at multiplicity `m` (JBR). -/
  explicitM     : Option ℕ := none
  /-- Well-formedness, auto-discharged at construction (≥ 1 AIR, `l_skip ≤ log_degree`, and no
      over-fold `rounds·k ≤ log_degree`); per-bound `actual ≤ envelope` checks live in `Bounded`. -/
  h_airs        : 1 ≤ airs.actual := by decide
  h_lskip_log   : lSkip ≤ whir.logDegree := by decide
  h_whir_fold   : whir.numIterations * whir.foldingFactors.headD 0 ≤ whir.logDegree := by decide
  /- The theorems below enforce coherency between fields
      included in different data structures. -/
  h_whir_field : whir.field = field := by rfl


/-! ## Derived SWIRL quantities (the `zkvm.py` correspondences, read back from `whir`) -/

/-- `w_stack`, the number of stacked columns (`= whir.batch_size`). -/
def SWIRLCfg.wStack (c : SWIRLCfg) : ℕ := c.whir.batchSize
/-- `log_blowup = μ₀ = whir.log_inv_rate`. -/
def SWIRLCfg.logBlowup (c : SWIRLCfg) : ℕ := c.whir.logInvRate
/-- WHIR folding factor `k` (constant across rounds in SWIRL; `= whir.folding_factors[0]`). -/
def SWIRLCfg.k (c : SWIRLCfg) : ℕ := c.whir.foldingFactors.headD 0
/-- `n_stack = log_stacked_height − l_skip`. -/
def SWIRLCfg.nStack (c : SWIRLCfg) : ℕ := c.whir.logDegree - c.lSkip
/-- `max_constraint_degree = whir.constraint_degree` (same TOML `constraint_degree`). -/
def SWIRLCfg.maxConstraintDegree (c : SWIRLCfg) : ℕ := c.whir.constraintDegree
/-- WHIR μ-batching PoW bits (`= whir.grindBatch`). -/
def SWIRLCfg.muPowBits         (c : SWIRLCfg) : ℕ := c.whir.grindBatch
/-- WHIR folding PoW bits, constant across rounds (`= whir.grindFolding[0][0]`). -/
def SWIRLCfg.foldingPowBits    (c : SWIRLCfg) : ℕ := (c.whir.grindFolding.headD []).headD 0
/-- WHIR query-phase PoW bits, constant across rounds (`= whir.grindQueries[0]`). -/
def SWIRLCfg.queryPhasePowBits (c : SWIRLCfg) : ℕ := c.whir.grindQueries.headD 0

/-- `calculate_n_logup_bound`: `max(min(field_bound, param_bound), 0)` where
`field_bound = ⌈log₂ maxIntCount⌉ − l_skip` and
`param_bound = ⌈log₂ num_airs⌉ + ⌈log₂ maxIntPerAir⌉ + max_log_trace_height − l_skip`.
(In ℕ the truncated subtractions plus `min` already realise Python's outer `max(·, 0)`.) Shared
by the GKR proof-size section and the constraint-batching error. -/
def swNLogupBound (lSkip numAirs maxIntPerAir maxLogTraceHeight maxIntCount : ℕ) : ℕ :=
  let fieldBound := Nat.clog 2 maxIntCount - lSkip
  let paramBound := (Nat.clog 2 numAirs + Nat.clog 2 maxIntPerAir + maxLogTraceHeight) - lSkip
  min fieldBound paramBound

-- Concrete SWIRL circuit instances (OpenVM2's app/leaf/internal_*/hook/root, zkDTVM's
-- root_shrink) and their proof-size / soundness checks against the reports live in the per-zkVM
-- files, not here. Both halves are validated: OpenVM2 `app` (unique regime) reproduces
-- `reports/openvm2.md`'s 26175 KiB proof size and its entire UDR security row (total 100) exactly.

end Soundcalc
