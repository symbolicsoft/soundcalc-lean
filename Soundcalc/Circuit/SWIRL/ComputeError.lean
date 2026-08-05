import Soundcalc.Circuit.SWIRL.Circuit
import Soundcalc.Circuit.SWIRL.ProofSize  -- proofSizeBits, for the bundled ExitCriteria
import Soundcalc.Common.Sqrt  -- sqrtLB / sqrtUB (list-decoding √ρ estimates)

open Soundcalc

/-!
# SWIRL circuit — soundness errors

Port of `calculator.py` (`calculate_swirl_soundness`): six SWIRL components (logup, GKR-sumcheck,
GKR-batching, zerocheck, constraint-batching, stacked-reduction) plus WHIR's round-by-round
model; total security = min bits = **max error `ε`**.

`calculator.py` uses float `log₂`-bits; we carry each `ε : ℚ` and take `secBits ε`. Since every
bits formula is `challenge_field_bits − log₂(D) − log₂(list) + effpow` and `challenge_field_bits =
log₂(card)`, `ε = D·list·2^(−effpow)/card` with no irrational `log₂ p`. Unique-decoding
(`explicitM = none`) is exact; the list-decoding path (`explicitM = some m`) replaces each `√ρ`
by the `sqrtLB`/`sqrtUB` enclosure in whichever direction makes the resulting error an upper
bound (see the per-definition docstrings below).
-/

namespace Soundcalc

/-- `√ρ` estimation granularity for the list-decoding regime (as in the WHIR JBR regime). -/
def swSqrtG : ℕ := 2 ^ 40
/-- `ρ = 2^(−log_inv_rate)`. -/
def swRho (logInvRate : ℕ) : ℚ := 1 / 2 ^ logInvRate

/-- `2^(−effpow)` as a rational factor on the error (`_effective_pow_bits` grinding):
`effpow = −log₂ p_hi`, `p_hi = (⌊p/2^b⌋+1)/p`, so the factor is `p_hi`. `b = 0` ⇒ no grinding. -/
def swEffpowFactor (F : FieldParams) (powBits : ℕ) : ℚ :=
  if powBits = 0 then 1 else (((F.p / 2 ^ powBits : ℕ) + 1 : ℕ) : ℚ) / (F.p : ℚ)

/-- `_max_agreement`: unique ⇒ `(1+ρ)/2` (exact); list ⇒ `√ρ·(1 + 1/(2m))` (√ρ upper bound, the
conservative — larger — direction for query error). Clamped at `1`. -/
def SWIRLCfg.maxAgreement (c : SWIRLCfg) (logInvRate : ℕ) : ℚ :=
  min 1 <|
    match c.explicitM with
    | none   => (1 + swRho logInvRate) / 2
    | some m => sqrtUB (swRho logInvRate) swSqrtG * (1 + 1 / (2 * ((max m 1 : ℕ) : ℚ)))

/-- List size `ℓ`: unique ⇒ `1`; list ⇒ `(m+½)/√ρ` (`= (m+½)·2^{log_inv_rate/2}`, the BCHKS25
`d_y`), using the √ρ *lower* bound so `ℓ` is a conservative *upper* bound. -/
def SWIRLCfg.listSize (c : SWIRLCfg) (logInvRate : ℕ) : ℚ :=
  match c.explicitM with
  | none   => 1
  | some m => (((max m 1 : ℕ) : ℚ) + 1 / 2) / sqrtLB (swRho logInvRate) swSqrtG

/-- `|F_ext| = p^e` as a rational — the shared denominator of every error. -/
def SWIRLCfg.card (c : SWIRLCfg) : ℚ := (c.whir.field.card : ℚ)

/-- `ℓ`: the initial proximity-gap list size (`listSize log_blowup`) the SWIRL components use. -/
def SWIRLCfg.initListSize (c : SWIRLCfg) : ℚ := c.listSize c.logBlowup

/-- The BCHKS25 list-decoding proximity bound `a` (`_log2_a_bound_bchks25`, in linear space):
`a = ⌈2·d_x·d_y²·d_z + d_y·(γ·N + 1)⌉` with `N = 2^{m+μ}`, `d_x = m̄·2^m/√ρ`, `d_y = m̄/√ρ`,
`d_z = max(d_y, m̄²·2^μ/3)`, `γ = 1 − √ρ − √ρ/(2m)`. Uses `sqrtLB ρ` for `√ρ` (conservative:
larger `a` ⇒ larger error). The float guards (returning `+∞`) are omitted — a finite `a` only
makes the bound *more* conservative. -/
def swBchks25ABound (logDegree logInvRate m : ℕ) : ℚ :=
  let sr   := sqrtLB (swRho logInvRate) swSqrtG          -- √ρ (lower bound)
  let mEff := (max m 1 : ℕ)
  let mBar := (mEff : ℚ) + 1 / 2
  let N    := (2 : ℚ) ^ (logDegree + logInvRate)
  let dx   := mBar * (2 : ℚ) ^ logDegree / sr
  let dy   := mBar / sr
  let dz   := max dy (mBar ^ 2 * (2 : ℚ) ^ logInvRate / 3)
  let eta  := sr / (2 * (mEff : ℚ))
  let gamma := 1 - sr - eta
  ((⌈2 * dx * dy ^ 2 * dz + dy * (gamma * N + 1)⌉ : ℤ) : ℚ)

/-- Proximity-gap error `ε` of the code `RS[log_degree, log_inv_rate]` batched over `batchSize`
functions (`_whir_proximity_gap_security`, converted to error space). `batchSize = 1` ⇒ no
batching challenge ⇒ error `0`. Unique regime is exact; list uses `bchks25ABound`. -/
def SWIRLCfg.proxGapErr (c : SWIRLCfg) (logDegree logInvRate batchSize : ℕ) : ℚ :=
  let card := c.card
  if batchSize ≤ 1 then 0 else
    let batch := ((batchSize - 1 : ℕ) : ℚ)
    match c.explicitM with
    | none   => batch * (2 : ℚ) ^ (logDegree + logInvRate) / card
    | some m => batch * swBchks25ABound logDegree logInvRate m / card

/-- Query error `ε` (`_whir_query_security_biased`, error space): `mass^t · 2^(−effpow)` where
`mass = α·(1 − r/p) + min(α·2^{lqd}, r)/p`, `α = maxAgreement`, `r = p mod 2^{lqd}` the "heavy"
residue count. `mass` is rational in the unique regime and `√ρ`-estimated in the list regime. -/
def SWIRLCfg.queryEps (c : SWIRLCfg) (numQueries logInvRate logQueryDomain : ℕ) : ℚ :=
  let p     := (c.whir.field.p : ℚ)
  let two   := (2 : ℚ) ^ logQueryDomain
  let r     := ((c.whir.field.p % 2 ^ logQueryDomain : ℕ) : ℚ)   -- heavy residues
  let alpha := c.maxAgreement logInvRate
  let heavyUsed := min (alpha * two) r
  let mass  := min 1 (alpha * (1 - r / p) + heavyUsed / p)
  mass ^ numQueries * swEffpowFactor c.whir.field c.queryPhasePowBits

/-- The named WHIR round-by-round errors (each the max `ε` over the relevant rounds/sub-rounds),
matching `reports/*.md`'s `whir_*` columns; `rbr` (the `whir` column) is the max over all. -/
structure SwirlWhirErrs where
  proxGaps      : ℚ
  sumcheck      : ℚ
  query         : ℚ
  gammaBatching : ℚ
  foldRbr       : ℚ
  shiftRbr      : ℚ
  ood           : ℚ
  muBatching    : ℚ
  rbr           : ℚ

/-- Port of `_calculate_whir_soundness` (error space). Threads `(current_log_degree,
log_inv_rate)` through the rounds: each round runs `k` fold sub-rounds (decrementing the degree,
accumulating prox-gaps / sumcheck / fold-rbr), then a query + γ-batching + shift-rbr, and (unless
final) an OOD error. `rbr`/`whir` is the max `ε` over `mu_batching`, every fold-rbr, every
shift-rbr, and every OOD. -/
def SWIRLCfg.whirErrs (c : SWIRLCfg) : SwirlWhirErrs :=
  let card      := c.card
  let k         := c.k
  let numRounds := c.whir.numIterations
  let foldFac   := swEffpowFactor c.whir.field c.foldingPowBits
  let muE       := c.proxGapErr c.whir.logDegree c.logBlowup c.wStack
                     * swEffpowFactor c.whir.field c.muPowBits
  let e0 : SwirlWhirErrs :=
    { proxGaps := 0, sumcheck := 0, query := 0, gammaBatching := 0,
      foldRbr := 0, shiftRbr := 0, ood := 0, muBatching := muE, rbr := muE }
  let step : ℕ × ℕ × SwirlWhirErrs → ℕ → ℕ × ℕ × SwirlWhirErrs := fun (cld, lir, e) i =>
    let isFinal  := i == numRounds - 1
    let nextRate := lir + (k - 1)
    let nq       := c.whir.numQueries.getD i 0
    let listCur  := c.listSize lir
    -- k fold sub-rounds (degree decreases by 1 each)
    let (cld, e) := (List.range k).foldl (fun (s : ℕ × SwirlWhirErrs) _ =>
      let (cld, e) := s
      let cld := cld - 1
      let pg  := c.proxGapErr cld lir 2 * foldFac
      let sc  := 3 * listCur * foldFac / card
      let fr  := sc + pg
      (cld, { e with proxGaps := max e.proxGaps pg, sumcheck := max e.sumcheck sc,
                     foldRbr := max e.foldRbr fr, rbr := max e.rbr fr })) (cld, e)
    let lqd      := cld + lir
    let q        := c.queryEps nq lir lqd
    let listNext := c.listSize nextRate
    let gb       := ((nq : ℚ) + 1) * listNext / card
    let sr       := q + gb
    let e := { e with query := max e.query q, gammaBatching := max e.gammaBatching gb,
                      shiftRbr := max e.shiftRbr sr, rbr := max e.rbr sr }
    let e := if isFinal then e else
      let ood := (2 : ℚ) ^ (cld - 1) * listNext ^ 2 / card
      { e with ood := max e.ood ood, rbr := max e.rbr ood }
    (cld, nextRate, e)
  (((List.range numRounds).foldl step (c.whir.logDegree, c.logBlowup, e0)).2).2

/-! ## The six SWIRL (non-WHIR) components. `ℓ = listSize log_blowup` (the initial prox-gap list
size); `card = |F_ext| = p^e`. -/

/-- `logup`: `2·max_interaction_count·max_message_length·ℓ / card`, ground by `logup_pow_bits`. -/
def SWIRLCfg.logupErr (c : SWIRLCfg) : ℚ :=
  2 * (c.logup.maxInteractionCount : ℚ) * ((2 ^ c.logup.logMaxMessageLength : ℕ) : ℚ)
    * c.initListSize * swEffpowFactor c.whir.field c.logup.powBits
    / c.card

/-- `gkr_sumcheck`: degree-3 sub-round, `3 / card`. -/
def SWIRLCfg.gkrSumcheckErr (c : SWIRLCfg) : ℚ := 3 / c.card

/-- `gkr_batching`: degree-1 (a no-op), `1 / card`. -/
def SWIRLCfg.gkrBatchingErr (c : SWIRLCfg) : ℚ := 1 / c.card

/-- `zerocheck_sumcheck`: `max((d+1)(2^l−1), d+1)·ℓ / card` with `d = max_constraint_degree`. -/
def SWIRLCfg.zerocheckErr (c : SWIRLCfg) : ℚ :=
  let d := c.maxConstraintDegree
  (max ((d + 1) * (2 ^ c.lSkip - 1)) (d + 1) : ℚ) * c.initListSize / c.card

/-- `constraint_batching`: `max(fused_boundary_degree, 3·num_airs − 1)·ℓ / card`, where
`fused_boundary_degree = max(n_extra, 3) + (2^l−1) + (max_constraints_per_air − 1)`,
`n_extra = max(max_log_trace_height − l − n_logup, 0)`. -/
def SWIRLCfg.constraintBatchingErr (c : SWIRLCfg) : ℚ :=
  let nLogup := swNLogupBound c.lSkip c.airs.soundEnvelope c.interactions.soundEnvelope c.logTraceHeight.soundEnvelope
                  c.logup.maxInteractionCount
  let nExtra := (c.logTraceHeight.soundEnvelope - c.lSkip) - nLogup      -- max(n_trace − n_logup, 0) in ℕ
  let fusedBoundary := max nExtra 3 + (2 ^ c.lSkip - 1) + (c.constraints.soundEnvelope - 1)
  let batchSumcheck := 3 * c.airs.soundEnvelope - 1
  (max fusedBoundary batchSumcheck : ℚ) * c.initListSize / c.card

/-- `stacked_reduction`: `max(2·num_trace_columns, 2(2^l−1), 2)·ℓ / card`. -/
def SWIRLCfg.stackedReductionErr (c : SWIRLCfg) : ℚ :=
  (max (max (2 * c.traceColumns.soundEnvelope) (2 * (2 ^ c.lSkip - 1))) 2 : ℚ)
    * c.initListSize / c.card

/-- All SWIRL soundness errors (the report's per-component cells, as errors). The circuit's
total security is `secBits` of the max of this list. -/
def SWIRLCfg.listErrs (c : SWIRLCfg) : List ℚ :=
  let w := c.whirErrs
  -- `w_stack = 1` ⇒ no μ-batching challenge (error 0, infinite security), so — like the Python
  -- calculator — the `whir_mu_batching` cell is dropped from the row entirely.
  [c.logupErr, c.gkrSumcheckErr, c.gkrBatchingErr, c.zerocheckErr, c.constraintBatchingErr,
   c.stackedReductionErr]
  ++ (if c.wStack ≤ 1 then [] else [w.muBatching])
  ++ [w.foldRbr, w.proxGaps, w.sumcheck, w.shiftRbr, w.query, w.gammaBatching, w.ood, w.rbr]

/-- Total soundness error: the max over all components (⇒ min security bits). -/
def SWIRLCfg.totalErr (c : SWIRLCfg) : ℚ := (c.listErrs).foldr max 0

/-- Bundles a SWIRL circuit's exit criteria for report validation (mirroring
`DeepAliCfg.ExitCriteria`): the full per-cell security row (`(listErrs).map secBits`, in
`listErrs` column order), the total (min bits), and the proof size in KiB (expected = worst).
One `native_decide` on this `Prop` replaces the per-circuit proof-size / row / total examples;
the regime is fixed by the config's `explicitM`, so no `Regime` argument is needed. -/
abbrev SWIRLCfg.ExitCriteria (c : SWIRLCfg) (rowBits : List ℕ) (totalBits proofSizeKib : ℕ) : Prop :=
  (c.listErrs).map secBits = rowBits ∧
  secBits c.totalErr = totalBits ∧
  c.proofSizeBits / KIB = proofSizeKib

end Soundcalc
