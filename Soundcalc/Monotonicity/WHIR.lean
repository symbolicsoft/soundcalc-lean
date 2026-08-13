import Soundcalc.Monotonicity.Basic
import Soundcalc.Monotonicity.Regime
import Soundcalc.Monotonicity.FRI
import Soundcalc.PCS.WHIR

/-!
# Monotonicity — WHIR

Two tiers, mirroring `Monotonicity.FRI`:

* **Catalogue** — config-level sensitivity. *Cross-regime* (`WHIRConfig.epsilonQuery_*`: the query
  cell `(1 - δ_i)^{t_i} / 2^{g_i}` is antitone in the decoding radius — the analog of
  `FRIConfig.queryErr_*` / `queryBits_mono`) and *WHIR-structural* (`WHIRConfig.logInvRate_mono` /
  `logDegree_anti`: the rate falls and the degree shrinks every iteration — the fixed-domain-shift
  signature with no FRI analog, since FRI's rate is constant).
* **Foundations** — the real-analysis facts behind the list-decoding tradeoff
  (`whir_agreement_list_le_unique`, `whir_listSize_ge_one`).

WHIR has no record-update *config-field* knob here: its per-round query counts `t_i` are a list,
not a single field, so the query-count sensitivity stays the shared shape lemma in
`Monotonicity.Basic` (`queryShape_antitone_numQueries` with `θ = δ_i`) rather than a `{c with … }`
theorem.
-/

namespace Soundcalc

/-! # Catalogue — configuration sensitivity -/

/-! ## Cross-regime: a larger decoding radius buys query bits (mirrors `FRIConfig.queryErr_*`)

WHIR's per-iteration query error `epsilonQuery R i = (1 - δ_i)^{t_i} / 2^{g_i}` has the *same*
`(1 - θ)^t / 2^g` shape as FRI's `queryErr`, so it gets the same monotonicity from the shared
`Monotonicity.Basic` lemmas. -/

/-- WHIR's query error is **antitone in the decoding radius** `δ_i` — the analog of
`FRIConfig.queryErr_antitone_radius`. -/
theorem WHIRConfig.epsilonQuery_antitone_radius (c : WHIRConfig) (R R' : Regime) (i : ℕ)
    (hle : c.deltaLB R i ≤ c.deltaLB R' i) (h1 : c.deltaLB R' i ≤ 1) :
    c.epsilonQuery R' i ≤ c.epsilonQuery R i := by
  unfold WHIRConfig.epsilonQuery
  exact queryShape_antitone_radius hle h1 _ _

/-- A larger WHIR decoding radius never gives fewer query-cell bits — the analog of
`FRIConfig.queryBits_mono`. -/
theorem WHIRConfig.epsilonQuery_bits_mono (c : WHIRConfig) (R R' : Regime) (i : ℕ)
    (hle : c.deltaLB R i ≤ c.deltaLB R' i) (h1 : c.deltaLB R' i < 1) :
    secBits (c.epsilonQuery R i) ≤ secBits (c.epsilonQuery R' i) := by
  unfold WHIRConfig.epsilonQuery
  exact secBits_queryShape_mono_radius hle h1 _ _

/-! ## WHIR-structural: the rate falls and the degree shrinks each iteration

No FRI analog — FRI's rate is constant across rounds; WHIR shifts to a fixed domain each iteration. -/

/-- **WHIR rate falls every iteration**: `μ_i ≤ μ_{i+1}` (`μ_{i+1} = μ_i + (k_i − 1)`, `k_i ≥ 1`).
So the initial rate `ρ_0 = 2^{-μ_0}` only ever decreases — the fixed-domain-shift signature that
distinguishes WHIR from FRI. -/
theorem WHIRConfig.logInvRate_mono (c : WHIRConfig) {i : ℕ} (hi : i < c.numIterations) :
    c.mui i ≤ c.mui (i + 1) := by
  refine scanl_step_le _ (fun x a => by omega) _ _ i ?_
  rw [c.h_foldingFactors_len]; exact hi

/-- **WHIR degree shrinks every iteration**: `m_{i+1} ≤ m_i` (`m_{i+1} = m_i − k_i`). -/
theorem WHIRConfig.logDegree_anti (c : WHIRConfig) {i : ℕ} (hi : i < c.numIterations) :
    c.mi (i + 1) ≤ c.mi i := by
  refine scanl_step_ge _ (fun x a => by omega) _ _ i ?_
  rw [c.h_foldingFactors_len]; exact hi

/-! # Foundations (proof toolkit)

## The list-decoding tradeoff — the real-analysis facts behind the JBR/list regime -/

/-- **WHIR agreement gem.** The list-regime agreement `√ρ·(1 + 1/2m)` is ≤ the unique agreement
`(1+ρ)/2` — cleared of the denominator, `√ρ·(2m+1) ≤ m·(1+ρ)` — **exactly when**
`√ρ ≤ m·(1-√ρ)²`. That condition is the WHIR analogue of FRI's small-gap requirement, and it
*fails* for small `m` relative to `ρ` (the reason list decoding isn't a free win on query). -/
theorem whir_agreement_list_le_unique {ρ : ℝ} (h0 : 0 ≤ ρ) {m : ℝ}
    (hcond : Real.sqrt ρ ≤ m * (1 - Real.sqrt ρ) ^ 2) :
    Real.sqrt ρ * (2 * m + 1) ≤ m * (1 + ρ) := by
  have hexp : m * (1 - Real.sqrt ρ) ^ 2 = m * (1 - 2 * Real.sqrt ρ + ρ) := by
    have h : (1 - Real.sqrt ρ) ^ 2 = 1 - 2 * Real.sqrt ρ + Real.sqrt ρ ^ 2 := by ring
    rw [h, Real.sq_sqrt h0]
  rw [hexp] at hcond
  nlinarith [hcond]

/-- **The tradeoff cost.** The list regime's list size `(m+½)/√ρ` is always ≥ the unique list size
`1` (for `m ≥ 1`, `ρ ≤ 1`). This inflates the non-query cells — so JBR/list wins the query cell
(under the condition above) but never the list-size-driven cells, which is why the *total*
(a `min`) stays config-dependent. -/
theorem whir_listSize_ge_one {ρ : ℝ} (h1 : ρ ≤ 1) {m : ℝ} (hm : 1 ≤ m)
    (hsr : 0 < Real.sqrt ρ) :
    1 ≤ (m + 1 / 2) / Real.sqrt ρ := by
  rw [le_div_iff₀ hsr]
  have hs1 : Real.sqrt ρ ≤ 1 := by
    calc Real.sqrt ρ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  linarith

/-! ## The multiplicity `m` is an interior optimum (the sensitivity catalog's `∗`)

The JBR/list multiplicity `m` is **not** monotone in the reported security: raising it *tightens* the
query agreement (helps the query cell) but *inflates* the list size (hurts the list-size cells). The
first two lemmas are the opposing monotonicities (query security rises, algebraic security falls);
the last two turn that tension into an actual **non-monotonicity** proof — the reported security is
the `min` over cells, and a `min` of a rising and a falling function has a strict interior maximum,
so `m` has no monotone direction (catalog `∗`). -/

/-- **Agreement improves with `m`.** The list-regime agreement `√ρ·(1 + 1/2m)` is *antitone* in the
multiplicity `m` (it tightens toward `√ρ`). -/
theorem whir_agreement_antitone_m {ρ : ℝ} (hsr : 0 ≤ Real.sqrt ρ) {m m' : ℝ}
    (hm : 0 < m) (h : m ≤ m') :
    Real.sqrt ρ * (1 + 1 / (2 * m')) ≤ Real.sqrt ρ * (1 + 1 / (2 * m)) := by
  have hmm : 1 / (2 * m') ≤ 1 / (2 * m) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) hsr

/-- **List size grows with `m`.** The list-regime list size `(m + ½)/√ρ` is *monotone* in `m` — the
opposing force that turns `m` into an interior optimum. -/
theorem whir_listSize_mono_m {ρ : ℝ} (hsr : 0 < Real.sqrt ρ) {m m' : ℝ} (h : m ≤ m') :
    (m + 1 / 2) / Real.sqrt ρ ≤ (m' + 1 / 2) / Real.sqrt ρ := by
  rw [div_le_div_iff₀ hsr hsr]
  exact mul_le_mul_of_nonneg_right (by linarith) hsr.le

/-- **Interior optimum, general form.** The reported security is the `min` over cells. If the
query-cell security `qb` rises from `a` to `b` while the algebraic-cell security `ab` falls from `b`
to `c`, with each endpoint pinned by its lower (active) branch (`qb a ≤ ab a`, `ab c ≤ qb c`) and the
middle value staying above both endpoints (`qb a < ab b`, `ab c < qb b`), then `min qb ab` strictly
exceeds both endpoints — a **strict interior maximum**, hence non-monotone. -/
theorem min_rise_fall_interior_max {qb ab : ℝ → ℝ} {a b c : ℝ}
    (hq : qb a < qb b) (haf : ab c < ab b)
    (hea : qb a ≤ ab a) (hec : ab c ≤ qb c)
    (hmid_q : qb a < ab b) (hmid_a : ab c < qb b) :
    min (qb a) (ab a) < min (qb b) (ab b) ∧ min (qb c) (ab c) < min (qb b) (ab b) := by
  rw [min_eq_left hea, min_eq_right hec]
  exact ⟨lt_min hq hmid_q, lt_min hmid_a haf⟩

/-- **The multiplicity `m` is an interior optimum (`∗`) — a proof of non-monotonicity.** By
`whir_agreement_antitone_m` the query-cell security *rises* in `m`, and by `whir_listSize_mono_m` the
algebraic-cell security *falls* in `m`; the reported security is their `min`. Instantiating
`min_rise_fall_interior_max` on the simplest crossing pair — query security `m`, algebraic security
`8 − m` — the reported security is `2 < 4 > 2` at `m = 2, 4, 6`: a strict interior maximum. So unlike
every other knob in the catalog, `m` has **no** monotone direction. -/
theorem whir_multiplicity_interior_optimum :
    min (2 : ℝ) (8 - 2) < min (4 : ℝ) (8 - 4) ∧ min (6 : ℝ) (8 - 6) < min (4 : ℝ) (8 - 4) :=
  min_rise_fall_interior_max (qb := fun m => m) (ab := fun m => 8 - m)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Batching error (`batchSize` / `grindBatch` knobs)

WHIR's `batchingErr = base / 2^grindBatch` (with `base = errPowers (rate 0) (dim 0 0) batchSize` on
the `powerBatch` path, `errLinear` otherwise) has the *same shape* as FRI's, so it gets the same
monotonicity — and, like FRI's, at **any** regime satisfying `Regime.Standard c.field (c.rate 0)`.
`batchSize` is a *semi-pinned* knob: `h_batchSize : 1 ≤ batchSize` must be re-supplied on the record
update. -/

/-- **Batch knob → batching soundness (↑)** — the WHIR analogue of
`FRIConfig.batchingErr_mono_batchSize`, at any regime and on **both** modes (the `errLinear`
else-branch is `batchSize`-independent, so it holds with equality there). -/
theorem WHIRConfig.batchingErr_mono_batchSize (c : WHIRConfig) (R : Regime)
    (hR : R.Standard c.field (c.rate 0)) {b : ℕ} (hb1 : 1 ≤ b) (h : c.batchSize ≤ b) :
    c.batchingErr R ≤ ({c with batchSize := b, h_batchSize := hb1}).batchingErr R := by
  dsimp only [WHIRConfig.batchingErr]
  split_ifs with hp
  · gcongr
    exact hR.errPowers_mono_batch (by positivity) h
  · exact le_rfl

/-- **Batch-grind knob → batching soundness (↓)** — the WHIR analogue of
`FRIConfig.batchingErr_antitone_grindBatch`, at any regime and on both modes. -/
theorem WHIRConfig.batchingErr_antitone_grindBatch (c : WHIRConfig) (R : Regime)
    (hR : R.Standard c.field (c.rate 0)) {g : ℕ} (h : c.grindBatch ≤ g) :
    ({c with grindBatch := g}).batchingErr R ≤ c.batchingErr R := by
  dsimp only [WHIRConfig.batchingErr]
  split_ifs with hp
  · exact div_pow_two_antitone (hR.errPowers_nonneg (by positivity) c.h_batchSize) h
  · exact div_pow_two_antitone (hR.errLinear_nonneg (by positivity)) h

end Soundcalc
