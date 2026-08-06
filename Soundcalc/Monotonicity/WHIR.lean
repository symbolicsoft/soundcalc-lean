import Soundcalc.Monotonicity.Basic
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

end Soundcalc
