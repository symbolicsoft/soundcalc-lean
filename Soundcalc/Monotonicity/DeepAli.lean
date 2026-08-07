import Soundcalc.Monotonicity.Basic
import Soundcalc.Circuit.DeepAli

/-!
# Monotonicity — DEEP-ALI circuit cells

`aliErr = L⁺ · C / |F|` and
`deepErr = L⁺ · num / (|F| − H − D) / 2^grindDeep` with
`num = deg·(H + m_max − 1) + (H − 1)`, `H = traceLen`, `D = H/ρ`, `L⁺ = R.listSize`.

`DeepAliCfg` pins `field`, `densePCS`, `lookups` together via `h_densePCS_field` / `h_lookups_field`,
so the `|F|`, `ρ`, `H` columns are **not** record-update knobs here. The free knobs are
`numConstraints`, `airMaxDegree`, `maxCombo`, `grindDeep`; the list-size (`L`) column is cross-regime.
The DEEP cells carry the genuine side condition `|F| − H − D > 0` (the multi-point denominator).

* **Catalogue** — `aliErr` in `numConstraints ↑` and `listSize ↑`; `deepErr` in `grindDeep ↓`,
  `airMaxDegree ↑`, `maxCombo ↑`, and `listSize ↑`.
* **Foundations** — the same-denominator / denominator-antitone plumbing.
-/

namespace Soundcalc

/-! # Foundations (proof toolkit) -/

private theorem div_le_div_same {a b c : ℚ} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  rw [div_le_div_iff₀ hc hc]
  exact mul_le_mul_of_nonneg_right h hc.le

/-! # Catalogue — configuration knobs and cross-regime sensitivities -/

/-- **ALI, list-size knob (↑).** A regime with a larger list size gives a larger ALI error. -/
theorem DeepAliCfg.aliErr_mono_listSize (c : DeepAliCfg) (R R' : Regime)
    (hle : R.listSize c.densePCS.ρ c.densePCS.traceLen
        ≤ R'.listSize c.densePCS.ρ c.densePCS.traceLen) :
    c.aliErr R ≤ c.aliErr R' := by
  simp only [DeepAliCfg.aliErr]
  refine div_le_div_same ?_ (by exact_mod_cast c.field.card_pos)
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **ALI, constraint-count knob (↑).** More constraints never lower the ALI error. -/
theorem DeepAliCfg.aliErr_mono_numConstraints (c : DeepAliCfg) (R : Regime)
    (hLp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen) {C : ℕ} (h : c.numConstraints ≤ C) :
    c.aliErr R ≤ ({c with numConstraints := C}).aliErr R := by
  dsimp only [DeepAliCfg.aliErr]
  refine div_le_div_same ?_ (by exact_mod_cast c.field.card_pos)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) hLp

/-- **DEEP, list-size knob (↑).** A regime with a larger list size gives a larger DEEP error
(under the multi-point denominator condition and `num ≥ 0`). -/
theorem DeepAliCfg.deepErr_mono_listSize (c : DeepAliCfg) (R R' : Regime)
    (hden : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (hnum : 0 ≤ (c.airMaxDegree : ℚ) * ((c.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
        + ((c.densePCS.traceLen : ℚ) - 1))
    (hle : R.listSize c.densePCS.ρ c.densePCS.traceLen
        ≤ R'.listSize c.densePCS.ρ c.densePCS.traceLen) :
    c.deepErr R ≤ c.deepErr R' := by
  simp only [DeepAliCfg.deepErr]
  refine div_le_div_same (div_le_div_same ?_ hden) (by positivity)
  exact mul_le_mul_of_nonneg_right hle hnum

/-- **DEEP, grind knob (↓).** More DEEP-phase PoW bits never raise the DEEP error. -/
theorem DeepAliCfg.deepErr_antitone_grindDeep (c : DeepAliCfg) (R : Regime)
    (hLp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hden : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (hnum : 0 ≤ (c.airMaxDegree : ℚ) * ((c.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
        + ((c.densePCS.traceLen : ℚ) - 1))
    {g : ℕ} (h : c.grindDeep ≤ g) :
    ({c with grindDeep := g}).deepErr R ≤ c.deepErr R := by
  dsimp only [DeepAliCfg.deepErr]
  refine div_pow_two_antitone (div_nonneg (mul_nonneg hLp hnum) hden.le) h

/-- **DEEP, degree knob (↑).** A larger AIR degree never lowers the DEEP error. -/
theorem DeepAliCfg.deepErr_mono_airMaxDegree (c : DeepAliCfg) (R : Regime)
    (hLp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hden : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (hcoeff : 0 ≤ (c.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
    {deg : ℕ} (h : c.airMaxDegree ≤ deg) :
    c.deepErr R ≤ ({c with airMaxDegree := deg}).deepErr R := by
  dsimp only [DeepAliCfg.deepErr]
  refine div_le_div_same (div_le_div_same (mul_le_mul_of_nonneg_left ?_ hLp) hden) (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hcoeff) le_rfl

/-- **DEEP, max-combo knob (↑).** A larger max-combo never lowers the DEEP error. -/
theorem DeepAliCfg.deepErr_mono_maxCombo (c : DeepAliCfg) (R : Regime)
    (hLp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hden : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    {mc : ℕ} (h : c.maxCombo ≤ mc) :
    c.deepErr R ≤ ({c with maxCombo := mc}).deepErr R := by
  dsimp only [DeepAliCfg.deepErr]
  refine div_le_div_same (div_le_div_same (mul_le_mul_of_nonneg_left ?_ hLp) hden) (by positivity)
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) le_rfl
  have : (c.maxCombo : ℚ) ≤ (mc : ℚ) := by exact_mod_cast h
  linarith

end Soundcalc
