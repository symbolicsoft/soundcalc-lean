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

/-! # Catalogue — configuration knobs and cross-regime sensitivities

The division-monotonicity finishing steps (`div_le_div_same`, `div_le_div_denom`,
`div_pow_two_antitone`) are shared from `Monotonicity.Basic`. -/

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

/-! ## Pinned columns (`|F|`, `ρ`, `H`) via two coherent configs

`|F|`/`ρ`/`H` cannot be moved by a record update (DeepAli's field-coherence invariants, and the
`FRIConfig.h_earlyStop` behind `densePCS.ρ`/`traceLen`). We back their directions by comparing two
configs that **agree on the other projections** — exactly how a "same circuit, bigger field / slower
rate / longer trace" instance relates to the original. -/

/-- **ALI, `|F|` column (↓).** A larger field (other projections equal) gives a smaller ALI error. -/
theorem DeepAliCfg.aliErr_antitone_card (c c' : DeepAliCfg) (R : Regime)
    (hρ : c'.densePCS.ρ = c.densePCS.ρ) (htl : c'.densePCS.traceLen = c.densePCS.traceLen)
    (hC : c'.numConstraints = c.numConstraints)
    (hlp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hcard : c.field.card ≤ c'.field.card) :
    c'.aliErr R ≤ c.aliErr R := by
  simp only [DeepAliCfg.aliErr, hρ, htl, hC]
  exact div_le_div_denom (mul_nonneg hlp (by positivity))
    (by exact_mod_cast c.field.card_pos) (by exact_mod_cast hcard)

/-- **DEEP, `|F|` column (↓).** A larger field (other projections equal, `|F|−H−D > 0`) gives a
smaller DEEP error. -/
theorem DeepAliCfg.deepErr_antitone_card (c c' : DeepAliCfg) (R : Regime)
    (hρ : c'.densePCS.ρ = c.densePCS.ρ) (htl : c'.densePCS.traceLen = c.densePCS.traceLen)
    (hdeg : c'.airMaxDegree = c.airMaxDegree) (hmc : c'.maxCombo = c.maxCombo)
    (hg : c'.grindDeep = c.grindDeep)
    (hlp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hnum : 0 ≤ (c.airMaxDegree : ℚ) * ((c.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
        + ((c.densePCS.traceLen : ℚ) - 1))
    (hden : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (hcard : c.field.card ≤ c'.field.card) :
    c'.deepErr R ≤ c.deepErr R := by
  simp only [DeepAliCfg.deepErr, hρ, htl, hdeg, hmc, hg]
  refine div_le_div_same (div_le_div_denom (mul_nonneg hlp hnum) hden ?_) (by positivity)
  have : (c.field.card : ℚ) ≤ (c'.field.card : ℚ) := by exact_mod_cast hcard
  linarith

/-- **DEEP, `ρ` column (↓).** A higher rate (other projections + list size equal) gives a smaller
DEEP error, via the `H/ρ` term in the `|F|−H−D` denominator. -/
theorem DeepAliCfg.deepErr_antitone_rho (c c' : DeepAliCfg) (R : Regime)
    (htl : c'.densePCS.traceLen = c.densePCS.traceLen) (hfield : c'.field = c.field)
    (hdeg : c'.airMaxDegree = c.airMaxDegree) (hmc : c'.maxCombo = c.maxCombo)
    (hg : c'.grindDeep = c.grindDeep)
    (hlpeq : R.listSize c'.densePCS.ρ c.densePCS.traceLen
        = R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hlp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hnum : 0 ≤ (c.airMaxDegree : ℚ) * ((c.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
        + ((c.densePCS.traceLen : ℚ) - 1))
    (hρpos : 0 < (c.densePCS.ρ : ℚ))
    (hden : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (hρ : (c.densePCS.ρ : ℚ) ≤ (c'.densePCS.ρ : ℚ)) :
    c'.deepErr R ≤ c.deepErr R := by
  simp only [DeepAliCfg.deepErr, htl, hfield, hdeg, hmc, hg, hlpeq]
  refine div_le_div_same (div_le_div_denom (mul_nonneg hlp hnum) hden ?_) (by positivity)
  have hDmono : (c.densePCS.traceLen : ℚ) / (c'.densePCS.ρ : ℚ)
      ≤ (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ) :=
    div_le_div_denom (by positivity) hρpos hρ
  exact sub_le_sub_left hDmono _

/-- **DEEP, `H` column (↑).** A longer trace (other projections + list size equal) gives a larger
DEEP error — it grows the numerator and shrinks the `|F|−H−D` denominator. -/
theorem DeepAliCfg.deepErr_mono_traceLen (c c' : DeepAliCfg) (R : Regime)
    (hfield : c'.field = c.field) (hρ : c'.densePCS.ρ = c.densePCS.ρ)
    (hdeg : c'.airMaxDegree = c.airMaxDegree) (hmc : c'.maxCombo = c.maxCombo)
    (hg : c'.grindDeep = c.grindDeep)
    (hlpeq : R.listSize c.densePCS.ρ c'.densePCS.traceLen
        = R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hlp : 0 ≤ R.listSize c.densePCS.ρ c.densePCS.traceLen)
    (hρpos : 0 < (c.densePCS.ρ : ℚ))
    (hnum' : 0 ≤ (c.airMaxDegree : ℚ) * ((c'.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
        + ((c'.densePCS.traceLen : ℚ) - 1))
    (hdenH : 0 < (c.field.card : ℚ) - (c.densePCS.traceLen : ℚ)
        - (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (hdenH' : 0 < (c.field.card : ℚ) - (c'.densePCS.traceLen : ℚ)
        - (c'.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ))
    (htl : c.densePCS.traceLen ≤ c'.densePCS.traceLen) :
    c.deepErr R ≤ c'.deepErr R := by
  simp only [DeepAliCfg.deepErr, hfield, hρ, hdeg, hmc, hg, hlpeq]
  refine div_le_div_same ?_ (by positivity)
  have htlQ : (c.densePCS.traceLen : ℚ) ≤ (c'.densePCS.traceLen : ℚ) := by exact_mod_cast htl
  have hd0 : (0 : ℚ) ≤ (c.airMaxDegree : ℚ) := by positivity
  have hnumMono :
      (c.airMaxDegree : ℚ) * ((c.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
          + ((c.densePCS.traceLen : ℚ) - 1)
        ≤ (c.airMaxDegree : ℚ) * ((c'.densePCS.traceLen : ℚ) + (c.maxCombo : ℚ) - 1)
          + ((c'.densePCS.traceLen : ℚ) - 1) := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.2 htlQ), htlQ]
  have hDmono : (c.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ)
      ≤ (c'.densePCS.traceLen : ℚ) / (c.densePCS.ρ : ℚ) := div_le_div_same htlQ hρpos
  refine le_trans (div_le_div_same (mul_le_mul_of_nonneg_left hnumMono hlp) hdenH) ?_
  refine div_le_div_denom (mul_nonneg hlp hnum') hdenH' ?_
  rw [sub_sub, sub_sub]
  exact sub_le_sub_left (add_le_add htlQ hDmono) _

end Soundcalc
