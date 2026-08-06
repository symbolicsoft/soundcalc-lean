import Soundcalc.Monotonicity.Basic
import Soundcalc.Regime

/-!
# Monotonicity — Regime (Johnson vs. unique decoding, and the field ceiling on `errLinear`)

* `johnson_beats_unique` — the Johnson decoding radius `1 − √ρ` always beats the unique-decoding
  radius `(1-ρ)/2` (a corollary of `two_sqrt_le`). This is *why* JBR helps the query cell.
* `one_div_card_le_errLinear` / `secBits_errLinear_le_field` — the linear (Schwartz–Zippel) error is
  `≥ 1/|F|`, so the field ceiling actually bites on the algebraic cells.
* `UDR_errLinear_mono_dim` — the linear error is monotone in the instance dimension.

These are **foundations** (regime/field-level mechanisms), not config-field catalogue entries; the
FRI/WHIR catalogues lift `UDR_errLinear_mono_dim` (via `errPowers`) and the field ceiling.
-/

namespace Soundcalc

/-- The Johnson-bound decoding radius `1 - √ρ` is always at least the unique-decoding radius
`(1-ρ)/2`, slack exactly `(1-√ρ)²/2`. A corollary of `two_sqrt_le`. -/
theorem johnson_beats_unique {ρ : ℝ} (h0 : 0 ≤ ρ) :
    (1 - ρ) / 2 ≤ 1 - Real.sqrt ρ := by
  have := two_sqrt_le h0; linarith

/-- **Connector.** The linear (Schwartz–Zippel) soundness error is `≥ 1/|F|` — its numerator
`θ·(d/ρ) + 1 ≥ 1`. So the field ceiling actually bites on the *algebraic* cells (unlike the query
cell `(1-θ)^t/2^g`, which has no `|F|` and is bounded by *repetition*, not the field). -/
theorem one_div_card_le_errLinear (F : FieldParams) (ρ : Rate) (d : ℕ) :
    1 / (F.card : ℚ) ≤ (UDR F).errLinear ρ d := by
  obtain ⟨r, hr0, _⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  simp only [UDR]
  have hnum : (1 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have hpos : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  gcongr

/-- The field ceiling, **applied**: the linear soundness cell can never report more bits than the
field baseline `secBits (1/|F|) = ⌊log₂|F|⌋`. -/
theorem secBits_errLinear_le_field (F : FieldParams) (ρ : Rate) (d : ℕ) :
    secBits ((UDR F).errLinear ρ d) ≤ secBits (1 / (F.card : ℚ)) :=
  secBits_le_field F.card_pos (one_div_card_le_errLinear F ρ d)

/-- **Smaller instance ⇒ more sound.** The linear (Schwartz–Zippel) error is monotone in the
dimension `d`. This is the mechanism behind "later FRI rounds are more secure": each fold shrinks
the dimension. -/
theorem UDR_errLinear_mono_dim (F : FieldParams) (ρ : Rate) {d d' : ℕ} (h : d ≤ d') :
    (UDR F).errLinear ρ d ≤ (UDR F).errLinear ρ d' := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hA : (0 : ℚ) ≤ (1 - r) / 2 := by linarith
  have hdd : (d : ℚ) ≤ (d' : ℚ) := by exact_mod_cast h
  simp only [UDR]
  gcongr

end Soundcalc
