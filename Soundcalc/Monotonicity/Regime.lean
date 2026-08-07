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

/-! # Foundations (regime / field-level mechanisms)

This whole file is foundations — regime-level facts the FRI/WHIR catalogues lift. There are no
config-field catalogue entries here (a `Regime` is not a config). -/

/-! ## Johnson vs. unique decoding -/

/-- The Johnson-bound decoding radius `1 - √ρ` is always at least the unique-decoding radius
`(1-ρ)/2`, slack exactly `(1-√ρ)²/2`. A corollary of `two_sqrt_le`. -/
theorem johnson_beats_unique {ρ : ℝ} (h0 : 0 ≤ ρ) :
    (1 - ρ) / 2 ≤ 1 - Real.sqrt ρ := by
  have := two_sqrt_le h0; linarith

/-! ## The field ceiling on the linear error -/

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

/-! ## `errLinear` / `errPowers` monotonicities (lifted by the FRI/WHIR catalogues) -/

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

/-- **Larger field ⇒ smaller error.** The linear error is antitone in `|F|` (it divides by `|F|`,
numerator field-independent). Backs the `|F| ↓` column. -/
theorem UDR_errLinear_antitone_card {F F' : FieldParams} (hc : F.card ≤ F'.card) (ρ : Rate) (d : ℕ) :
    (UDR F').errLinear ρ d ≤ (UDR F).errLinear ρ d := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hF : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hcQ : (F.card : ℚ) ≤ (F'.card : ℚ) := by exact_mod_cast hc
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) := mul_nonneg (by linarith) (by positivity)
    linarith
  simp only [UDR]
  gcongr

/-- **Higher rate ⇒ smaller error.** The linear error is antitone in the rate `ρ`: the algebraic
term `(1−ρ)/2 · (d/ρ) = d(1−ρ)/(2ρ)` falls as `ρ` grows (`1/ρ` shrinks). Backs the `ρ ↓` column. -/
theorem UDR_errLinear_antitone_rho (F : FieldParams) {ρ ρ' : Rate}
    (h : (ρ : ℚ) ≤ (ρ' : ℚ)) (d : ℕ) :
    (UDR F).errLinear ρ' d ≤ (UDR F).errLinear ρ d := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  obtain ⟨r', hr0', hr1'⟩ := ρ'
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have e : ∀ x : ℚ, 0 < x → (1 - x) / 2 * ((d : ℚ) / x) = (d : ℚ) / 2 * (1 / x - 1) := by
    intro x hx; field_simp
  have hrec : 1 / r' ≤ 1 / r := one_div_le_one_div_of_le hr0 h
  have hd : (0 : ℚ) ≤ (d : ℚ) / 2 := by positivity
  have hkey : (1 - r') / 2 * ((d : ℚ) / r') ≤ (1 - r) / 2 * ((d : ℚ) / r) := by
    rw [e r' hr0', e r hr0]
    exact mul_le_mul_of_nonneg_left (by linarith) hd
  have hnum : (1 - r') / 2 * ((d : ℚ) / r') + 1 ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by linarith
  simp only [UDR]
  rw [div_le_div_iff₀ hc hc]
  exact mul_le_mul_of_nonneg_right hnum hc.le

/-- Powers-batching error is antitone in `|F|` (corollary of `UDR_errLinear_antitone_card`, `b ≥ 1`). -/
theorem UDR_errPowers_antitone_card {F F' : FieldParams} (hc : F.card ≤ F'.card) (ρ : Rate) (d : ℕ)
    {b : ℕ} (hb : 1 ≤ b) :
    (UDR F').errPowers ρ d b ≤ (UDR F).errPowers ρ d b := by
  have hlin := UDR_errLinear_antitone_card hc ρ d
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  simp only [UDR] at hlin ⊢
  exact mul_le_mul_of_nonneg_right hlin hbb

/-- Powers-batching error is antitone in the rate `ρ` (corollary of `UDR_errLinear_antitone_rho`). -/
theorem UDR_errPowers_antitone_rho (F : FieldParams) {ρ ρ' : Rate} (h : (ρ : ℚ) ≤ (ρ' : ℚ)) (d : ℕ)
    {b : ℕ} (hb : 1 ≤ b) :
    (UDR F).errPowers ρ' d b ≤ (UDR F).errPowers ρ d b := by
  have hlin := UDR_errLinear_antitone_rho F h d
  obtain ⟨r, hr0, hr1⟩ := ρ
  obtain ⟨r', hr0', hr1'⟩ := ρ'
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  simp only [UDR] at hlin ⊢
  exact mul_le_mul_of_nonneg_right hlin hbb

/-- Powers-batching error is monotone in the dimension `d` (corollary of `UDR_errLinear_mono_dim`).
Backs the `H ↑` column for the commit/batching cell. -/
theorem UDR_errPowers_mono_dim (F : FieldParams) (ρ : Rate) {d d' : ℕ} (h : d ≤ d')
    {b : ℕ} (hb : 1 ≤ b) :
    (UDR F).errPowers ρ d b ≤ (UDR F).errPowers ρ d' b := by
  have hlin := UDR_errLinear_mono_dim F ρ h
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  simp only [UDR] at hlin ⊢
  exact mul_le_mul_of_nonneg_right hlin hbb

/-- **Batching soundness cost.** The powers-batching error `errPowers = errLinear·(batch − 1)` is
monotone in `batchSize`: batching more polynomials weakens the batching cell. -/
theorem UDR_errPowers_mono_batch (F : FieldParams) (ρ : Rate) (d : ℕ) {b b' : ℕ} (h : b ≤ b') :
    (UDR F).errPowers ρ d b ≤ (UDR F).errPowers ρ d b' := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  simp only [UDR]
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) := mul_nonneg (by linarith) (by positivity)
    linarith
  have hbase : (0 : ℚ) ≤ ((1 - r) / 2 * ((d : ℚ) / r) + 1) / (F.card : ℚ) := div_nonneg hnum hc.le
  have hbb : ((b : ℚ) - 1) ≤ ((b' : ℚ) - 1) := by
    have : (b : ℚ) ≤ (b' : ℚ) := by exact_mod_cast h
    linarith
  gcongr

/-- The powers-batching error is nonnegative (for `b ≥ 1`) — needed to apply the grinding
antitonicity to the batching cell. -/
theorem UDR_errPowers_nonneg (F : FieldParams) (ρ : Rate) (d : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ (UDR F).errPowers ρ d b := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) := mul_nonneg (by linarith) (by positivity)
    linarith
  simp only [UDR]
  exact mul_nonneg (div_nonneg hnum hc.le) hbb

end Soundcalc
