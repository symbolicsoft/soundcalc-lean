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

/-- The powers-batching error is nonnegative (for `b ≥ 1` and a nonnegative dimension) — needed to
apply the grinding antitonicity to the batching/commit cells. The dimension is a rational so that
this also serves `commitErr`, whose dimension is `denseLen / ∏ foldingFactors`. -/
theorem UDR_errPowers_nonneg (F : FieldParams) (ρ : Rate) {d : ℚ} (hd : 0 ≤ d) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ (UDR F).errPowers ρ d b := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * (d / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * (d / r) := mul_nonneg (by linarith) (div_nonneg hd hr0.le)
    linarith
  simp only [UDR]
  exact mul_nonneg (div_nonneg hnum hc.le) hbb

/-- **Multilinear-batching soundness cost.** The multilinear-batching error
`errMultilinear = errLinear·⌈log₂ batch⌉` is monotone in `batchSize` — the SP1 (`multilinBatch`) path's
analogue of `UDR_errPowers_mono_batch`. -/
theorem UDR_errMultilinear_mono_batch (F : FieldParams) (ρ : Rate) (d : ℕ) {b b' : ℕ} (h : b ≤ b') :
    (UDR F).errMultilinear ρ d b ≤ (UDR F).errMultilinear ρ d b' := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) := mul_nonneg (by linarith) (by positivity)
    linarith
  have hbase : (0 : ℚ) ≤ ((1 - r) / 2 * ((d : ℚ) / r) + 1) / (F.card : ℚ) := div_nonneg hnum hc.le
  have hclog : (Nat.clog 2 b : ℚ) ≤ (Nat.clog 2 b' : ℚ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  simp only [UDR]
  exact mul_le_mul_of_nonneg_left hclog hbase

/-- The multilinear-batching error is nonnegative — needed to grind the `multilinBatch` cell. -/
theorem UDR_errMultilinear_nonneg (F : FieldParams) (ρ : Rate) (d : ℕ) (b : ℕ) :
    0 ≤ (UDR F).errMultilinear ρ d b := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) := mul_nonneg (by linarith) (by positivity)
    linarith
  simp only [UDR]
  exact mul_nonneg (div_nonneg hnum hc.le) (by positivity)

/-! ## The JBR (Johnson-bound) regime

`JBR.errLinear = jbrErrLinear`, whose numerator `2·ms⁵ + 3·ms·(θρ)` is nonnegative because the
`2·ms⁵` term (with `ms = jbrM + ½ ≥ 3.5`, since `jbrM ≥ 3`) dominates. That nonnegativity is the crux
that lets the batching/commit monotonicities carry over from `UDR` to `JBR` (both have
`errPowers = errLinear·(b−1)`, `errMultilinear = errLinear·⌈log₂ b⌉`). -/

/-- Domination: `2·ms⁵` beats `3·ms·t` once `ms ≥ 7/2` and `t ≥ −1`. -/
private theorem jbr_dom {ms t : ℚ} (hms : 7 / 2 ≤ ms) (ht : -1 ≤ t) :
    0 ≤ 2 * ms ^ 5 + 3 * ms * t := by
  have h0 : (0 : ℚ) ≤ ms := by linarith
  have h2 : (12 : ℚ) ≤ ms ^ 2 := by nlinarith [sq_nonneg (ms - 7 / 2)]
  have h4 : (144 : ℚ) ≤ ms ^ 4 := by nlinarith [sq_nonneg (ms ^ 2 - 12), h2]
  have key : 2 * ms ^ 5 + 3 * ms * t = ms * (2 * ms ^ 4 + 3 * t) := by ring
  rw [key]
  exact mul_nonneg h0 (by linarith)

/-- **The JBR linear error is nonnegative** (under the standard config conditions: `0 < ρ < 1`,
`η ≤ 1`, and `0 < sqrtLB ρ g ≤ 1`). The crux for the JBR batching/commit monotonicities. -/
theorem jbrErrLinear_nonneg (F : FieldParams) {η : ℚ} {g : ℕ} {ρ : ℚ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : η ≤ 1) (hsr0 : 0 < sqrtLB ρ g) (hsr1 : sqrtLB ρ g ≤ 1)
    {d : ℚ} (hd : 0 ≤ d) :
    0 ≤ jbrErrLinear F η g ρ d := by
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hm3 : 3 ≤ jbrM ρ η g := le_max_right _ 3
  have hms : (7 : ℚ) / 2 ≤ (jbrM ρ η g : ℚ) + 1 / 2 := by
    have : (3 : ℚ) ≤ (jbrM ρ η g : ℚ) := by exact_mod_cast hm3
    linarith
  have hθρ : (-1 : ℚ) ≤ ((1 - η) - sqrtLB ρ g) * ρ := by
    have hpos : (0 : ℚ) ≤ ((1 - η) - sqrtLB ρ g + 1) * ρ :=
      mul_nonneg (by linarith) hρ0.le
    nlinarith [hpos, hρ1]
  have hdom := jbr_dom hms hθρ
  have hn : (0 : ℚ) ≤ d / ρ := div_nonneg hd hρ0.le
  have hden : (0 : ℚ) < 3 * ρ * sqrtLB ρ g :=
    mul_pos (mul_pos (by norm_num) hρ0) hsr0
  simp only [jbrErrLinear]
  refine div_nonneg (add_nonneg ?_ ?_) hc.le
  · exact div_nonneg (mul_nonneg hdom hn) hden.le
  · exact div_nonneg (by linarith) hsr0.le

/-- The JBR regime's linear error is nonnegative (packaging `jbrErrLinear_nonneg` at the `JBR`
regime). The `sqrtLB`/`etaLB` side conditions hold for every real config. -/
theorem JBR_errLinear_nonneg (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) :
    0 ≤ (JBR F g gap).errLinear ρ d := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR]
  exact jbrErrLinear_nonneg F hr0 hr1 hη hsr0 hsr1 hd

/-- **Batching cost at JBR.** `JBR.errPowers = jbrErrLinear·(b−1)` is monotone in `batchSize`. -/
theorem JBR_errPowers_mono_batch (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) {b b' : ℕ} (h : b ≤ b') :
    (JBR F g gap).errPowers ρ d b ≤ (JBR F g gap).errPowers ρ d b' := by
  have hlin := JBR_errLinear_nonneg F g gap ρ hd hsr0 hsr1 hη
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR] at hlin ⊢
  have hbb : ((b : ℚ) - 1) ≤ ((b' : ℚ) - 1) := by
    have : (b : ℚ) ≤ (b' : ℚ) := by exact_mod_cast h
    linarith
  exact mul_le_mul_of_nonneg_left hbb hlin

/-- **Multilinear batching cost at JBR** (SP1's mode). `JBR.errMultilinear = jbrErrLinear·⌈log₂ b⌉`. -/
theorem JBR_errMultilinear_mono_batch (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) {b b' : ℕ} (h : b ≤ b') :
    (JBR F g gap).errMultilinear ρ d b ≤ (JBR F g gap).errMultilinear ρ d b' := by
  have hlin := JBR_errLinear_nonneg F g gap ρ hd hsr0 hsr1 hη
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR] at hlin ⊢
  have hclog : (Nat.clog 2 b : ℚ) ≤ (Nat.clog 2 b' : ℚ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  exact mul_le_mul_of_nonneg_left hclog hlin

/-- The JBR powers error is nonnegative (`b ≥ 1`) — for the JBR grind knobs. -/
theorem JBR_errPowers_nonneg (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ (JBR F g gap).errPowers ρ d b := by
  have hlin := JBR_errLinear_nonneg F g gap ρ hd hsr0 hsr1 hη
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR] at hlin ⊢
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  exact mul_nonneg hlin hbb

/-- The JBR multilinear error is nonnegative — for the JBR grind knob on SP1's mode. -/
theorem JBR_errMultilinear_nonneg (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) (b : ℕ) :
    0 ≤ (JBR F g gap).errMultilinear ρ d b := by
  have hlin := JBR_errLinear_nonneg F g gap ρ hd hsr0 hsr1 hη
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR] at hlin ⊢
  exact mul_nonneg hlin (by positivity)

/-- **The `H` cell at JBR.** `jbrErrLinear` is monotone in the dimension `d` (it enters linearly via
`n = d/ρ`, and the coefficient is nonnegative). Unlike `ρ`/`|F|`, `d` does not thread through the gap
`etaLB`, so this is clean. -/
theorem JBR_errLinear_mono_dim (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d d' : ℚ}
    (hdd : d ≤ d') (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) :
    (JBR F g gap).errLinear ρ d ≤ (JBR F g gap).errLinear ρ d' := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hm3 : 3 ≤ jbrM r (etaLB r g F.card gap) g := le_max_right _ 3
  have hms : (7 : ℚ) / 2 ≤ (jbrM r (etaLB r g F.card gap) g : ℚ) + 1 / 2 := by
    have : (3 : ℚ) ≤ (jbrM r (etaLB r g F.card gap) g : ℚ) := by exact_mod_cast hm3
    linarith
  have hθρ : (-1 : ℚ) ≤ ((1 - etaLB r g F.card gap) - sqrtLB r g) * r := by
    have hpos : (0 : ℚ) ≤ ((1 - etaLB r g F.card gap) - sqrtLB r g + 1) * r :=
      mul_nonneg (by linarith) hr0.le
    nlinarith [hpos, hr1]
  have hdom := jbr_dom hms hθρ
  have hden : (0 : ℚ) < 3 * r * sqrtLB r g := mul_pos (mul_pos (by norm_num) hr0) hsr0
  simp only [JBR, jbrErrLinear]
  gcongr

/-- Powers error at JBR is monotone in the dimension (`H ↑` for the commit/batching cell). -/
theorem JBR_errPowers_mono_dim (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d d' : ℚ}
    (hdd : d ≤ d') (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) {b : ℕ} (hb : 1 ≤ b) :
    (JBR F g gap).errPowers ρ d b ≤ (JBR F g gap).errPowers ρ d' b := by
  have hlin := JBR_errLinear_mono_dim F g gap ρ hdd hsr0 hsr1 hη
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR] at hlin ⊢
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  exact mul_le_mul_of_nonneg_right hlin hbb

/-- **The `|F|` cell at JBR.** `jbrErrLinear` is antitone in `|F|` (it divides by `|F|`) **provided the
gap agrees** — `etaLB` depends on `card` only through the `card > 2^150` threshold, so two fields on the
same side of it give the same `η`, making the numerator `|F|`-independent. -/
theorem JBR_errLinear_antitone_card {F F' : FieldParams} (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hηeq : etaLB (ρ : ℚ) g F'.card gap = etaLB (ρ : ℚ) g F.card gap)
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) (hcard : F.card ≤ F'.card) :
    (JBR F' g gap).errLinear ρ d ≤ (JBR F g gap).errLinear ρ d := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hcF : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hcQ : (F.card : ℚ) ≤ (F'.card : ℚ) := by exact_mod_cast hcard
  have hm3 : 3 ≤ jbrM r (etaLB r g F.card gap) g := le_max_right _ 3
  have hms : (7 : ℚ) / 2 ≤ (jbrM r (etaLB r g F.card gap) g : ℚ) + 1 / 2 := by
    have : (3 : ℚ) ≤ (jbrM r (etaLB r g F.card gap) g : ℚ) := by exact_mod_cast hm3
    linarith
  have hθρ : (-1 : ℚ) ≤ ((1 - etaLB r g F.card gap) - sqrtLB r g) * r := by
    have hpos : (0 : ℚ) ≤ ((1 - etaLB r g F.card gap) - sqrtLB r g + 1) * r :=
      mul_nonneg (by linarith) hr0.le
    nlinarith [hpos, hr1]
  have hdom := jbr_dom hms hθρ
  have hn : (0 : ℚ) ≤ d / r := div_nonneg hd hr0.le
  have hden : (0 : ℚ) < 3 * r * sqrtLB r g := mul_pos (mul_pos (by norm_num) hr0) hsr0
  simp only [JBR, jbrErrLinear, hηeq]
  refine div_le_div_denom (add_nonneg ?_ ?_) hcF hcQ
  · exact div_nonneg (mul_nonneg hdom hn) hden.le
  · exact div_nonneg (by linarith) hsr0.le

/-- Powers error at JBR is antitone in `|F|` (same gap-agreement condition). -/
theorem JBR_errPowers_antitone_card {F F' : FieldParams} (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hηeq : etaLB (ρ : ℚ) g F'.card gap = etaLB (ρ : ℚ) g F.card gap)
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) (hcard : F.card ≤ F'.card) {b : ℕ} (hb : 1 ≤ b) :
    (JBR F' g gap).errPowers ρ d b ≤ (JBR F g gap).errPowers ρ d b := by
  have hlin := JBR_errLinear_antitone_card g gap ρ hηeq hd hsr0 hsr1 hη hcard
  obtain ⟨r, hr0, hr1⟩ := ρ
  simp only [JBR] at hlin ⊢
  have hbb : (0 : ℚ) ≤ (b : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  exact mul_le_mul_of_nonneg_right hlin hbb

end Soundcalc
