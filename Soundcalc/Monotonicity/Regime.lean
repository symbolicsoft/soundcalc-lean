import Soundcalc.Monotonicity.Basic
import Soundcalc.Regime

/-!
# Monotonicity — Regime (Johnson vs. unique decoding, and the regime-independent cell mechanisms)

* `johnson_beats_unique` — the Johnson decoding radius `1 − √ρ` always beats the unique-decoding
  radius `(1-ρ)/2` (a corollary of `two_sqrt_le`). This is *why* JBR helps the query cell.
* `Regime.Standard` — **the regime-independence device.** A `Prop`-bundle saying a regime has the
  standard algebraic shape: `errPowers = errLinear·(b−1)`, `errMultilinear = errLinear·⌈log₂ b⌉`,
  the linear error is `≥ 1/|F|` (so the field ceiling bites), and it is monotone in the instance
  dimension. Every algebraic *cell* lemma below — and every algebraic catalogue theorem in
  `Monotonicity.FRI` / `.WHIR` — is stated for an **arbitrary** regime satisfying it.
* `UDR_standard` / `JBR_standard` — the only two regime-specific proofs in the whole catalogue.
  Everything else is regime-polymorphic, so there are no `UDR_`/`JBR_` cell duplicates to keep in
  sync (the sole exception is the `|F|` knob, which *is* a change of regime — see below).

These are **foundations** (regime/field-level mechanisms), not config-field catalogue entries.
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

/-! ## The standard regime shape — what makes the catalogue regime-independent

Both regimes in the model (`UDR`, `JBR`) build *every* algebraic error out of one scalar, the linear
(Schwartz–Zippel / MCA) error `errLinear ρ d`:

* `errPowers ρ d b = errLinear ρ d · (b − 1)` (union bound over `b − 1` power checks),
* `errMultilinear ρ d b = errLinear ρ d · ⌈log₂ b⌉` (one term per sumcheck round),

and that scalar is `≥ 1/|F|` (the field ceiling bites) and monotone in the dimension `d` (smaller
instance ⇒ more sound). `Regime.Standard` records exactly those four facts, so a cell lemma proved
from it holds at **any** regime — no per-regime restatement. -/

/-- **The standard regime shape.** `R.Standard F ρ` says the regime `R`, over the field `F` at rate
`ρ`, has the algebraic structure every regime in this model has. It is the hypothesis that makes the
algebraic catalogue regime-independent: `UDR_standard` and `JBR_standard` discharge it. -/
structure Regime.Standard (R : Regime) (F : FieldParams) (ρ : Rate) : Prop where
  /-- Powers batching is the linear error scaled by `b − 1` (union bound). -/
  errPowers_eq : ∀ (d : ℚ) (b : ℕ), R.errPowers ρ d b = R.errLinear ρ d * ((b : ℚ) - 1)
  /-- Multilinear batching is the linear error scaled by `⌈log₂ b⌉` (one term per sumcheck round). -/
  errMultilinear_eq :
    ∀ (d : ℚ) (b : ℕ), R.errMultilinear ρ d b = R.errLinear ρ d * (Nat.clog 2 b : ℚ)
  /-- The field ceiling bites: the linear error is at least `1/|F|`. -/
  one_div_card_le : ∀ d : ℚ, 0 ≤ d → 1 / (F.card : ℚ) ≤ R.errLinear ρ d
  /-- Smaller instance ⇒ more sound: the linear error is monotone in the dimension. -/
  errLinear_mono_dim : ∀ d d' : ℚ, d ≤ d' → R.errLinear ρ d ≤ R.errLinear ρ d'

namespace Regime.Standard

variable {R : Regime} {F : FieldParams} {ρ : Rate}

/-- The linear error is nonnegative (it is `≥ 1/|F| > 0`). -/
theorem errLinear_nonneg (hR : R.Standard F ρ) {d : ℚ} (hd : 0 ≤ d) : 0 ≤ R.errLinear ρ d := by
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have h := hR.one_div_card_le d hd
  have hpos : (0 : ℚ) < 1 / (F.card : ℚ) := by positivity
  linarith

/-- The powers-batching error is nonnegative (`b ≥ 1`) — the input to every grind knob on a
`powerBatch`-path cell. -/
theorem errPowers_nonneg (hR : R.Standard F ρ) {d : ℚ} (hd : 0 ≤ d) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ R.errPowers ρ d b := by
  rw [hR.errPowers_eq]
  have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  exact mul_nonneg (hR.errLinear_nonneg hd) (by linarith)

/-- The multilinear-batching error is nonnegative — the grind-knob input on the multilinear path. -/
theorem errMultilinear_nonneg (hR : R.Standard F ρ) {d : ℚ} (hd : 0 ≤ d) (b : ℕ) :
    0 ≤ R.errMultilinear ρ d b := by
  rw [hR.errMultilinear_eq]
  exact mul_nonneg (hR.errLinear_nonneg hd) (by positivity)

/-- **Batching soundness cost, any regime.** `errPowers = errLinear·(b − 1)` is monotone in
`batchSize`: batching more polynomials weakens the batching cell. -/
theorem errPowers_mono_batch (hR : R.Standard F ρ) {d : ℚ} (hd : 0 ≤ d) {b b' : ℕ} (h : b ≤ b') :
    R.errPowers ρ d b ≤ R.errPowers ρ d b' := by
  rw [hR.errPowers_eq, hR.errPowers_eq]
  have hbb : (b : ℚ) ≤ (b' : ℚ) := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_left (by linarith) (hR.errLinear_nonneg hd)

/-- **Multilinear batching cost, any regime** (SP1's mode).
`errMultilinear = errLinear·⌈log₂ b⌉` is monotone in `batchSize`. -/
theorem errMultilinear_mono_batch (hR : R.Standard F ρ) {d : ℚ} (hd : 0 ≤ d) {b b' : ℕ}
    (h : b ≤ b') :
    R.errMultilinear ρ d b ≤ R.errMultilinear ρ d b' := by
  rw [hR.errMultilinear_eq, hR.errMultilinear_eq]
  have hclog : (Nat.clog 2 b : ℚ) ≤ (Nat.clog 2 b' : ℚ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  exact mul_le_mul_of_nonneg_left hclog (hR.errLinear_nonneg hd)

/-- **The field ceiling, applied — at any regime.** An algebraic cell can never report more bits
than the field baseline `secBits (1/|F|) = ⌊log₂|F|⌋`. (Unlike the query cell `(1−θ)^t/2^g`, which
carries no `|F|` and is bounded by *repetition*, not the field.) -/
theorem secBits_errLinear_le_field (hR : R.Standard F ρ) {d : ℚ} (hd : 0 ≤ d) :
    secBits (R.errLinear ρ d) ≤ secBits (1 / (F.card : ℚ)) :=
  secBits_le_field F.card_pos (hR.one_div_card_le d hd)

end Regime.Standard

/-! ## Batching errors are monotone in the underlying linear error

The one lemma behind both the `H` column (same regime, bigger dimension) and the `|F|` column
(bigger field, hence a *different* regime with a smaller linear error): whatever moves `errLinear`
moves `errPowers`/`errMultilinear` the same way. Stated across two regimes so the `|F|` cell — which
necessarily changes `UDR F` into `UDR F'` — is covered by the same theorem. -/

/-- Powers batching is monotone in the linear error, across regimes. -/
theorem errPowers_le_of_errLinear_le {R R' : Regime} {F F' : FieldParams} {ρ : Rate} {d d' : ℚ}
    (hR : R.Standard F ρ) (hR' : R'.Standard F' ρ)
    (hlin : R.errLinear ρ d ≤ R'.errLinear ρ d') {b : ℕ} (hb : 1 ≤ b) :
    R.errPowers ρ d b ≤ R'.errPowers ρ d' b := by
  rw [hR.errPowers_eq, hR'.errPowers_eq]
  have h1b : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  exact mul_le_mul_of_nonneg_right hlin (by linarith)

/-- Multilinear batching is monotone in the linear error, across regimes. -/
theorem errMultilinear_le_of_errLinear_le {R R' : Regime} {F F' : FieldParams} {ρ : Rate} {d d' : ℚ}
    (hR : R.Standard F ρ) (hR' : R'.Standard F' ρ)
    (hlin : R.errLinear ρ d ≤ R'.errLinear ρ d') (b : ℕ) :
    R.errMultilinear ρ d b ≤ R'.errMultilinear ρ d' b := by
  rw [hR.errMultilinear_eq, hR'.errMultilinear_eq]
  exact mul_le_mul_of_nonneg_right hlin (by positivity)

/-- **The `H` column, any regime.** Powers batching is monotone in the dimension — the mechanism
behind "later FRI rounds are more secure": each fold shrinks the dimension. -/
theorem errPowers_mono_dim {R : Regime} {F : FieldParams} {ρ : Rate} (hR : R.Standard F ρ)
    {d d' : ℚ} (hdd : d ≤ d') {b : ℕ} (hb : 1 ≤ b) :
    R.errPowers ρ d b ≤ R.errPowers ρ d' b :=
  errPowers_le_of_errLinear_le hR hR (hR.errLinear_mono_dim d d' hdd) hb

/-- **The `H` column on the multilinear path, any regime.** -/
theorem errMultilinear_mono_dim {R : Regime} {F : FieldParams} {ρ : Rate} (hR : R.Standard F ρ)
    {d d' : ℚ} (hdd : d ≤ d') (b : ℕ) :
    R.errMultilinear ρ d b ≤ R.errMultilinear ρ d' b :=
  errMultilinear_le_of_errLinear_le hR hR (hR.errLinear_mono_dim d d' hdd) b

/-! ## Instance 1: the Unique Decoding Regime -/

/-- **UDR is standard.** The unique-decoding regime has the standard algebraic shape at every field
and rate — one of the two regime-specific proofs in the catalogue. -/
theorem UDR_standard (F : FieldParams) (ρ : Rate) : (UDR F).Standard F ρ := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  refine ⟨fun d b => rfl, fun d b => rfl, ?_, ?_⟩
  · intro d hd
    simp only [UDR]
    have hnum : (1 : ℚ) ≤ (1 - r) / 2 * (d / r) + 1 := by
      have : (0 : ℚ) ≤ (1 - r) / 2 * (d / r) :=
        mul_nonneg (by linarith) (div_nonneg hd hr0.le)
      linarith
    gcongr
  · intro d d' hdd
    simp only [UDR]
    have hA : (0 : ℚ) ≤ (1 - r) / 2 := by linarith
    gcongr

/-- **Larger field ⇒ smaller error (UDR).** The linear error is antitone in `|F|` (it divides by
`|F|`, numerator field-independent). This is the regime-specific input to the `|F|` column. -/
theorem UDR_errLinear_antitone_card {F F' : FieldParams} (hc : F.card ≤ F'.card) (ρ : Rate)
    {d : ℚ} (hd : 0 ≤ d) :
    (UDR F').errLinear ρ d ≤ (UDR F).errLinear ρ d := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hF : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hcQ : (F.card : ℚ) ≤ (F'.card : ℚ) := by exact_mod_cast hc
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * (d / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * (d / r) := mul_nonneg (by linarith) (div_nonneg hd hr0.le)
    linarith
  simp only [UDR]
  gcongr

/-- The `|F|` column on the powers path, at UDR (a `|F|` change *is* a regime change, so this is one
of the two cells that must name its regime). -/
theorem UDR_errPowers_antitone_card {F F' : FieldParams} (hc : F.card ≤ F'.card) (ρ : Rate)
    {d : ℚ} (hd : 0 ≤ d) {b : ℕ} (hb : 1 ≤ b) :
    (UDR F').errPowers ρ d b ≤ (UDR F).errPowers ρ d b :=
  errPowers_le_of_errLinear_le (UDR_standard F' ρ) (UDR_standard F ρ)
    (UDR_errLinear_antitone_card hc ρ hd) hb

/-- The `|F|` column on the multilinear path, at UDR. -/
theorem UDR_errMultilinear_antitone_card {F F' : FieldParams} (hc : F.card ≤ F'.card) (ρ : Rate)
    {d : ℚ} (hd : 0 ≤ d) (b : ℕ) :
    (UDR F').errMultilinear ρ d b ≤ (UDR F).errMultilinear ρ d b :=
  errMultilinear_le_of_errLinear_le (UDR_standard F' ρ) (UDR_standard F ρ)
    (UDR_errLinear_antitone_card hc ρ hd) b

/-! ## Instance 2: the JBR (Johnson-bound) regime

`JBR.errLinear = jbrErrLinear`, whose numerator `(2·ms⁵ + 3·ms·(θρ))·n/(3ρ·sr) + ms/sr` is `≥ 1`
because the `2·ms⁵` term (with `ms = jbrM + ½ ≥ 3.5`, since `jbrM ≥ 3`) dominates the first summand,
and the second summand `ms/sr ≥ ms ≥ 3.5` on its own clears `1`. That bound is the crux that makes
JBR `Standard`, and hence lets *every* algebraic cell theorem apply at JBR with no restatement. -/

/-- Domination: `2·ms⁵` beats `3·ms·t` once `ms ≥ 7/2` and `t ≥ −1`. -/
private theorem jbr_dom {ms t : ℚ} (hms : 7 / 2 ≤ ms) (ht : -1 ≤ t) :
    0 ≤ 2 * ms ^ 5 + 3 * ms * t := by
  have h0 : (0 : ℚ) ≤ ms := by linarith
  have h2 : (12 : ℚ) ≤ ms ^ 2 := by nlinarith [sq_nonneg (ms - 7 / 2)]
  have h4 : (144 : ℚ) ≤ ms ^ 4 := by nlinarith [sq_nonneg (ms ^ 2 - 12), h2]
  have key : 2 * ms ^ 5 + 3 * ms * t = ms * (2 * ms ^ 4 + 3 * t) := by ring
  rw [key]
  exact mul_nonneg h0 (by linarith)

/-- **The field ceiling bites at JBR.** `1/|F| ≤ jbrErrLinear` (under the standard config
conditions: `0 < ρ < 1`, `η ≤ 1`, `0 < sqrtLB ρ g ≤ 1`): the first summand is nonnegative by
`jbr_dom`, and the second is `ms/sr ≥ ms ≥ 7/2`. -/
theorem one_div_card_le_jbrErrLinear (F : FieldParams) {η : ℚ} {g : ℕ} {ρ : ℚ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : η ≤ 1) (hsr0 : 0 < sqrtLB ρ g) (hsr1 : sqrtLB ρ g ≤ 1)
    {d : ℚ} (hd : 0 ≤ d) :
    1 / (F.card : ℚ) ≤ jbrErrLinear F η g ρ d := by
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
  refine div_le_div_same (le_add_of_nonneg_of_le ?_ ?_) hc
  · exact div_nonneg (mul_nonneg hdom hn) hden.le
  · rw [le_div_iff₀ hsr0]; linarith

/-- **The JBR linear error is nonnegative** — the weaker corollary of
`one_div_card_le_jbrErrLinear` that the grind knobs consume. -/
theorem jbrErrLinear_nonneg (F : FieldParams) {η : ℚ} {g : ℕ} {ρ : ℚ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : η ≤ 1) (hsr0 : 0 < sqrtLB ρ g) (hsr1 : sqrtLB ρ g ≤ 1)
    {d : ℚ} (hd : 0 ≤ d) :
    0 ≤ jbrErrLinear F η g ρ d := by
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have h := one_div_card_le_jbrErrLinear F hρ0 hρ1 hη hsr0 hsr1 hd
  have hpos : (0 : ℚ) < 1 / (F.card : ℚ) := by positivity
  linarith

/-- **The `H` cell at JBR.** `jbrErrLinear` is monotone in the dimension `d` (it enters linearly via
`n = d/ρ`, and the coefficient is nonnegative by `jbr_dom`). Unlike `ρ`/`|F|`, `d` does not thread
through the gap `η`, so this is clean. -/
theorem jbrErrLinear_mono_dim (F : FieldParams) {η : ℚ} {g : ℕ} {ρ : ℚ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : η ≤ 1) (hsr0 : 0 < sqrtLB ρ g) (hsr1 : sqrtLB ρ g ≤ 1)
    {d d' : ℚ} (hdd : d ≤ d') :
    jbrErrLinear F η g ρ d ≤ jbrErrLinear F η g ρ d' := by
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
  have hden : (0 : ℚ) < 3 * ρ * sqrtLB ρ g := mul_pos (mul_pos (by norm_num) hρ0) hsr0
  simp only [jbrErrLinear]
  gcongr

/-- **JBR is standard.** The Johnson-bound regime has the same algebraic shape as UDR, under the
`sqrtLB`/`etaLB` side conditions that every real config meets. This is the second (and last)
regime-specific proof: with it, every algebraic cell theorem in the catalogue applies at JBR
verbatim — Airbender/OpenVM/Pico/ZisK report there. -/
theorem JBR_standard (F : FieldParams) (g : ℕ) (gap : Option ℚ) (ρ : Rate)
    (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1) :
    (JBR F g gap).Standard F ρ := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  refine ⟨fun d b => rfl, fun d b => rfl, ?_, ?_⟩
  · intro d hd
    exact one_div_card_le_jbrErrLinear F hr0 hr1 hη hsr0 hsr1 hd
  · intro d d' hdd
    exact jbrErrLinear_mono_dim F hr0 hr1 hη hsr0 hsr1 hdd

/-- **The `|F|` cell at JBR.** `jbrErrLinear` is antitone in `|F|` (it divides by `|F|`) **provided
the gap agrees** — `etaLB` depends on `card` only through the `card > 2^150` threshold, so two fields
on the same side of it give the same `η`, making the numerator `|F|`-independent. -/
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

/-- The `|F|` column on the powers path, at JBR (same gap-agreement condition). -/
theorem JBR_errPowers_antitone_card {F F' : FieldParams} (g : ℕ) (gap : Option ℚ) (ρ : Rate) {d : ℚ}
    (hηeq : etaLB (ρ : ℚ) g F'.card gap = etaLB (ρ : ℚ) g F.card gap)
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1)
    (hη' : etaLB (ρ : ℚ) g F'.card gap ≤ 1) (hcard : F.card ≤ F'.card) {b : ℕ} (hb : 1 ≤ b) :
    (JBR F' g gap).errPowers ρ d b ≤ (JBR F g gap).errPowers ρ d b :=
  errPowers_le_of_errLinear_le (JBR_standard F' g gap ρ hsr0 hsr1 hη')
    (JBR_standard F g gap ρ hsr0 hsr1 hη)
    (JBR_errLinear_antitone_card g gap ρ hηeq hd hsr0 hsr1 hη hcard) hb

/-- The `|F|` column on the multilinear path, at JBR (same gap-agreement condition). -/
theorem JBR_errMultilinear_antitone_card {F F' : FieldParams} (g : ℕ) (gap : Option ℚ) (ρ : Rate)
    {d : ℚ}
    (hηeq : etaLB (ρ : ℚ) g F'.card gap = etaLB (ρ : ℚ) g F.card gap)
    (hd : 0 ≤ d) (hsr0 : 0 < sqrtLB (ρ : ℚ) g) (hsr1 : sqrtLB (ρ : ℚ) g ≤ 1)
    (hη : etaLB (ρ : ℚ) g F.card gap ≤ 1)
    (hη' : etaLB (ρ : ℚ) g F'.card gap ≤ 1) (hcard : F.card ≤ F'.card) (b : ℕ) :
    (JBR F' g gap).errMultilinear ρ d b ≤ (JBR F g gap).errMultilinear ρ d b :=
  errMultilinear_le_of_errLinear_le (JBR_standard F' g gap ρ hsr0 hsr1 hη')
    (JBR_standard F g gap ρ hsr0 hsr1 hη)
    (JBR_errLinear_antitone_card g gap ρ hηeq hd hsr0 hsr1 hη hcard) b

end Soundcalc
