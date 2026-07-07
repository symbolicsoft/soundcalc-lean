import Mathlib
import Soundcalc.Field
import Soundcalc.Common.Sqrt

namespace Soundcalc

/-!
# Regime: parametrised error-bound structure for code-based proof systems

A `Regime` bundles five formulas describing how error probabilities and list sizes
scale with the *code rate* ρ and the *dimension* `dim` (and, for power/multilinear
checks, a *batch size*).

All five formulas are only meaningful when the rate lies strictly inside the unit
interval.  We enforce this by defining `Rate` — a subtype of ℚ that carries the
proof `0 < ρ < 1` — and using it as the domain of every field.  The constraint is
therefore part of the type, not a side-condition on each call.
-/

/-- A code rate restricted to the open unit interval `(0, 1)`.
    Both bounds are strict:
    * `0 < ρ` ensures the denominator in `d / ρ` is nonzero.
    * `ρ < 1` ensures the distance `1 - ρ > 0`, so the decoder has room to correct
      errors. -/
abbrev Rate := {ρ : ℚ // 0 < ρ ∧ ρ < 1}

/-!
## The Regime structure

Each field is a function of a `Rate` (and possibly `dim`, `batch`), returning a
rational number representing an error probability or list size.
-/

/-- Bundle of error-bound and list-size formulas for a decoding regime.

| field             | meaning                                                            |
|-------------------|--------------------------------------------------------------------|
| `θ`               | relative-distance threshold used by the decoder                    |
| `listSize`        | worst-case number of codewords output by the decoder               |
| `errLinear`       | soundness error for a single linear check                          |
| `errPowers`       | soundness error for a batch of power checks                        |
| `errMultilinear`  | soundness error for a batch of multilinear (sumcheck) rounds       |
-/
structure Regime where
  θ              : Rate → (dim : ℕ) → ℚ
  listSize       : Rate → (dim : ℕ) → ℚ
  errLinear      : Rate → (dim : ℕ) → ℚ
  errPowers      : Rate → (dim : ℕ) → (batch : ℕ) → ℚ
  errMultilinear : Rate → (dim : ℕ) → (batch : ℕ) → ℚ

/-!
## Unique Decoding Regime (UDR)

The classical decoder corrects up to *half* the minimum distance:

* `θ ρ = (1 - ρ) / 2`
  — the decoder's relative distance threshold is half the code's relative distance.

* `listSize = 1`
  — unique decoding: at most one codeword lies within distance `θ` of the received
  word.

* `errLinear ρ d = (θ * (d/ρ) + 1) / |F|`
  — Schwartz-Zippel bound for a polynomial of degree `d/ρ` over the field `F`.

* `errPowers ρ d batch = errLinear ρ d * (batch - 1)`
  — union bound over `batch - 1` independent power checks.

* `errMultilinear ρ d batch = errLinear ρ d * ⌈log₂ batch⌉`
  — sumcheck with `⌈log₂ batch⌉` rounds, one error term per round.
-/

/-- The Unique Decoding Regime instance.
    We destructure `⟨ρ, _⟩ : Rate` in each field to extract the value `ρ : ℚ`;
    the proof component is not needed in the formula but is enforced by the type. -/
def UDR (F : FieldParams) : Regime where
  θ              := fun ⟨ρ, _⟩ _   => (1 - ρ) / 2
  listSize       := fun _      _   => 1
  errLinear      := fun ⟨ρ, _⟩ d   => ((1 - ρ) / 2 * (d / ρ) + 1) / (F.card : ℚ)
  errPowers      := fun ⟨ρ, _⟩ d b => ((1 - ρ) / 2 * (d / ρ) + 1) / (F.card : ℚ) * (b - 1)
  errMultilinear := fun ⟨ρ, _⟩ d b => ((1 - ρ) / 2 * (d / ρ) + 1) / (F.card : ℚ) * (Nat.clog 2 b : ℚ)

/-!
## Johnson Bound Regime (JBR)

Conservative rational envelope for the MCA error of BCHKS25 Theorem 4.2.
Parametrised by the rational gap `η` and the A1 granularity `g`; every `√ρ`
appearance is replaced by `sqrtLB` or `sqrtUB` in whichever direction keeps the
result an upper bound.
-/

/-- JBR multiplicity `m = max(⌈√ρ / (2η)⌉, 3)` (BCHKS25 Thm 4.2).
    Rounded **up** via `sqrtUB` since the error formula is increasing in `m`. -/
def jbrM (ρ η : ℚ) (g : ℕ) : ℕ :=
  max ⌈sqrtUB ρ g / (2 * η)⌉₊ 3

/-- Certified **upper bound** on the JBR linear MCA error (BCHKS25 Thm 4.2).
    Every `√ρ` is replaced by `sqrtLB` because the error is decreasing in `√ρ`, so
    substituting a smaller value makes the bound larger (conservative). -/
def jbrErrLinear (F : FieldParams) (η : ℚ) (g : ℕ) (ρ : ℚ) (d : ℕ) : ℚ :=
  let sr     := sqrtLB ρ g
  let m      := (jbrM ρ η g : ℚ)
  let ms     := m + 1 / 2
  let n      := (d : ℚ) / ρ
  let θ      := (1 - η) - sr
  let first  := (2 * ms ^ 5 + 3 * ms * (θ * ρ)) * n / (3 * ρ * sr)
  let second := ms / sr
  (first + second) / (F.card : ℚ)

/-- The Johnson Bound Regime as a certified conservative envelope.
    `η` is the rational gap parameter and `g` the A1 granularity.
    Each field rounds `√ρ` in the direction that makes the output an upper bound:
    - `θ` uses `sqrtUB` (larger √ρ → smaller θ → fewer codewords in the list, conservative);
    - `listSize` and `errLinear` use `sqrtLB` (smaller √ρ → larger error/list). -/
def JBR (F : FieldParams) (η : ℚ) (g : ℕ) : Regime where
  θ              := fun ⟨ρ, _⟩ _   => (1 - η) - sqrtUB ρ g
  listSize       := fun ⟨ρ, _⟩ _   => 1 / (2 * η * sqrtLB ρ g)
  errLinear      := fun ⟨ρ, _⟩ d   => jbrErrLinear F η g ρ d
  errPowers      := fun ⟨ρ, _⟩ d b => jbrErrLinear F η g ρ d * (b - 1)
  errMultilinear := fun ⟨ρ, _⟩ d b => jbrErrLinear F η g ρ d * (Nat.clog 2 b : ℚ)

/-- The **true** real-valued Johnson linear error (BCHKS25 Thm 4.2): the quantity that the
    rational `jbrErrLinear` is proven to over-approximate. Uses the genuine irrational
    `Real.sqrt ρ`, so it is `noncomputable` and is never `decide`d — only bounded. -/
noncomputable def trueErrLinearJBR
    (F : FieldParams) (η : ℚ) (m : ℕ) (ρ : ℚ) (d : ℕ) : ℝ :=
  let sr : ℝ := Real.sqrt (ρ : ℝ)
  let ms : ℝ := (m : ℝ) + 1 / 2
  let n  : ℝ := (d : ℝ) / (ρ : ℝ)
  let θ  : ℝ := (1 - (η : ℝ)) - sr
  let first  : ℝ := (2 * ms ^ 5 + 3 * ms * (θ * (ρ : ℝ))) * n / (3 * (ρ : ℝ) * sr)
  let second : ℝ := ms / sr
  (first + second) / (F.card : ℝ)

/--
Core monotonicity lemma for the JBR linear-error expression.

Fix all parameters except the square-root term. If `0 < L <= S`, then replacing
`S` by the smaller value `L` makes the JBR expression larger. In plain terms:
the error bound is decreasing in the square-root parameter, provided `η <= 1`
and the relevant coefficients are nonnegative.
-/
private lemma jbrCore_mono
    {M R D E L S : ℝ}
    (hR : 0 < R)
    (hD : 0 ≤ D)
    (hM : 0 ≤ M)
    (hE : E ≤ 1)
    (hL : 0 < L)
    (hS : 0 < S)
    (hLS : L ≤ S) :
    ((2 * M ^ 5 + 3 * M * (((1 - E) - S) * R)) * (D / R) / (3 * R * S) + M / S)
      ≤
    ((2 * M ^ 5 + 3 * M * (((1 - E) - L) * R)) * (D / R) / (3 * R * L) + M / L) := by
  let A : ℝ :=
    D * (2 * M ^ 5 + 3 * M * ((1 - E) * R)) / (3 * R ^ 2) + M

  have hRne : R ≠ 0 := ne_of_gt hR
  have hLne : L ≠ 0 := ne_of_gt hL
  have hSne : S ≠ 0 := ne_of_gt hS

  have h1E : 0 ≤ 1 - E := by
    linarith

  have hterm :
      0 ≤ 2 * M ^ 5 + 3 * M * ((1 - E) * R) := by
    have hpow : 0 ≤ M ^ 5 := pow_nonneg hM 5
    have hprod : 0 ≤ M * ((1 - E) * R) := by
      exact mul_nonneg hM (mul_nonneg h1E (le_of_lt hR))
    nlinarith

  have hden_nonneg : 0 ≤ 3 * R ^ 2 := by
    exact mul_nonneg (by norm_num) (sq_nonneg R)

  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (div_nonneg (mul_nonneg hD hterm) hden_nonneg)
      hM

  have hinv : 1 / S ≤ 1 / L := by
    exact one_div_le_one_div_of_le hL hLS

  have hmono : A * (1 / S) ≤ A * (1 / L) := by
    exact mul_le_mul_of_nonneg_left hinv hA_nonneg

  have hS_rewrite :
      ((2 * M ^ 5 + 3 * M * (((1 - E) - S) * R)) * (D / R) / (3 * R * S) + M / S)
        =
      A * (1 / S) - M * D / R := by
    dsimp [A]
    field_simp [hRne, hSne]
    ring

  have hL_rewrite :
      ((2 * M ^ 5 + 3 * M * (((1 - E) - L) * R)) * (D / R) / (3 * R * L) + M / L)
        =
      A * (1 / L) - M * D / R := by
    dsimp [A]
    field_simp [hRne, hLne]
    ring

  calc
    ((2 * M ^ 5 + 3 * M * (((1 - E) - S) * R)) * (D / R) / (3 * R * S) + M / S)
        = A * (1 / S) - M * D / R := hS_rewrite
    _ ≤ A * (1 / L) - M * D / R := by
        exact sub_le_sub_right hmono (M * D / R)
    _ =
      ((2 * M ^ 5 + 3 * M * (((1 - E) - L) * R)) * (D / R) / (3 * R * L) + M / L) := by
        exact hL_rewrite.symm


/--
The rational JBR linear-error formula upper-bounds the true real-valued formula.

The true formula uses the exact value `sqrt ρ`, while `jbrErrLinear` replaces it
by the rational lower approximation `sqrtLB ρ g`. Since `sqrtLB ρ g <= sqrt ρ`
and the JBR expression is decreasing in this square-root parameter, this
replacement gives a conservative upper bound.

The hypothesis `hsr` ensures that the lower approximation is positive, so the
division by `sqrtLB ρ g` is meaningful.
-/
theorem jbrErrLinear_conservative
    (F : FieldParams) {η : ℚ} {g : ℕ} {ρ : ℚ}
    (hρ : 0 < ρ ∧ ρ < 1) (d : ℕ)
    (hg : 0 < g)
    (hη : η ≤ 1)
    (hsr : 0 < sqrtLB ρ g) :
    (trueErrLinearJBR F η (jbrM ρ η g) ρ d : ℝ)
      ≤ (jbrErrLinear F η g ρ d : ℝ) := by
  have hρR_pos : (0 : ℝ) < (ρ : ℝ) := by
    exact_mod_cast hρ.1

  have hρR_nonneg : (0 : ℝ) ≤ (ρ : ℝ) := le_of_lt hρR_pos

  have hηR : (η : ℝ) ≤ 1 := by
    exact_mod_cast hη

  have hL_pos : (0 : ℝ) < (sqrtLB ρ g : ℝ) := by
    exact_mod_cast hsr

  have hS_pos : (0 : ℝ) < Real.sqrt (ρ : ℝ) := by
    exact Real.sqrt_pos.mpr hρR_pos

  have hLB :
      (sqrtLB ρ g : ℝ) ≤ Real.sqrt (ρ : ℝ) := by
    exact sqrtLB_le (ρ := ρ) (le_of_lt hρ.1) (g := g) hg

  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.zero_le d

  have hm_nonneg : (0 : ℝ) ≤ (jbrM ρ η g : ℝ) := by
    exact_mod_cast Nat.zero_le (jbrM ρ η g)

  have hms_nonneg :
      (0 : ℝ) ≤ (jbrM ρ η g : ℝ) + 1 / 2 := by
    exact add_nonneg hm_nonneg (by norm_num)

  have hcardNat : 0 < F.card := by
    unfold FieldParams.card
    exact Nat.pow_pos (a := F.p) (n := F.e) (Nat.Prime.pos F.prime)

  have hcardR : (0 : ℝ) < (F.card : ℝ) := by
    exact_mod_cast hcardNat

  have hcore :
      ((2 * ((jbrM ρ η g : ℝ) + 1 / 2) ^ 5
          + 3 * ((jbrM ρ η g : ℝ) + 1 / 2)
              * ((((1 : ℝ) - (η : ℝ)) - Real.sqrt (ρ : ℝ)) * (ρ : ℝ)))
          * ((d : ℝ) / (ρ : ℝ))
          / (3 * (ρ : ℝ) * Real.sqrt (ρ : ℝ))
        + ((jbrM ρ η g : ℝ) + 1 / 2) / Real.sqrt (ρ : ℝ))
      ≤
      ((2 * ((jbrM ρ η g : ℝ) + 1 / 2) ^ 5
          + 3 * ((jbrM ρ η g : ℝ) + 1 / 2)
              * ((((1 : ℝ) - (η : ℝ)) - (sqrtLB ρ g : ℝ)) * (ρ : ℝ)))
          * ((d : ℝ) / (ρ : ℝ))
          / (3 * (ρ : ℝ) * (sqrtLB ρ g : ℝ))
        + ((jbrM ρ η g : ℝ) + 1 / 2) / (sqrtLB ρ g : ℝ)) := by
    exact jbrCore_mono
      (M := (jbrM ρ η g : ℝ) + 1 / 2)
      (R := (ρ : ℝ))
      (D := (d : ℝ))
      (E := (η : ℝ))
      (L := (sqrtLB ρ g : ℝ))
      (S := Real.sqrt (ρ : ℝ))
      hρR_pos
      hd_nonneg
      hms_nonneg
      hηR
      hL_pos
      hS_pos
      hLB

  have hdiv :
      ((2 * ((jbrM ρ η g : ℝ) + 1 / 2) ^ 5
          + 3 * ((jbrM ρ η g : ℝ) + 1 / 2)
              * ((((1 : ℝ) - (η : ℝ)) - Real.sqrt (ρ : ℝ)) * (ρ : ℝ)))
          * ((d : ℝ) / (ρ : ℝ))
          / (3 * (ρ : ℝ) * Real.sqrt (ρ : ℝ))
        + ((jbrM ρ η g : ℝ) + 1 / 2) / Real.sqrt (ρ : ℝ))
        / (F.card : ℝ)
      ≤
      ((2 * ((jbrM ρ η g : ℝ) + 1 / 2) ^ 5
          + 3 * ((jbrM ρ η g : ℝ) + 1 / 2)
              * ((((1 : ℝ) - (η : ℝ)) - (sqrtLB ρ g : ℝ)) * (ρ : ℝ)))
          * ((d : ℝ) / (ρ : ℝ))
          / (3 * (ρ : ℝ) * (sqrtLB ρ g : ℝ))
        + ((jbrM ρ η g : ℝ) + 1 / 2) / (sqrtLB ρ g : ℝ))
        / (F.card : ℝ) := by
    exact div_le_div_of_nonneg_right hcore (le_of_lt hcardR)

  simpa [trueErrLinearJBR, jbrErrLinear] using hdiv


end Soundcalc
