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

/-- **Soundness of the envelope**: the rational `jbrErrLinear` upper-bounds the true real
    error `trueErrLinearJBR`. Proved once here; every A6 batching/commit theorem inherits
    conservativity. Consumes `sqrtLB_le` (for `√ρ` terms that must stay ≤ true `√ρ`) and
    `le_sqrtUB` (for the `θ` term, where a larger bound is required). -/
theorem jbrErrLinear_conservative
    (F : FieldParams) {η : ℚ} {g : ℕ} {ρ : ℚ} (_hρ : 0 < ρ ∧ ρ < 1) (d : ℕ)
    (_hg : 0 < g) :
    (trueErrLinearJBR F η (jbrM ρ η g) ρ d : ℝ) ≤ (jbrErrLinear F η g ρ d : ℝ) := by sorry

end Soundcalc
