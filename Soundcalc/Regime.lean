import Mathlib
import Soundcalc.SecBits
import Soundcalc.Field

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
def UDR (F : Field.FieldParams) : Regime where
  θ              := fun ⟨ρ, _⟩ _   => (1 - ρ) / 2
  listSize       := fun _      _   => 1
  errLinear      := fun ⟨ρ, _⟩ d   => ((1 - ρ) / 2 * (d / ρ) + 1) / (F.card : ℚ)
  errPowers      := fun ⟨ρ, _⟩ d b => ((1 - ρ) / 2 * (d / ρ) + 1) / (F.card : ℚ) * (b - 1)
  errMultilinear := fun ⟨ρ, _⟩ d b => ((1 - ρ) / 2 * (d / ρ) + 1) / (F.card : ℚ) * (Nat.clog 2 b : ℚ)

end Soundcalc
