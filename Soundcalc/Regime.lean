import Mathlib
import Soundcalc.SecBits

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

/-- Parameters of the finite field over which the code is defined. -/
structure FieldParams where
  card : ℕ

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
## Exit criterion

Concrete instantiation for SP1's FRI-based sumcheck, verifying that the symbolic
formula reduces to the expected closed form and achieves the claimed security level.

Parameters:
* field  : KoalaBear degree-4 extension, `|F| = p^4` where `p = 2^31 - 2^24 + 1`
* rate   : `ρ = 1/4`
* dim    : `2^21` (trace column degree)
* batch  : `193` rounds, so `⌈log₂ 193⌉ = 8` (since `2^7 = 128 < 193 ≤ 256 = 2^8`)
-/

/-- The KoalaBear prime: `p = 2^31 - 2^24 + 1`, a Mersenne-like prime chosen for
    efficient Montgomery reduction on 32-bit hardware. -/
def koalaBearPrime : ℕ := 2 ^ 31 - 2 ^ 24 + 1

/-- KoalaBear degree-4 extension field (used in SP1 / Plonky3).
    Element count: `p^4` where `p` is the KoalaBear prime. -/
def koalaBear4 : FieldParams := { card := koalaBearPrime ^ 4 }

/-- **Exit criterion — formula check.**
    The `errMultilinear` formula for `(ρ, dim, batch) = (1/4, 2^21, 193)` simplifies to
    `(3/8 · 2^23 + 1) / |F| · 8`.

    Derivation:
    * `θ = (1 - 1/4)/2 = 3/8`
    * `dim / ρ = 2^21 / (1/4) = 2^23`
    * `⌈log₂ 193⌉ = 8` -/
example : (UDR koalaBear4).errMultilinear ⟨1/4, by norm_num⟩ (2 ^ 21) 193
    = (3 / 8 * (2 : ℚ) ^ 23 + 1) / (koalaBear4.card : ℚ) * 8 := by
  have hlog : Nat.clog 2 193 = 8 := by decide
  simp only [UDR, hlog]
  push_cast
  ring

/-- **Exit criterion — security level.**
    The raw `errMultilinear` value has `secBits = 99`.

    Note: the 104-bit claim in SP1 belongs to `batchingErr`, which divides
    `errMultilinear` by `2 ^ grindBatch = 32`, adding 5 bits (99 + 5 = 104).

    Proof: `norm_num` reduces `secBits` to a `Nat.log2` of a concrete quotient;
    `native_decide` then evaluates that at native speed. -/
example : secBits ((UDR koalaBear4).errMultilinear ⟨1/4, by norm_num⟩ (2 ^ 21) 193) = 99 := by
  have hlog : Nat.clog 2 193 = 8 := by decide
  simp only [UDR, hlog]
  push_cast
  norm_num [secBits, koalaBear4, koalaBearPrime]
  -- remaining goal: (koalaBearPrime ^ 4 / 25165832).log2 = 99
  native_decide

end Soundcalc
