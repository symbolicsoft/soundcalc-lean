import Mathlib

/-!
# `Soundcalc.Field.Core` — field parameters with certified invariants (roadmap S2)

Mirrors `soundcalc/common/fields.py`'s `FieldParams`, but every invariant travels as a *proof*
and every size is an exact `ℕ` — no floats.

* `prime` — a kernel-checked primality proof (`by norm_num` for the 31-bit presets; a
  `lucas_primality` Pratt certificate for Goldilocks — see `Soundcalc/Field/Goldilocks.lean`).
* `twoAdicity` — stored and certified as exactly `v₂(p - 1)`, the base field's max power-of-2
  root-of-unity exponent, by `twoAdicity_spec`:
  - `2 ^ twoAdicity ∣ p - 1` — a `2^twoAdicity`-th root of unity exists in `𝔽_p`;
  - `¬ 2 ^ (twoAdicity + 1) ∣ p - 1` — maximality of `twoAdicity`.
  **Known deviation from the Python:** soundcalc's `fields.py` stores `v₂(p-1)` for the NTT fields
  (Goldilocks 32, BabyBear 27, KoalaBear 24 — same values as here) but `v₂(pᵉ-1) = 33` for `M31_4`
  (whose `v₂(p-1)` is only 1, the value stored here), despite its own comment claiming `v₂(p-1)`;
  no single formula reproduces the Python values. Consumers mirroring Python semantics against
  `two_adicity` (e.g. `WHIRConfig.h_twoAdicity`) will diverge for Mersenne31 until reconciled;
  today `twoAdicity`'s only consumer is WHIR over Goldilocks, where the two agree.
* The Python's `F : float` field is intentionally dropped — `card : ℕ` is its exact replacement.

The concrete presets live one-per-file in `Soundcalc/Field/`: `KoalaBear`, `Mersenne31`,
`BabyBear`, `Goldilocks`. `Soundcalc/Field.lean` re-exports this module and all of them.
-/

namespace Soundcalc

/-- A finite field `F = 𝔽_{p^e}`, carrying *proofs* of its invariants. -/
structure FieldParams where
  p              : ℕ
  e              : ℕ
  twoAdicity     : ℕ
  prime          : p.Prime
  epos           : 0 < e
  /-- `twoAdicity` is *exactly* `v₂(p - 1)`: the maximal `s` with `2 ^ s ∣ p - 1`
  (the second conjunct is maximality, since divisibility by powers of two is
  downward-closed). Matches soundcalc's `two_adicity`. -/
  twoAdicity_spec : 2 ^ twoAdicity ∣ p - 1 ∧ ¬ 2 ^ (twoAdicity + 1) ∣ p - 1

/- Introducing exact equality for `FieldParams` structures.
   The comparison is operated on a per-ℕ field basis. -/
deriving instance BEq for FieldParams
deriving instance DecidableEq for FieldParams

/-- `|F| = p ^ e`, an exact natural number — never a float. -/
def FieldParams.card (F : FieldParams) : ℕ := F.p ^ F.e

/-- Bits per base-field element: `⌈log₂ p⌉`
(Python `base_field_element_size_bits = math.ceil(math.log2(p))`). -/
def FieldParams.baseElementSizeBits (F : FieldParams) : ℕ := Nat.clog 2 F.p

/-- Bits per extension-field element: `⌈log₂ p⌉ · e` (Python
`extension_field_element_size_bits = base * field_extension_degree`). -/
def FieldParams.elementSizeBits (F : FieldParams) : ℕ := F.baseElementSizeBits * F.e

end Soundcalc
