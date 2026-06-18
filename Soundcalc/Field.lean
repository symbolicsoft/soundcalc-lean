import Mathlib

/-!
# `Soundcalc.Field` — field parameters with certified invariants (roadmap S2)

Mirrors `soundcalc/common/fields.py`'s `FieldParams`, but every invariant
travels as a *proof* and every size is an exact `ℕ` — no floats.

* `prime` — `by norm_num` (kernel-checked, axiom-clean) for KoalaBear's 31-bit
  prime.
* `twoAdicity` — the field's max power-of-2 root-of-unity exponent. It is
  *stored*, not derived: across presets it is `v₂(p-1)` for the NTT fields but
  `v₂(pᵉ-1)` for Mersenne31 (whose `v₂(p-1)` is only 1), so no single formula
  reproduces it. It is certified by `twoAdicity_spec`, which is characterized
  by two conjuncts:
  - `2 ^ twoAdicity ∣ p - 1` ensures `2 ^ twoAdicity` divides `p-1` (i.e., a
    `2^twoAdicity`-th root of unity exists in `F`);
  - `¬ 2 ^ (twoAdicity + 1) ∣ p - 1` ensures `2 ^ (twoAdicity+1)` does *not*
    divide `p-1`, enforcing maximality of `twoAdicity`.
  The above capture the one invariant true for every preset (`v₂(p-1)`).
* The Python's `F : float` field is intentionally dropped — `card : ℕ` is its
  exact replacement. (`name : String` for the S9 renderer can be added later.)
-/

/-
* *TODO*: Include Goldilocks/BN254-scale primes using a `lucas_primality` Pratt
  certificate - `native_decide` is avoided (it taxes the TCB and is slow).
  This comes later in the roadmap.
-/

namespace Soundcalc.Field

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

/-- `|F| = p ^ e`, an exact natural number — never a float. -/
def FieldParams.card (F : FieldParams) : ℕ := F.p ^ F.e

/-- Bits per base-field element: `⌈log₂ p⌉`
(Python `base_field_element_size_bits = math.ceil(math.log2(p))`). -/
def FieldParams.baseElementSizeBits (F : FieldParams) : ℕ := Nat.clog 2 F.p

/-- Bits per extension-field element: `⌈log₂ p⌉ · e` (Python
`extension_field_element_size_bits = base * field_extension_degree`). -/
def FieldParams.elementSizeBits (F : FieldParams) : ℕ := F.baseElementSizeBits * F.e

/-- KoalaBear, `p = 2^31 - 2^24 + 1`; SP1 uses its degree-4 extension. -/
def koalaBear4 : FieldParams where
  p               := 2 ^ 31 - 2 ^ 24 + 1
  e               := 4
  twoAdicity      := 24
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-! ## S2 exit criteria (all kernel-checked, no `sorry`, no `native_decide`) -/

/-- `|F|` matches the Python `field.F` for SP1 core. -/
example : koalaBear4.card = (2 ^ 31 - 2 ^ 24 + 1) ^ 4 := by
  unfold FieldParams.card koalaBear4; norm_num

/-- Reusable pattern for evaluating `Nat.clog` without `decide`/`native_decide`
(it is well-founded recursion, so it does not reduce in the kernel): bound it
both ways via the characterization lemmas, then `omega`. -/
theorem koalaBear4_baseBits : koalaBear4.baseElementSizeBits = 31 := by
  show Nat.clog 2 (2 ^ 31 - 2 ^ 24 + 1) = 31
  have hle : Nat.clog 2 (2 ^ 31 - 2 ^ 24 + 1) ≤ 31 := by
    rw [Nat.clog_le_iff_le_pow]
    norm_num
    norm_num
  have hlt : 30 < Nat.clog 2 (2 ^ 31 - 2 ^ 24 + 1) := by
    rw [Nat.lt_clog_iff_pow_lt]
    norm_num
    norm_num
  omega

/-- An extension-field element of KoalaBear⁴ is 124 bits (`31 · 4`). -/
theorem koalaBear4_elementBits : koalaBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, koalaBear4_baseBits]; rfl

end Soundcalc.Field
