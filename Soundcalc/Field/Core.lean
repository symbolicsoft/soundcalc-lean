import Mathlib

/-!
# `Soundcalc.Field.Core` — prime fields and their extensions, with certified invariants

A field is split into two structures so the base prime is defined once and reused by every
extension (e.g. KoalaBear's degree-4 and degree-5 extensions share one `koalaBear` prime field):

* `PrimeField` — a prime `p` with a kernel-checked primality proof and its 2-adicity.
* `FieldParams` — a `PrimeField` `base` together with an extension degree `e ≥ 1`, i.e. `𝔽_{p^e}`.

The accessors `FieldParams.p`/`.twoAdicity`/`.prime`/`.card`/`.elementSizeBits` read straight
through the base, so consumers use `FieldParams` transparently.

* `prime` — a kernel-checked primality proof (`by norm_num` for the 31-bit presets; a
  `lucas_primality` Pratt certificate for Goldilocks — see `Soundcalc/Field/Goldilocks.lean`).
* `twoAdicity` — stored and certified as exactly `v₂(p - 1)`, the max power-of-2 root-of-unity
  exponent, by `twoAdicity_spec`:
  - `2 ^ twoAdicity ∣ p - 1` — a `2^twoAdicity`-th root of unity exists in `𝔽_p`;
  - `¬ 2 ^ (twoAdicity + 1) ∣ p - 1` — maximality of `twoAdicity`.
  **Known deviation from the Python:** soundcalc's `fields.py` stores `v₂(p-1)` for the NTT fields
  (Goldilocks 32, BabyBear 27, KoalaBear 24 — same values as here) but `v₂(pᵉ-1) = 33` for `M31_4`
  (whose `v₂(p-1)` is only 1, the value stored here), despite its own comment claiming `v₂(p-1)`;
  no single formula reproduces the Python values. Consumers mirroring Python semantics against
  `two_adicity` (e.g. `WHIRConfig.h_twoAdicity`) will diverge for Mersenne31 until reconciled;
  today `twoAdicity`'s only consumer is WHIR over Goldilocks, where the two agree.
* The Python's `F : float` field is intentionally dropped — `card : ℕ` is its exact replacement.
-/

namespace Soundcalc

/-- A prime field `𝔽_p`: the prime `p`, a kernel-checked primality proof, and its 2-adicity. -/
structure PrimeField where
  p               : ℕ
  prime           : p.Prime
  twoAdicity      : ℕ
  /-- `twoAdicity` is *exactly* `v₂(p - 1)`: the maximal `s` with `2 ^ s ∣ p - 1` (the second
  conjunct is maximality). Matches soundcalc's `two_adicity`. -/
  twoAdicity_spec : 2 ^ twoAdicity ∣ p - 1 ∧ ¬ 2 ^ (twoAdicity + 1) ∣ p - 1

deriving instance BEq for PrimeField
deriving instance DecidableEq for PrimeField

/-- A finite field `𝔽_{p^e}`: a `PrimeField` `base` and an extension degree `e ≥ 1`. -/
structure FieldParams where
  base : PrimeField
  e    : ℕ
  epos : 0 < e

deriving instance BEq for FieldParams
deriving instance DecidableEq for FieldParams

/-- Build the degree-`e` extension `𝔽_{p^e}` of a prime field (`e = 1` gives the prime field). -/
def PrimeField.extension (F : PrimeField) (e : ℕ) (h : 0 < e := by decide) : FieldParams :=
  { base := F, e := e, epos := h }

/-- The base prime `p`. -/
abbrev FieldParams.p (F : FieldParams) : ℕ := F.base.p
/-- Base-field 2-adicity `v₂(p - 1)`. -/
abbrev FieldParams.twoAdicity (F : FieldParams) : ℕ := F.base.twoAdicity
/-- Primality of the base prime. -/
abbrev FieldParams.prime (F : FieldParams) : F.p.Prime := F.base.prime

/-- `|F| = p ^ e`, an exact natural number — never a float. -/
def FieldParams.card (F : FieldParams) : ℕ := F.base.p ^ F.e

/-- Bits per base-field element: `⌈log₂ p⌉`
(Python `base_field_element_size_bits = math.ceil(math.log2(p))`). -/
def FieldParams.baseElementSizeBits (F : FieldParams) : ℕ := Nat.clog 2 F.base.p

/-- Bits per extension-field element: `⌈log₂ p⌉ · e` (Python
`extension_field_element_size_bits = base * field_extension_degree`). -/
def FieldParams.elementSizeBits (F : FieldParams) : ℕ := F.baseElementSizeBits * F.e

/-- Evaluate `baseElementSizeBits` (`= ⌈log₂ p⌉`) by sandwiching: `2^(n-1) < p ≤ 2^n ⟹ = n`.
`Nat.clog` is well-founded recursion so it does not reduce in the kernel; each preset discharges
`hlo`/`hhi` with `norm_num` instead. -/
theorem FieldParams.baseElementSizeBits_eq (F : FieldParams) (n : ℕ)
    (hlo : 2 ^ (n - 1) < F.base.p) (hhi : F.base.p ≤ 2 ^ n) : F.baseElementSizeBits = n := by
  have hle : Nat.clog 2 F.base.p ≤ n := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hhi
  have hlt : n - 1 < Nat.clog 2 F.base.p := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlo
  show Nat.clog 2 F.base.p = n
  omega

end Soundcalc
