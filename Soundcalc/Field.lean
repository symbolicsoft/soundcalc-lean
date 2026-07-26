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
* Goldilocks (`goldilocks3`, below) is certified by a kernel-checked `lucas_primality`
  Pratt certificate — no `native_decide` — see the `Goldilocks` namespace at the end of
  this file. The larger BN254-scale primes are left for later in the roadmap.
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

/-! ## Mersenne31 -/

/-- Mersenne31, `p = 2^31 − 1`; Airbender uses its degree-4 extension, `|F| ≈ 2^124`. -/
def mersenne31_4 : FieldParams where
  p               := 2 ^ 31 - 1
  e               := 4
  twoAdicity      := 1
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-- `|F|` matches the Python `M31_4.F`. -/
example : mersenne31_4.card = (2 ^ 31 - 1) ^ 4 := by
  unfold FieldParams.card mersenne31_4; norm_num

/-- An M31⁴ element is 124 bits (`31 · 4`) — same sandwich proof as `koalaBear4_baseBits`. -/
theorem mersenne31_4_baseBits : mersenne31_4.baseElementSizeBits = 31 := by
  show Nat.clog 2 (2 ^ 31 - 1) = 31
  have hle : Nat.clog 2 (2 ^ 31 - 1) ≤ 31 := by
    rw [Nat.clog_le_iff_le_pow] <;> norm_num
  have hlt : 30 < Nat.clog 2 (2 ^ 31 - 1) := by
    rw [Nat.lt_clog_iff_pow_lt] <;> norm_num
  omega

theorem mersenne31_4_elementBits : mersenne31_4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, mersenne31_4_baseBits]; rfl

/-! ## BabyBear -/

/-- BabyBear, `p = 2^31 - 2^27 + 1`; OpenVM uses its degree-4 extension. -/
def babyBear4 : FieldParams where
  p               := 2 ^ 31 - 2 ^ 27 + 1
  e               := 4
  twoAdicity      := 27
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-- `|F|` matches the Python `BABYBEAR_4.F`. -/
example : babyBear4.card = (2 ^ 31 - 2 ^ 27 + 1) ^ 4 := by
  unfold FieldParams.card babyBear4; norm_num

theorem babyBear4_baseBits : babyBear4.baseElementSizeBits = 31 := by
  show Nat.clog 2 (2 ^ 31 - 2 ^ 27 + 1) = 31
  have hle : Nat.clog 2 (2 ^ 31 - 2 ^ 27 + 1) ≤ 31 := by
    rw [Nat.clog_le_iff_le_pow] <;> norm_num
  have hlt : 30 < Nat.clog 2 (2 ^ 31 - 2 ^ 27 + 1) := by
    rw [Nat.lt_clog_iff_pow_lt] <;> norm_num
  omega

theorem babyBear4_elementBits : babyBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, babyBear4_baseBits]; rfl

/-! ## Goldilocks

The 64-bit prime `p = 2^64 - 2^32 + 1` is out of reach for kernel `decide`/`norm_num` (trial
division to √p ≈ 2^32), and we avoid `native_decide`. The `Goldilocks` namespace below proves
primality with a **Pratt certificate** (`lucas_primality`, primitive root 7,
`p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`): each modular exponentiation is discharged by
`decide` over `modPow`, a square-and-multiply *structural in an explicit `fuel`* so the kernel
reduces it in `O(fuel)` steps. Kernel-checked, `native_decide`-free. -/

namespace Goldilocks

/-- Modular exponentiation `base ^ e % m` by square-and-multiply, with an explicit `fuel`
    bound. Recursion is structural in `fuel`, so the kernel evaluates it in `O(fuel)` steps
    (unlike well-founded recursion on `e`, which does not reduce in the kernel). -/
def modPow (m : ℕ) : (fuel base e : ℕ) → ℕ
  | 0,        _,    _ => 1 % m
  | fuel + 1, base, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then modPow m fuel (base * base % m) (e / 2) * base % m
    else modPow m fuel (base * base % m) (e / 2)

/-- `modPow` computes `base ^ e % m`, provided `fuel` is a large enough bit budget. -/
theorem modPow_eq (m : ℕ) :
    ∀ (fuel base e : ℕ), e < 2 ^ fuel → modPow m fuel base e = base ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro base e he
    rw [pow_zero] at he
    have : e = 0 := by omega
    subst this
    simp [modPow]
  | succ fuel ih =>
    intro base e he
    rw [modPow]
    by_cases he0 : e = 0
    · subst he0; simp
    · rw [if_neg he0]
      have hhalf : e / 2 < 2 ^ fuel := by rw [pow_succ] at he; omega
      have hr : modPow m fuel (base * base % m) (e / 2) = (base * base % m) ^ (e / 2) % m :=
        ih (base * base % m) (e / 2) hhalf
      have hsq : (base * base % m) ^ (e / 2) % m = base ^ (2 * (e / 2)) % m := by
        have hmm : base * base % m ≡ base ^ 2 [MOD m] := by
          rw [pow_two]; exact Nat.mod_modEq _ _
        calc (base * base % m) ^ (e / 2) % m
            = (base ^ 2) ^ (e / 2) % m := hmm.pow _
          _ = base ^ (2 * (e / 2)) % m := by rw [← pow_mul]
      by_cases hpar : e % 2 = 1
      · rw [if_pos hpar, hr, hsq]
        calc base ^ (2 * (e / 2)) % m * base % m
            = base ^ (2 * (e / 2)) * base % m := (Nat.mod_modEq _ m).mul_right base
          _ = base ^ (2 * (e / 2) + 1) % m := by rw [pow_succ]
          _ = base ^ e % m := by rw [show 2 * (e / 2) + 1 = e from by omega]
      · rw [if_neg hpar, hr, hsq, show 2 * (e / 2) = e from by omega]

/-- Bridge: `(7 : ZMod m) ^ E = ↑(modPow m 64 7 E)` for any `E < 2^64`. -/
private theorem zmod_pow_eq (m E : ℕ) (hE : E < 2 ^ 64) :
    (7 : ZMod m) ^ E = ((modPow m 64 7 E : ℕ) : ZMod m) := by
  rw [modPow_eq m 64 7 E hE, ZMod.natCast_mod]
  push_cast
  ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- The Goldilocks prime, via a kernel-checked Pratt certificate (`a = 7`,
    `p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`). -/
theorem goldilocks_prime : Nat.Prime (2 ^ 64 - 2 ^ 32 + 1) := by
  refine lucas_primality (2 ^ 64 - 2 ^ 32 + 1) (7 : ZMod (2 ^ 64 - 2 ^ 32 + 1)) ?_ ?_
  · -- 7 ^ (p-1) = 1
    rw [zmod_pow_eq _ _ (by norm_num),
        show modPow (2 ^ 64 - 2 ^ 32 + 1) 64 7 (2 ^ 64 - 2 ^ 32 + 1 - 1) = 1 from by decide]
    exact Nat.cast_one
  · -- ∀ prime q ∣ p-1, 7 ^ ((p-1)/q) ≠ 1
    intro q hq hqd
    have hfact : 2 ^ 64 - 2 ^ 32 + 1 - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by norm_num
    rw [hfact] at hqd
    -- reduce a `≠ 1` goal to a `decide`-able `modPow` residue fact
    have hne : ∀ E : ℕ, E < 2 ^ 64 →
        modPow (2 ^ 64 - 2 ^ 32 + 1) 64 7 E % (2 ^ 64 - 2 ^ 32 + 1) ≠ 1 % (2 ^ 64 - 2 ^ 32 + 1) →
        (7 : ZMod (2 ^ 64 - 2 ^ 32 + 1)) ^ E ≠ 1 := by
      intro E hE hmod hc
      rw [zmod_pow_eq _ _ hE,
          show (1 : ZMod (2 ^ 64 - 2 ^ 32 + 1)) = ((1 : ℕ) : ZMod (2 ^ 64 - 2 ^ 32 + 1)) from
            (Nat.cast_one).symm,
          ZMod.natCast_eq_natCast_iff] at hc
      exact hmod hc
    rcases hq.dvd_mul.mp hqd with h | h65537
    rcases hq.dvd_mul.mp h with h | h257
    rcases hq.dvd_mul.mp h with h | h17
    rcases hq.dvd_mul.mp h with h | h5
    rcases hq.dvd_mul.mp h with h2 | h3
    · rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)]
      exact hne _ (by norm_num) (by decide)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3]
      exact hne _ (by norm_num) (by decide)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5]
      exact hne _ (by norm_num) (by decide)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17]
      exact hne _ (by norm_num) (by decide)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h257]
      exact hne _ (by norm_num) (by decide)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h65537]
      exact hne _ (by norm_num) (by decide)

end Goldilocks

/-- Goldilocks, `p = 2^64 - 2^32 + 1`; ZisK uses its degree-3 extension. -/
def goldilocks3 : FieldParams where
  p               := 2 ^ 64 - 2 ^ 32 + 1
  e               := 3
  twoAdicity      := 32
  prime           := Goldilocks.goldilocks_prime   -- kernel-clean Pratt cert (`Goldilocks` above)
  epos            := by decide
  twoAdicity_spec := by decide

/-- `|F|` matches the Python `GOLDILOCKS_3.F`. -/
example : goldilocks3.card = (2 ^ 64 - 2 ^ 32 + 1) ^ 3 := by
  unfold FieldParams.card goldilocks3; norm_num

theorem goldilocks3_baseBits : goldilocks3.baseElementSizeBits = 64 := by
  show Nat.clog 2 (2 ^ 64 - 2 ^ 32 + 1) = 64
  have hle : Nat.clog 2 (2 ^ 64 - 2 ^ 32 + 1) ≤ 64 := by
    rw [Nat.clog_le_iff_le_pow] <;> norm_num
  have hlt : 63 < Nat.clog 2 (2 ^ 64 - 2 ^ 32 + 1) := by
    rw [Nat.lt_clog_iff_pow_lt] <;> norm_num
  omega

theorem goldilocks3_elementBits : goldilocks3.elementSizeBits = 192 := by
  rw [FieldParams.elementSizeBits, goldilocks3_baseBits]; rfl

end Soundcalc
