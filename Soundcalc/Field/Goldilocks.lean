import Soundcalc.Field.Core
import Soundcalc.Field.Pratt

/-!
# Goldilocks — `p = 2^64 - 2^32 + 1`; ZisK uses its degree-3 extension.

The 64-bit prime is out of reach for kernel `decide`/`norm_num` (trial division to √p ≈ 2^32),
and we avoid `native_decide`. The `Goldilocks` namespace below proves primality with a **Pratt
certificate** (`lucas_primality`, primitive root 7, `p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`):
each modular exponentiation is discharged by `decide` over `Soundcalc.Pratt.modPow`, a
square-and-multiply *structural in an explicit `fuel`* so the kernel reduces it in `O(fuel)` steps
(see `Soundcalc.Field.Pratt`). Kernel-checked, `native_decide`-free.
-/

namespace Soundcalc

namespace Goldilocks

open Soundcalc.Pratt

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
