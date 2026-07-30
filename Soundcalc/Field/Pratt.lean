import Mathlib

/-!
# Pratt-certificate helpers — kernel-reducible modular exponentiation.

`modPow` is square-and-multiply, structural in an explicit `fuel`, so the kernel reduces
`modPow m fuel base e` in `O(fuel)` steps (unlike well-founded recursion on the exponent, which
does not reduce in the kernel). This is the workhorse behind `lucas_primality` Pratt certificates
for primes out of reach of `decide`/`norm_num` (trial division to √p) and without `native_decide`.
Any field whose modulus needs such a certificate can reuse `modPow`/`modPow_eq` from here.
-/

namespace Soundcalc

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

end Soundcalc
