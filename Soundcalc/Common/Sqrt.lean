import Mathlib

namespace Soundcalc

/--
Integer approximation to the scaled square root.

For a nonnegative rational ρ and a natural granularity g, this is

  [√(g^2 . ρ)]

Since ρ = ρ.num / ρ.den, the quantity inside the square root is represented as

  (ρ.num . g^2) / ρ.den.
-/
def isqrtScaled (ρ : ℚ) (g : ℕ) : ℕ :=
  Nat.sqrt (ρ.num.toNat * g ^ 2 / ρ.den)

/--
Rational lower approximation to √ρ at granularity g.

Mathematically,

  sqrtLB(ρ,g) = [√(g^2 . ρ)] / g.

For ρ >= 0 and g > 0, this lies below √ρ.
-/
def sqrtLB (ρ : ℚ) (g : ℕ) : ℚ :=
  (isqrtScaled ρ g : ℚ) / g

/--
Rational upper approximation to √ρ at granularity g.

Mathematically,

  sqrtUB(ρ,g) = ([√(g^2 . ρ)] + 1) / g.

For ρ >= 0 and g > 0, this lies above √ρ.
-/
def sqrtUB (ρ : ℚ) (g : ℕ) : ℚ :=
  (isqrtScaled ρ g + 1 : ℚ) / g

/--
Scaled rational identity for a nonnegative rational.

If ρ = a / b with a >= 0 and b > 0, then

  (a . g^2) / b = ρ . g^2.

In Lean, ρ.num.toNat represents the numerator a as a natural number.
This is valid because ρ >= 0.
-/
private lemma scaled_num_div_den_eq {ρ : ℚ} (hρ : 0 ≤ ρ) (g : ℕ) :
    (((ρ.num.toNat * g ^ 2 : ℕ) : ℚ) / (ρ.den : ℚ))
      = ρ * (g : ℚ) ^ 2 := by
  have hnum_nonneg : 0 ≤ ρ.num := Rat.num_nonneg.mpr hρ

  have hnum_toNat :
      (ρ.num.toNat : ℚ) = (ρ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum_nonneg

  calc
    (((ρ.num.toNat * g ^ 2 : ℕ) : ℚ) / (ρ.den : ℚ))
        = ((ρ.num.toNat : ℚ) * (g : ℚ) ^ 2) / (ρ.den : ℚ) := by
          push_cast
          ring
    _ = ((ρ.num : ℚ) * (g : ℚ) ^ 2) / (ρ.den : ℚ) := by
          rw [hnum_toNat]
    _ = ((ρ.num : ℚ) / (ρ.den : ℚ)) * (g : ℚ) ^ 2 := by
          ring
    _ = ρ * (g : ℚ) ^ 2 := by
          rw [Rat.num_div_den ρ]

/--
The integer quotient is at most the corresponding rational quotient.

For natural numbers A and d > 0,

  [A / d] <= A / d.
-/
private lemma nat_div_cast_le (A d : ℕ) (hd : 0 < d) :
    ((A / d : ℕ) : ℚ) ≤ (A : ℚ) / (d : ℚ) := by
  have hdQ : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast hd

  have hmul_nat :
      (A / d) * d ≤ A := by
    exact Nat.div_mul_le_self A d

  have hmul_rat :
      (((A / d) * d : ℕ) : ℚ) ≤ (A : ℚ) := by
    exact_mod_cast hmul_nat

  have hmul_rat' :
      ((A / d : ℕ) : ℚ) * (d : ℚ) ≤ (A : ℚ) := by
    simpa [Nat.cast_mul] using hmul_rat

  exact (le_div_iff₀ hdQ).mpr hmul_rat'

/--
A rational quotient is strictly below one plus its integer quotient.

For natural numbers A and d > 0,

  A / d < [A / d] + 1.
-/
private lemma rat_lt_nat_div_succ (A d : ℕ) (hd : 0 < d) :
    (A : ℚ) / (d : ℚ) < ((A / d + 1 : ℕ) : ℚ) := by
  have hdQ : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast hd

  have hdiv_lt :
      A / d < A / d + 1 := by
    exact Nat.lt_succ_self (A / d)

  have hlt_nat' :
      A < (A / d + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).mp hdiv_lt

  have hlt_rat :
      (A : ℚ) < ((A / d + 1 : ℕ) : ℚ) * (d : ℚ) := by
    exact_mod_cast hlt_nat'

  exact (div_lt_iff₀ hdQ).mpr hlt_rat

/--
The lower square-root approximation is nonnegative.

For g > 0,

  0 <= sqrtLB(ρ,g).

This holds because the numerator is a natural number and the denominator is
positive.
-/
private lemma sqrtLB_nonneg {ρ : ℚ} {g : ℕ} (hg : 0 < g) :
    0 ≤ sqrtLB ρ g := by
  have hgQ : (0 : ℚ) ≤ (g : ℚ) := by
    exact_mod_cast Nat.le_of_lt hg

  have hsqrt_nonneg :
      (0 : ℚ) ≤ (isqrtScaled ρ g : ℚ) := by
    exact_mod_cast Nat.zero_le (isqrtScaled ρ g)

  unfold sqrtLB
  exact div_nonneg hsqrt_nonneg hgQ

/--
The upper square-root approximation is nonnegative.

For g > 0,

  0 <= sqrtUB(ρ,g).

This holds because the numerator is positive and the denominator is positive.
-/
private lemma sqrtUB_nonneg {ρ : ℚ} {g : ℕ} (hg : 0 < g) :
    0 ≤ sqrtUB ρ g := by
  have hgQ : (0 : ℚ) ≤ (g : ℚ) := by
    exact_mod_cast Nat.le_of_lt hg

  have hsqrt_nonneg :
      (0 : ℚ) ≤ (isqrtScaled ρ g : ℚ) := by
    exact_mod_cast Nat.zero_le (isqrtScaled ρ g)

  have hsqrt_succ_nonneg :
      (0 : ℚ) ≤ (isqrtScaled ρ g : ℚ) + 1 := by
    linarith

  unfold sqrtUB
  exact div_nonneg hsqrt_succ_nonneg hgQ

/--
sqrtLB is a lower bound on the real square root.

For every rational ρ >= 0 and every granularity g > 0,

  sqrtLB(ρ,g) <= √ρ.

Equivalently, the integer floor approximation never overshoots the true square
root.
-/
theorem sqrtLB_le {ρ : ℚ} (hρ : 0 ≤ ρ) {g : ℕ} (hg : 0 < g) :
    (sqrtLB ρ g : ℝ) ≤ Real.sqrt (ρ : ℝ) := by
  let A : ℕ := ρ.num.toNat * g ^ 2
  let N : ℕ := A / ρ.den

  have hden_pos : 0 < ρ.den := ρ.pos

  have hfloor_le :
      (N : ℚ) ≤ (A : ℚ) / (ρ.den : ℚ) := by
    dsimp [N]
    exact nat_div_cast_le A ρ.den hden_pos

  have hscale :
      (A : ℚ) / (ρ.den : ℚ) = ρ * (g : ℚ) ^ 2 := by
    dsimp [A]
    exact scaled_num_div_den_eq hρ g

  have hsqrt_nat :
      (isqrtScaled ρ g) ^ 2 ≤ N := by
    simpa [isqrtScaled, A, N] using Nat.sqrt_le' N

  have hsqrt_rat :
      ((isqrtScaled ρ g : ℚ) ^ 2) ≤ (N : ℚ) := by
    exact_mod_cast hsqrt_nat

  have hnum :
      ((isqrtScaled ρ g : ℚ) ^ 2) ≤ ρ * (g : ℚ) ^ 2 := by
    calc
      ((isqrtScaled ρ g : ℚ) ^ 2)
          ≤ (N : ℚ) := hsqrt_rat
      _ ≤ (A : ℚ) / (ρ.den : ℚ) := hfloor_le
      _ = ρ * (g : ℚ) ^ 2 := hscale

  have hgQ_pos : (0 : ℚ) < (g : ℚ) := by
    exact_mod_cast hg

  have hgQ_ne : (g : ℚ) ≠ 0 := by
    exact ne_of_gt hgQ_pos

  have hcertQ :
      (sqrtLB ρ g) ^ 2 ≤ ρ := by
    unfold sqrtLB
    calc
      (((isqrtScaled ρ g : ℚ) / (g : ℚ)) ^ 2)
          = ((isqrtScaled ρ g : ℚ) ^ 2) / (g : ℚ) ^ 2 := by
            rw [div_pow]
      _ ≤ (ρ * (g : ℚ) ^ 2) / (g : ℚ) ^ 2 := by
            exact div_le_div_of_nonneg_right hnum (sq_nonneg (g : ℚ))
      _ = ρ := by
            field_simp [hgQ_ne]

  have hcertR :
      ((sqrtLB ρ g : ℝ) ^ 2) ≤ (ρ : ℝ) := by
    exact_mod_cast hcertQ

  have hlo_nonnegR :
      (0 : ℝ) ≤ (sqrtLB ρ g : ℝ) := by
    exact_mod_cast sqrtLB_nonneg (ρ := ρ) hg

  calc
    (sqrtLB ρ g : ℝ)
        = Real.sqrt ((sqrtLB ρ g : ℝ) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hlo_nonnegR]
    _ ≤ Real.sqrt (ρ : ℝ) := by
          exact Real.sqrt_le_sqrt hcertR

/--
sqrtUB is an upper bound on the real square root.

For every rational ρ >= 0 and every granularity g > 0,

  √ρ <= sqrtUB(ρ,g).

Equivalently, adding one unit after the integer floor gives an approximation
that never lies below the true square root.
-/
theorem le_sqrtUB {ρ : ℚ} (hρ : 0 ≤ ρ) {g : ℕ} (hg : 0 < g) :
    Real.sqrt (ρ : ℝ) ≤ (sqrtUB ρ g : ℝ) := by
  let A : ℕ := ρ.num.toNat * g ^ 2
  let N : ℕ := A / ρ.den

  have hden_pos : 0 < ρ.den := ρ.pos

  have hfloor_lt :
      (A : ℚ) / (ρ.den : ℚ) < ((N + 1 : ℕ) : ℚ) := by
    dsimp [N]
    simpa [Nat.add_comm] using rat_lt_nat_div_succ A ρ.den hden_pos

  have hscale :
      (A : ℚ) / (ρ.den : ℚ) = ρ * (g : ℚ) ^ 2 := by
    dsimp [A]
    exact scaled_num_div_den_eq hρ g

  have hsqrt_succ_nat :
      N + 1 ≤ (isqrtScaled ρ g + 1) * (isqrtScaled ρ g + 1) := by
    have hlt :
        N <
          (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N

    have hle :
        N + 1 ≤ (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
      exact Nat.succ_le_of_lt hlt

    simpa [isqrtScaled, A, N] using hle

  have hsqrt_succ_rat :
      ((N + 1 : ℕ) : ℚ)
        ≤ ((isqrtScaled ρ g : ℚ) + 1) *
          ((isqrtScaled ρ g : ℚ) + 1) := by
    exact_mod_cast hsqrt_succ_nat

  have hnum :
      ρ * (g : ℚ) ^ 2
        ≤ ((isqrtScaled ρ g : ℚ) + 1) *
          ((isqrtScaled ρ g : ℚ) + 1) := by
    calc
      ρ * (g : ℚ) ^ 2
          = (A : ℚ) / (ρ.den : ℚ) := hscale.symm
      _ ≤ ((N + 1 : ℕ) : ℚ) := le_of_lt hfloor_lt
      _ ≤ ((isqrtScaled ρ g : ℚ) + 1) *
            ((isqrtScaled ρ g : ℚ) + 1) := hsqrt_succ_rat

  have hgQ_pos : (0 : ℚ) < (g : ℚ) := by
    exact_mod_cast hg

  have hgQ_ne : (g : ℚ) ≠ 0 := by
    exact ne_of_gt hgQ_pos

  have hcertQ :
      ρ ≤ (sqrtUB ρ g) ^ 2 := by
    unfold sqrtUB
    calc
      ρ = (ρ * (g : ℚ) ^ 2) / (g : ℚ) ^ 2 := by
            field_simp [hgQ_ne]
      _ ≤ (((isqrtScaled ρ g : ℚ) + 1) *
              ((isqrtScaled ρ g : ℚ) + 1)) / (g : ℚ) ^ 2 := by
            exact div_le_div_of_nonneg_right hnum (sq_nonneg (g : ℚ))
      _ = (((isqrtScaled ρ g : ℚ) + 1) / (g : ℚ)) ^ 2 := by
            ring_nf

  have hcertR :
      (ρ : ℝ) ≤ ((sqrtUB ρ g : ℝ) ^ 2) := by
    exact_mod_cast hcertQ

  have hhi_nonnegR :
      (0 : ℝ) ≤ (sqrtUB ρ g : ℝ) := by
    exact_mod_cast sqrtUB_nonneg (ρ := ρ) hg

  calc
    Real.sqrt (ρ : ℝ)
        ≤ Real.sqrt ((sqrtUB ρ g : ℝ) ^ 2) := by
          exact Real.sqrt_le_sqrt hcertR
    _ = (sqrtUB ρ g : ℝ) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hhi_nonnegR]

/--
The distance between the upper and lower rational approximations is exactly one
granularity unit.

For every g > 0,

  sqrtUB(ρ,g) - sqrtLB(ρ,g) = 1 / g.

Thus increasing g makes the enclosing interval narrower.
-/
theorem sqrtUB_sub_sqrtLB {ρ : ℚ} {g : ℕ} (hg : 0 < g) :
    sqrtUB ρ g - sqrtLB ρ g = 1 / g := by
  unfold sqrtUB sqrtLB
  field_simp
  ring

/-! ## A1 exit criterion

These examples are the "hello world" certificate check: the bounds `sqrtLB` and
`sqrtUB` each satisfy the pure rational inequality that witnesses they bracket √(1/2).
Both are discharged by `native_decide` (kernel-evaluated on concrete `ℕ`/`ℚ` values).
-/

/-- Lower-bound certificate: `(sqrtLB (1/2) (2^40))² ≤ 1/2`. -/
example : sqrtLB (1 / 2) (2 ^ 40) ^ 2 ≤ 1 / 2 := by native_decide

/-- Upper-bound certificate: `1/2 ≤ (sqrtUB (1/2) (2^40))²`. -/
example : 1 / 2 ≤ sqrtUB (1 / 2) (2 ^ 40) ^ 2 := by native_decide

end Soundcalc
