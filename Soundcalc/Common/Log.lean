import Mathlib

/-!
# `Soundcalc.Common.Log` — rational upper bound for log₂ with certified enclosure

Provides `log2UB`, a rational dyadic over-approximation of `Real.logb 2`, together
with the theorems bounding the approximation error.  Used by `Soundcalc.Lookup` for
the GKR and LogUp soundness error formulas.
-/

namespace Soundcalc

/-- A rational approximation for `log_2 x` at dyadic granularity `m`
    (e.g. `m = 64` overstates by `< 2^(-6)`); certificate is
    `2^(Nat.clog 2 (x^m) - 1) < x^m ≤ 2^(Nat.clog 2 (x^m))`
    (proved in `log2UB_approx_bound`)
-/
def log2UB (x m : ℕ) : ℚ := (Nat.clog 2 (x^m) : ℚ) / m

/-- `log_2 x ≤ c/m` reduces to the integer inequality `x^m ≤ 2^c`.
    Human-stated theorem; AI-assisted proof and comments. -/
theorem logb_le_div {x m c : ℕ}
  (hm : 0 < m)
  (hc : 1 ≤ c)
  (h : x ^ m ≤ 2 ^ c) :
  Real.logb 2 x ≤ (c : ℝ) / m := by
have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
rcases Nat.eq_zero_or_pos x with hx0 | hxpos
· subst hx0
  simp only [Nat.cast_zero, Real.logb_zero]
  positivity
· have hcertR : (x:ℝ) ^ m ≤ (2:ℝ) ^ c := by exact_mod_cast h
  have hstep : Real.logb 2 ((x:ℝ) ^ m) ≤ Real.logb 2 ((2:ℝ) ^ c) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hcertR
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hstep
  rw [le_div_iff₀ hmR, mul_comm]
  exact_mod_cast hstep

/-- `(c-1)/m < log_2 x` reduces to the integer inequality `2^(c-1) < x^m`.
    Human-stated theorem; AI-assisted proof and comments. -/
theorem div_lt_logb {x m c : ℕ}
    (hm : 0 < m)
    (hc : 1 ≤ c)
    (h  : 2 ^ (c - 1) < x ^ m) :
    ((c : ℝ) - 1) / m < Real.logb 2 x := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hxpos : 0 < x := by
    by_contra hx0
    push Not at hx0
    interval_cases x
    simp only [zero_pow hm.ne'] at h
    exact absurd h (Nat.not_succ_le_zero _)
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    push_cast [Nat.cast_sub hc]
    simp
  have hcertR : (2:ℝ) ^ (c - 1 : ℕ) < (x:ℝ) ^ m := by exact_mod_cast h
  have hstep : Real.logb 2 ((2:ℝ) ^ (c - 1 : ℕ)) < Real.logb 2 ((x:ℝ) ^ m) :=
    Real.logb_lt_logb (by norm_num) (by positivity) hcertR
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hstep
  rw [Real.logb_pow] at hstep
  rw [hcast] at hstep
  rw [div_lt_iff₀ hmR, mul_comm]
  linarith

/-!
Assuming `x^m ≤ 2^c`, `2^(c-1) < x^m`, `c ≥ 1`, `m > 0`, the above theorems give:

- `c/m` upper-bounds `log_2 x`
- `(c-1)/m` lower-bounds `log_2 x` (tightly).

Hence `c/m` is at most `1/m` from the real logarithm.

We first cast these results to `c = Nat.clog 2 (x^m)`, establishing:
- `x^m ≤ 2^{clog2(x^m)}`                       [Trivially verified]
- `2^{clog2(x^m) - 1} < x^m`                   [Verified when `x^m > 1`]
- `Nat.clog 2 (x^m) ≥ 1`                       [Verified when `x^m > 1`]
-/

private theorem clog2_hceil {x m : ℕ} :
  x^m ≤ 2^(Nat.clog 2 (x^m)) := by
  refine Nat.le_pow_clog ?_ (x ^ m)
  linarith

private theorem clog2_hfloor {x m : ℕ} (hxm : 1 < x^m) :
  2^(Nat.clog 2 (x^m) - 1) < x^m :=
  Nat.pow_pred_clog_lt_self (by norm_num) hxm

private theorem clog2_hc {x m : ℕ} (hxm : 1 < x^m) :
  Nat.clog 2 (x^m) ≥ 1 :=
  Nat.clog_pos (by norm_num) hxm

private theorem clog2_upper_bound {x m : ℕ} (hxm : 1 < x^m) (hm : 0 < m) :
  Real.logb 2 x ≤ ((Nat.clog 2 (x^m)) : ℝ) / m := by
  apply logb_le_div hm (clog2_hc hxm) clog2_hceil

private theorem clog2_lower_bound {x m : ℕ} (hxm : 1 < x^m) (hm : 0 < m) :
  (((Nat.clog 2 (x^m)) - 1) : ℝ) / m < Real.logb 2 x := by
  apply div_lt_logb hm (clog2_hc hxm) (clog2_hfloor hxm)

/-- `log2UB x m` upper-bounds `Real.logb 2 x`. -/
theorem log2UB_upper_bound {x m : ℕ} (hxm : 1 < x^m) (hm : 0 < m) :
  Real.logb 2 x ≤ log2UB x m := by
  unfold log2UB; push_cast
  apply clog2_upper_bound hxm hm

/-- `log2UB x m - 1/m` lower-bounds `Real.logb 2 x`. -/
theorem log2UB_lower_bound {x m : ℕ} (hxm : 1 < x^m) (hm : 0 < m) :
  (log2UB x m) - (1 : ℚ) / m < Real.logb 2 x := by
  unfold log2UB; push_cast
  have hdiv : ((Nat.clog 2 (x ^ m) : ℝ) - 1) / m =
      (Nat.clog 2 (x ^ m) : ℝ) / m - 1 / m := by ring
  rw [← hdiv]
  apply clog2_lower_bound hxm hm

/-- Combined: `log2UB x m - 1/m < Real.logb 2 x ≤ log2UB x m`. -/
theorem log2UB_approx_bound {x m : ℕ} (hxm : 1 < x^m) (hm : 0 < m) :
  (log2UB x m) - (1 : ℚ) / m < Real.logb 2 x ∧ Real.logb 2 x ≤ log2UB x m :=
  ⟨log2UB_lower_bound hxm hm, log2UB_upper_bound hxm hm⟩

end Soundcalc
