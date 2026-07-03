import Mathlib

namespace Soundcalc

/-- A pair of directed rational bounds on a square root. -/
structure SqrtBounds where
  lo : ℚ
  hi : ℚ
deriving Repr, DecidableEq

namespace SqrtBounds

/-- Bounds on √n (n : ℕ) at width 1/prec, computed via `Nat.sqrt` — no per-instance
    certificates needed. -/
def ofNat (n prec : ℕ) : SqrtBounds where
  lo := (Nat.sqrt (n * prec ^ 2) : ℚ) / prec
  hi := ((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) / prec

/-- Bounds on √q (q : ℚ, q ≥ 0) via √(a/b) = √(a·b)/b. -/
def ofRat (q : ℚ) (prec : ℕ) : SqrtBounds :=
  let s := ofNat (q.num.toNat * q.den) prec
  ⟨s.lo / q.den, s.hi / q.den⟩

/-! ### Key rational identity -/

/--
For a nonnegative rational \(q = a/b\) with \(a \ge 0\) and \(b > 0\),
the integer numerator can be viewed as a natural number. The lemma proves

\[
    a b = a/b * b^2,
\]

This lets us reduce a rational square-root bound to a natural-number one.
-/
private lemma num_toNat_mul_den_eq {q : ℚ} (hq : 0 ≤ q) :
    (q.num.toNat : ℚ) * q.den = q * q.den ^ 2 := by
  have hnum_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq

  have hnum_toNat :
      (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum_nonneg

  have hden_ne : (q.den : ℚ) ≠ 0 := by
    exact_mod_cast q.pos.ne'

  calc
    (q.num.toNat : ℚ) * q.den
        = (q.num : ℚ) * q.den := by
          rw [hnum_toNat]
    _ = ((q.num : ℚ) / q.den) * q.den ^ 2 := by
          field_simp [hden_ne]
    _ = q * q.den ^ 2 := by
          rw [Rat.num_div_den q]


/-! ### ofNat theorems — proved once from `Nat.sqrt_le'` / `Nat.lt_succ_sqrt` -/

/--
Let \(m = [\sqrt{n * prec^2}]\). Since
\(m^2 <= n * prec^2\), we have

\[
    (m / prec)^2 \le n.
\]
-/
theorem ofNat_lo_sq_le (n : ℕ) {prec : ℕ} (hp : 0 < prec) :
    (ofNat n prec).lo ^ 2 ≤ n := by
  have hprec_pos : (0 : ℚ) < (prec : ℚ) := by
    exact_mod_cast hp

  have hprec_ne : (prec : ℚ) ≠ 0 := by
    exact ne_of_gt hprec_pos

  have hsqrt_nat :
      (Nat.sqrt (n * prec ^ 2)) ^ 2 ≤ n * prec ^ 2 := by
    exact Nat.sqrt_le' (n * prec ^ 2)

  have hsqrt_rat :
      ((Nat.sqrt (n * prec ^ 2) : ℚ) ^ 2)
        ≤ (n : ℚ) * (prec : ℚ) ^ 2 := by
    exact_mod_cast hsqrt_nat

  calc
    (ofNat n prec).lo ^ 2
        = ((Nat.sqrt (n * prec ^ 2) : ℚ) / (prec : ℚ)) ^ 2 := by
          rfl
    _ = ((Nat.sqrt (n * prec ^ 2) : ℚ) ^ 2) / (prec : ℚ) ^ 2 := by
          rw [div_pow]
    _ ≤ ((n : ℚ) * (prec : ℚ) ^ 2) / (prec : ℚ) ^ 2 := by
          exact div_le_div_of_nonneg_right hsqrt_rat (sq_nonneg (prec : ℚ))
    _ = n := by
          field_simp [hprec_ne]

/--
Let \(m = [\sqrt{n * prec^2}]\). Since
\(n * prec^2 < (m + 1)^2\), we have

\[
    n \le ((m + 1) / prec)^2.
\]
-/theorem ofNat_le_hi_sq (n : ℕ) {prec : ℕ} (hp : 0 < prec) :
    (n : ℚ) ≤ (ofNat n prec).hi ^ 2 := by
  have hprec_pos : (0 : ℚ) < (prec : ℚ) := by
    exact_mod_cast hp

  have hprec_ne : (prec : ℚ) ≠ 0 := by
    exact ne_of_gt hprec_pos

  have hsqrt_nat :
      n * prec ^ 2 <
        (Nat.sqrt (n * prec ^ 2) + 1) *
          (Nat.sqrt (n * prec ^ 2) + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (n * prec ^ 2)

  have hsqrt_rat :
      (n : ℚ) * (prec : ℚ) ^ 2
        ≤ (((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) *
            ((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ)) := by
    exact_mod_cast le_of_lt hsqrt_nat

  show
      (n : ℚ) ≤
        (((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) / (prec : ℚ)) ^ 2

  calc
    (n : ℚ)
        = ((n : ℚ) * (prec : ℚ) ^ 2) / (prec : ℚ) ^ 2 := by
          field_simp [hprec_ne]
    _ ≤ ((((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) *
            ((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ))
            / (prec : ℚ) ^ 2) := by
          exact div_le_div_of_nonneg_right hsqrt_rat (sq_nonneg (prec : ℚ))
    _ = (((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) / (prec : ℚ)) ^ 2 := by
          ring_nf

/-! ### ofRat theorems — sandwich Real.sqrt between lo and hi -/

private lemma ofNat_lo_nonneg (n : ℕ) {prec : ℕ} (hp : 0 < prec) :
    0 ≤ (ofNat n prec).lo := by
  have hprec_pos : (0 : ℚ) < (prec : ℚ) := by
    exact_mod_cast hp

  have hsqrt_nonneg :
      (0 : ℚ) ≤ (Nat.sqrt (n * prec ^ 2) : ℚ) := by
    exact_mod_cast Nat.zero_le (Nat.sqrt (n * prec ^ 2))

  change 0 ≤ (Nat.sqrt (n * prec ^ 2) : ℚ) / (prec : ℚ)
  exact div_nonneg hsqrt_nonneg (le_of_lt hprec_pos)


private lemma ofNat_hi_nonneg (n : ℕ) {prec : ℕ} (hp : 0 < prec) :
    0 ≤ (ofNat n prec).hi := by
  have hprec_pos : (0 : ℚ) < (prec : ℚ) := by
    exact_mod_cast hp

  have hsqrt_succ_nonneg :
      (0 : ℚ) ≤ ((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.zero_le (Nat.sqrt (n * prec ^ 2) + 1)

  change 0 ≤ (((Nat.sqrt (n * prec ^ 2) + 1 : ℕ) : ℚ) / (prec : ℚ))
  exact div_nonneg hsqrt_succ_nonneg (le_of_lt hprec_pos)


/-- lo (as a real) is at most √q. -/
theorem ofRat_lo_le_sqrt {q : ℚ} (hq : 0 ≤ q) {prec : ℕ} (hp : 0 < prec) :
    ((ofRat q prec).lo : ℝ) ≤ Real.sqrt q := by
  let N : ℕ := q.num.toNat * q.den

  have hden_posQ : (0 : ℚ) < (q.den : ℚ) := by
    exact_mod_cast q.pos

  have hden_neQ : (q.den : ℚ) ≠ 0 := by
    exact ne_of_gt hden_posQ

  have hN_eq : (N : ℚ) = q * (q.den : ℚ) ^ 2 := by
    dsimp [N]
    simpa [Nat.cast_mul] using num_toNat_mul_den_eq hq

  have hlo_nat :
      (ofNat N prec).lo ^ 2 ≤ (N : ℚ) := by
    simpa using ofNat_lo_sq_le N hp

  have hlo_sqQ :
      (ofRat q prec).lo ^ 2 ≤ q := by
    change ((ofNat N prec).lo / (q.den : ℚ)) ^ 2 ≤ q

    calc
      ((ofNat N prec).lo / (q.den : ℚ)) ^ 2
          = (ofNat N prec).lo ^ 2 / (q.den : ℚ) ^ 2 := by
            rw [div_pow]
      _ ≤ (N : ℚ) / (q.den : ℚ) ^ 2 := by
            exact div_le_div_of_nonneg_right hlo_nat (sq_nonneg (q.den : ℚ))
      _ = q := by
            rw [hN_eq]
            field_simp [hden_neQ]

  have hlo_sqR :
      (((ofRat q prec).lo : ℝ) ^ 2) ≤ (q : ℝ) := by
    exact_mod_cast hlo_sqQ

  have hlo_nonnegQ :
      (0 : ℚ) ≤ (ofRat q prec).lo := by
    change (0 : ℚ) ≤ (ofNat N prec).lo / (q.den : ℚ)
    exact div_nonneg (ofNat_lo_nonneg N hp) (le_of_lt hden_posQ)

  have hlo_nonnegR :
      (0 : ℝ) ≤ ((ofRat q prec).lo : ℝ) := by
    exact_mod_cast hlo_nonnegQ

  calc
    ((ofRat q prec).lo : ℝ)
        = Real.sqrt (((ofRat q prec).lo : ℝ) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hlo_nonnegR]
    _ ≤ Real.sqrt (q : ℝ) := by
          exact Real.sqrt_le_sqrt hlo_sqR


/-- √q is at most hi (as a real). -/
theorem ofRat_sqrt_le_hi {q : ℚ} (hq : 0 ≤ q) {prec : ℕ} (hp : 0 < prec) :
    Real.sqrt q ≤ ((ofRat q prec).hi : ℝ) := by
  let N : ℕ := q.num.toNat * q.den

  have hden_posQ : (0 : ℚ) < (q.den : ℚ) := by
    exact_mod_cast q.pos

  have hden_neQ : (q.den : ℚ) ≠ 0 := by
    exact ne_of_gt hden_posQ

  have hN_eq : (N : ℚ) = q * (q.den : ℚ) ^ 2 := by
    dsimp [N]
    simpa [Nat.cast_mul] using num_toNat_mul_den_eq hq

  have hhi_nat :
      (N : ℚ) ≤ (ofNat N prec).hi ^ 2 := by
    simpa using ofNat_le_hi_sq N hp

  have hhi_sqQ :
      q ≤ (ofRat q prec).hi ^ 2 := by
    change q ≤ ((ofNat N prec).hi / (q.den : ℚ)) ^ 2

    calc
      q = (N : ℚ) / (q.den : ℚ) ^ 2 := by
            rw [hN_eq]
            field_simp [hden_neQ]
      _ ≤ (ofNat N prec).hi ^ 2 / (q.den : ℚ) ^ 2 := by
            exact div_le_div_of_nonneg_right hhi_nat (sq_nonneg (q.den : ℚ))
      _ = ((ofNat N prec).hi / (q.den : ℚ)) ^ 2 := by
            rw [div_pow]

  have hhi_sqR :
      (q : ℝ) ≤ (((ofRat q prec).hi : ℝ) ^ 2) := by
    exact_mod_cast hhi_sqQ

  have hhi_nonnegQ :
      (0 : ℚ) ≤ (ofRat q prec).hi := by
    change (0 : ℚ) ≤ (ofNat N prec).hi / (q.den : ℚ)
    exact div_nonneg (ofNat_hi_nonneg N hp) (le_of_lt hden_posQ)

  have hhi_nonnegR :
      (0 : ℝ) ≤ ((ofRat q prec).hi : ℝ) := by
    exact_mod_cast hhi_nonnegQ

  calc
    Real.sqrt (q : ℝ)
        ≤ Real.sqrt (((ofRat q prec).hi : ℝ) ^ 2) := by
          exact Real.sqrt_le_sqrt hhi_sqR
    _ = ((ofRat q prec).hi : ℝ) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hhi_nonnegR]

/-- The interval width is 1/(q.den · prec). -/
theorem ofRat_width (q : ℚ) (prec : ℕ) :
    (ofRat q prec).hi - (ofRat q prec).lo = 1 / (q.den * prec) := by
  simp only [ofRat, ofNat]
  push_cast
  ring

/-! ### Examples — ρ = 1/2, prec = 5000

`Nat.sqrt (1 · 2 · 5000²) = Nat.sqrt 50_000_000 = 7071`
because  `7071² = 49_999_041 ≤ 50_000_000 < 50_013_184 = 7072²`.

So `(ofRat (1/2) 5000).lo = 7071/5000/2 = 7071/10000` and
   `(ofRat (1/2) 5000).hi = 7072/5000/2 = 7072/10000`, width `10⁻⁴`.
Kernel cost is negligible: `Nat.sqrt` unfolds to O(log n) GMP-accelerated
divisions and the projections reduce past the record with no friction. -/

example : Nat.sqrt (2 * 5000 ^ 2) = 7071 := by native_decide

example : (ofRat (1/2 : ℚ) 5000).lo = 7071 / 10000 := by native_decide
example : (ofRat (1/2 : ℚ) 5000).hi = 7072 / 10000 := by native_decide

-- Width follows analytically from `ofRat_width`; no `native_decide` needed.
example : (ofRat (1/2 : ℚ) 5000).hi - (ofRat (1/2 : ℚ) 5000).lo = 1 / 10000 := by
  rw [ofRat_width]; norm_num

end SqrtBounds
end Soundcalc
