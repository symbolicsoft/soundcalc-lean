import Mathlib

/-!
# secBits, and one cell of `reports/sp1.md`

Milestone M0 seed. This `secBits` handles only the shapes the example needs;
the library version will be total, specified by `le_secBits_iff`, and proved
against it.

## Shared proof strategy (read this once)

A rational `ε` is stored as `num/den` in lowest terms with `den > 0`, so
`1/ε = den/num` and, on the `else` branch,

    secBits ε = log₂ ⌊den/num⌋        (ℕ `/` is floor division; `.log2` is ⌊log₂⌋)

Reasoning about `log₂` and floor-division *in place* is painful, so none of the
proofs below do that. Instead each one pushes BOTH the hypothesis and the goal
down to a single clean integer inequality

    num * 2^k ≤ den            (equivalently:  ε ≤ 1 / 2^k)

and uses `exact_mod_cast` to move that fact between ℕ, ℤ and ℚ. Recognising this
"funnel to a common integer statement" pattern makes all four lemmas read the
same way:

* `le_secBits_if` : `k ≤ secBits ε → ε ≤ 1/2^k`   — soundness (never over-promises)
* `secBits_ge`    : `ε ≤ 1/2^k → k ≤ secBits ε`   — completeness (the converse)
* `secBits_anti`  : `a ≤ b → secBits b ≤ secBits a` — smaller error ⇒ more bits
* `secBits_min'`  : `secBits (min a b) = max (..) (..)` — pure order theory

A quick tactic glossary used throughout:
* `intro h`         — move a hypothesis of a `→` goal into context, naming it `h`.
* `have h : T := e` — prove a side fact `T` and name it `h` (`:= by ...` for a proof).
* `rw [l]`          — rewrite the goal left-to-right using equality/iff `l`
                      (`rw [← l]` rewrites right-to-left; `... at h` rewrites in `h`).
* `rwa [...]`       — `rw [...]` then close the goal with `assumption`.
* `exact_mod_cast`  — like `exact`, but inserts/removes ℕ↔ℤ↔ℚ coercions automatically.
* `omega`           — decision procedure for linear arithmetic over ℕ/ℤ.
* `positivity`      — proves `0 < e` / `0 ≤ e` goals automatically.
* `nlinarith`       — nonlinear arithmetic: closes a goal from given product/inequality hints.
-/

namespace Soundcalc

/-- Bits of security of a rational error: the largest `k` with `ε ≤ 2 ^ (-k)`.
For `0 < ε ≤ 1` this is `⌊log₂ (1 / ε)⌋`, computed on numerator/denominator. -/
def secBits (ε : ℚ) : ℕ :=
  -- A nonpositive "error" is meaningless here, so report 0 bits.
  if ε ≤ 0 then 0
  -- Else: 1/ε = den/num, so ⌊log₂(1/ε)⌋ = log₂ of the ℕ-floor ⌊den/num⌋.
  else (ε.den / ε.num.toNat).log2


/-- **Soundness direction.** If `secBits` claims at least `k` bits, then `ε` really
is at most `2^(-k)`. (One half of the eventual `iff`; the floor losing precision
is harmless in this direction.) -/
theorem le_secBits_if (ε : ℚ) (hε : ε > 0) (hε1 : ε ≤ 1) (k : ℕ) :
    k ≤ secBits ε → ε ≤ 1 / 2 ^ k := by
  -- Peel the `→`: assume `hk : k ≤ secBits ε`, leaving goal `ε ≤ 1 / 2^k`.
  intro hk
  -- Replace `secBits ε` by its `else` branch. `not_le.mpr hε : ¬ (ε ≤ 0)`
  -- lets `if_neg` discard the `then` branch; `rwa` then closes by `assumption`.
  have hk' : k ≤ (ε.den / ε.num.toNat).log2 := by
    unfold secBits at hk
    rwa [if_neg (not_le.mpr hε)] at hk
  -- ── positivity bookkeeping (needed to make later steps legal) ──
  -- `Rat.num_pos : 0 < q.num ↔ 0 < q`; `.mpr hε` gives a positive numerator (in ℤ).
  have hnum_pos : 0 < ε.num := Rat.num_pos.mpr hε
  -- num > 0 in ℤ ⇒ num.toNat > 0 in ℕ; `omega` knows this.
  have hp_pos : 0 < ε.num.toNat := by omega
  -- Denominators of rationals are always positive (built-in fact).
  have hq_pos : 0 < ε.den := ε.den_pos
  -- ε ≤ 1  ⇒  num ≤ den, transported all the way down to ℕ.
  have hpq : ε.num.toNat ≤ ε.den := by
    have hden : (0 : ℚ) < (ε.den : ℚ) := by exact_mod_cast hq_pos
    -- Rewrite the goal `num ≤ den` BACKWARDS through `div_le_one` (a/b ≤ 1 ↔ a ≤ b)
    -- to get `num/den ≤ 1`, then `Rat.num_div_den` turns `num/den` into `ε`.
    have hle : (ε.num : ℚ) ≤ (ε.den : ℚ) := by
      rw [← div_le_one hden, Rat.num_div_den]; exact hε1
    have : ε.num ≤ (ε.den : ℤ) := by exact_mod_cast hle
    omega
  -- ⌊den/num⌋ ≠ 0 (it's positive), the side condition `Nat.le_log2` requires.
  have hm : ε.den / ε.num.toNat ≠ 0 := (Nat.div_pos hpq hp_pos).ne'
  -- Strip the log₂: `Nat.le_log2 hm : k ≤ n.log2 ↔ 2^k ≤ n`; `.mp` is the forward dir.
  have h1 : 2 ^ k ≤ ε.den / ε.num.toNat := (Nat.le_log2 hm).mp hk'
  -- ── the crux: clear the floor division to get  num * 2^k ≤ den  (in ℕ) ──
  -- A `calc` chain: each line's RHS is the next line's LHS.
  have h2 : ε.num.toNat * 2 ^ k ≤ ε.den :=
    calc ε.num.toNat * 2 ^ k
        -- multiply `h1` on the left by num
        ≤ ε.num.toNat * (ε.den / ε.num.toNat) := mul_le_mul_left' h1 _
        -- commute the product
      _ = (ε.den / ε.num.toNat) * ε.num.toNat := Nat.mul_comm _ _
        -- standard floor fact: ⌊a/b⌋ * b ≤ a
      _ ≤ ε.den := Nat.div_mul_le_self _ _
  -- Lift `h2` from ℕ to ℤ. `exact_mod_cast` inserts the coercions; then
  -- `Int.toNat_of_nonneg` ((a.toNat : ℤ) = a for a ≥ 0) cleans `↑num.toNat` to `num`.
  have h2' : ε.num * 2 ^ k ≤ (ε.den : ℤ) := by
    have h : (ε.num.toNat : ℤ) * 2 ^ k ≤ (ε.den : ℤ) := by exact_mod_cast h2
    rwa [Int.toNat_of_nonneg hnum_pos.le] at h
  -- ── finish: rewrite the GOAL `ε ≤ 1/2^k` down to match `h2'` ──
  --   le_div_iff₀ (0<2^k) : a ≤ b/c ↔ a*c ≤ b      ⇒  ε * 2^k ≤ 1
  --   ← Rat.num_div_den ε : replace ε by num/den   ⇒  (num/den) * 2^k ≤ 1
  --   div_mul_eq_mul_div  : (a/b)*c = (a*c)/b       ⇒  (num*2^k)/den ≤ 1
  --   div_le_one (0<den)  : a/b ≤ 1 ↔ a ≤ b         ⇒  num*2^k ≤ den
  -- (`positivity` discharges the `0 < 2^k` side goal inline.)
  rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ k), ← Rat.num_div_den ε,
      div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq_pos)]
  -- The goal is now exactly `h2'` up to coercions.
  exact_mod_cast h2'


/-- Antitone: smaller error ⇒ at least as many bits.
Strategy: both errors are positive (so both take the `else` branch); strip the
`log₂` via its monotonicity; what's left is comparing the two floor-divisions,
which follows by cross-multiplying `a ≤ b` and combining in ℤ. -/
theorem secBits_anti {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) :
    secBits b ≤ secBits a := by
  -- Helper: `log₂` is monotone (handled separately because the `n = 0` case is special).
  have log2_mono : ∀ {p q : ℕ}, p ≤ q → p.log2 ≤ q.log2 := by
    intro p q hpq
    rcases Nat.eq_zero_or_pos p with hp | hp     -- split on p = 0 vs p > 0
    · have : Nat.log2 0 = 0 := by simp [Nat.log2]
      rw [hp, this]; exact Nat.zero_le _          -- log₂ 0 = 0 ≤ anything
    · have hq : q ≠ 0 := by omega
      rw [Nat.le_log2 hq]                         -- reduce `p.log2 ≤ q.log2` to `2^(p.log2) ≤ q`
      exact le_trans ((Nat.le_log2 hp.ne').mp le_rfl) hpq
  -- a > 0 and a ≤ b give b > 0.
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- positivity facts for both rationals (same idioms as in `le_secBits_if`)
  have han : 0 < a.num := Rat.num_pos.mpr ha
  have hbn : 0 < b.num := Rat.num_pos.mpr hb
  have had : 0 < a.den := a.den_pos
  have hbd : 0 < b.den := b.den_pos
  have hanT : 0 < a.num.toNat := by omega
  -- Both inputs positive ⇒ both `secBits` take the `else` branch.
  unfold secBits
  rw [if_neg (not_le.mpr hb), if_neg (not_le.mpr ha)]
  -- Reduce `⌊..b..⌋.log2 ≤ ⌊..a..⌋.log2` to `⌊..b..⌋ ≤ ⌊..a..⌋` (monotonicity).
  apply log2_mono
  -- `Nat.le_div_iff_mul_le hanT` turns the goal `⌊den_b/num_b⌋ ≤ den_a/num_a`
  -- into the product form `⌊den_b/num_b⌋ * num_a ≤ den_a`.
  rw [Nat.le_div_iff_mul_le hanT]
  -- Floor bound for b: ⌊den_b/num_b⌋ * num_b ≤ den_b, lifted to ℤ.
  have hb_floor : (b.den / b.num.toNat) * b.num.toNat ≤ b.den :=
    Nat.div_mul_le_self _ _
  have hbf : ((b.den / b.num.toNat : ℕ) : ℤ) * b.num ≤ b.den := by
    have h : ((b.den / b.num.toNat : ℕ) : ℤ) * (b.num.toNat : ℤ) ≤ (b.den : ℤ) := by
      exact_mod_cast hb_floor
    rwa [Int.toNat_of_nonneg hbn.le] at h
  -- Cross-multiply `a ≤ b`: num_a * den_b ≤ num_b * den_a (the `₀`-lemma family
  -- handles the positive denominators), then drop coercions to ℤ.
  have hcross : (a.num : ℤ) * b.den ≤ b.num * a.den := by
    have h := hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b,
        div_le_iff₀ (by exact_mod_cast had : (0:ℚ) < a.den),
        div_mul_eq_mul_div,
        le_div_iff₀ (by exact_mod_cast hbd : (0:ℚ) < b.den)] at h
    exact_mod_cast h
  -- Combine everything in ℤ. `nlinarith` is given the two products and the
  -- positivity facts it needs to cancel `b.num > 0` and reach the goal.
  have hM : (0:ℤ) ≤ ((b.den / b.num.toNat : ℕ) : ℤ) := by positivity
  have goalZ : ((b.den / b.num.toNat : ℕ) : ℤ) * a.num ≤ a.den := by
    nlinarith [mul_le_mul_of_nonneg_right hbf han.le, hcross, hbn, hM]
  -- Transport the ℤ result back to the ℕ goal (num_a.toNat = num_a since num_a ≥ 0).
  have hfin : ((b.den / b.num.toNat : ℕ) : ℤ) * (a.num.toNat : ℤ) ≤ (a.den : ℤ) := by
    rwa [Int.toNat_of_nonneg han.le]
  exact_mod_cast hfin


/-- "total = min over rounds": the worst (largest) per-round error
    gives the fewest bits, the min over rounds. Pure order theory.
    Since `secBits` is antitone, the smaller error `min a b` yields the larger
    bit-count `max (secBits a) (secBits b)`. -/
  theorem secBits_min' {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    secBits (min a b) = max (secBits a) (secBits b) := by
  -- Split on which of a, b is smaller; in each branch `min`/`max` collapse and
  -- `secBits_anti` supplies the inequality that picks the right `max` side.
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab,  max_eq_left  (secBits_anti ha hab)]
  · rw [min_eq_right hba, max_eq_right (secBits_anti hb hba)]


/-- **Completeness direction** (the converse of `le_secBits_if`): if `ε ≤ 2^(-k)`
then `secBits` reports at least `k` bits. Same skeleton, run backwards — and note
it does NOT need `ε ≤ 1`. (Docstring: grinding is exactly additive in bits,
matching `apply_grinding`.) -/
    theorem secBits_ge (ε : ℚ) (hε : 0 < ε) (k : ℕ) :
    ε ≤ 1 / 2 ^ k → k ≤ secBits ε := by
  intro hk
  -- positivity bookkeeping (as before)
  have hnum_pos : 0 < ε.num := Rat.num_pos.mpr hε
  have hp_pos : 0 < ε.num.toNat := by omega
  have hq_pos : 0 < ε.den := ε.den_pos
  -- Turn the hypothesis `ε ≤ 1/2^k` into `num * 2^k ≤ den` in ℤ. This is exactly
  -- the final `rw` chain of `le_secBits_if`, applied here `at hk'` instead of the goal.
  have h2' : ε.num * 2 ^ k ≤ (ε.den : ℤ) := by
    have hk' := hk
    rw [le_div_iff₀ (by positivity : (0:ℚ) < 2 ^ k), ← Rat.num_div_den ε,
        div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq_pos)] at hk'
    exact_mod_cast hk'
  -- Drop to ℕ (num.toNat = num since num ≥ 0).
  have h2 : ε.num.toNat * 2 ^ k ≤ ε.den := by
    have step : (ε.num.toNat : ℤ) * 2 ^ k ≤ (ε.den : ℤ) := by
      rw [Int.toNat_of_nonneg hnum_pos.le]; exact h2'
    exact_mod_cast step
  -- Re-introduce the floor division: `Nat.le_div_iff_mul_le hp_pos` turns
  -- `2^k ≤ ⌊den/num⌋` into `2^k * num ≤ den`, which is `h2` after commuting.
  have h1 : 2 ^ k ≤ ε.den / ε.num.toNat := by
    rw [Nat.le_div_iff_mul_le hp_pos]
    calc 2 ^ k * ε.num.toNat = ε.num.toNat * 2 ^ k := Nat.mul_comm _ _
      _ ≤ ε.den := h2
  -- ⌊den/num⌋ ≠ 0 because it dominates the positive 2^k.
  have hm : ε.den / ε.num.toNat ≠ 0 :=
    (lt_of_lt_of_le (pow_pos (by norm_num : (0:ℕ) < 2) k) h1).ne'
  -- Pick the `else` branch, then re-attach the log₂ via the BACKWARD direction
  -- of `Nat.le_log2` (`.mpr`): `2^k ≤ n → k ≤ n.log2`.
  unfold secBits
  rw [if_neg (not_le.mpr hε)]
  exact (Nat.le_log2 hm).mpr h1


/-- **The central iff.** `k ≤ secBits ε ↔ ε ≤ 1 / 2 ^ k`.
Both directions are already proved above; this iff is the M0-gate statement. -/
theorem le_secBits_iff (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1) (k : ℕ) :
    k ≤ secBits ε ↔ ε ≤ 1 / 2 ^ k :=
  ⟨le_secBits_if ε hε hε1 k, secBits_ge ε hε k⟩


-- M0 gate "hello world": the 100-bit claim is exact, not an approximation.
example : secBits ((5 / 8 : ℚ) ^ 124 / 2 ^ 16) = 100 := by native_decide


end Soundcalc