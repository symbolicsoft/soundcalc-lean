import Mathlib
import Soundcalc.Field
import Soundcalc.SecBits

open Soundcalc
open Soundcalc.Field

/-!
# `Soundcalc.Lookup` — LogUp, GKR, and the certified log₂ enclosure (roadmap S6)
  Mirrors `soundcalc/lookup/logup.py` and `soundcalc/lookup/gkr.py`.
* `LookupCfg` holds all the parameters needed to evaluate the lookup soundness
  error for all the circuits of interest for SP1.
* Real logarithms are computed approximately in ℚ with a small provably-bounded
  error.
-/

/-
* *TODO*: The current structure only captures the multivariate setting, as SP1
  only considers lookup errors of this type. Including support for the univariate
  setting comes later in the roadmap. Explicit TODO markers have been added
  throughout this file for this purpose.
-/

namespace Soundcalc.Lookup

structure LookupCfg where
  field           : FieldParams
  rowsT           : ℕ -- Rows of "big" table `T`
  rowsL           : ℕ -- Rows of "small" table `L` (looked up inside `T`)
  numColumnsS     : ℕ -- Number of columns of `T` and `L` (`S=1` for single column case)
  numLookupsM     : ℕ -- Number of lookups performed on `T`
  grindBitsLookup : ℕ -- PoW grinding (expressed in bits of security)
  /- *TODO*: Include support for the univariate case -/
  /- *TODO*: Add support for soundcalc's reduction_error
    (optional field) not used within SP1. -/

/-- A rational approximation for `log_2 x` at dyadic granularity `m`
    (e.g. `m = 64` overstates by `< 2^(-6)`); certificate is
    `2^(Nat.clog 2 (x^m) - 1) < x^m ≤ 2^(Nat.clog 2 (x^m))`
    (proved in `log2UB_approx_bound`)
-/
def log2UB (x m : ℕ) : ℚ := (Nat.clog 2 (x^m) : ℚ) / m

/-- Computes an upper bound of the soundness error for the GKR protocol as:
      `(1/2) * (n + m) * (3 * (n + m) + 1) / |F|`
    where:
      - `|F|` is the field size,
      - `2^n` is the alphabet size,
      - `m = log2(M)`, and `M` is the number of lookups.
    Logarithms are upper-bounded as per `log2UB`, ensuring a bounded
    and verifiable over-approximation of the error.
-/
def gkrErrorUB (F : FieldParams) (alphabetSize numLookupsM : ℕ) : ℚ :=
  let n := log2UB alphabetSize 64
  let m := log2UB numLookupsM 64
  let nm := n + m
  (1/2 * nm * (3 * nm + 1) / F.card)

/-- Returns `R`, the soundness multiplier induced by column aggregation.

    For multivariate aggregation `R = log2(S)`, with the single-column case
    normalized to `R = 1`.
    For univariate aggregation `R = S`. *TODO* This is not implemented yet.
-/
def columnAggregFactor (S : ℕ) : ℚ :=
  max (log2UB S 64) 1

def LookupCfg.errUB (c: LookupCfg) : ℚ :=
    /-
    Calculates the base lookup soundness using the unified lookup model:
        `K * H * R / F`
    where `H = rows_L + rows_T` and `R` is the column aggregation factor.
    -/
  let F         := c.field
  let H         := c.rowsL + c.rowsT
  let S         := c.numColumnsS
  let K         := c.numLookupsM
  let R         := columnAggregFactor S
  let baseError := ((K * H : ℚ) * R) / F.card
  /-
    For multivariate lookups, we additionally account for the GKR
    soundness term and any configured reduction error.
    *TODO* In the univariate case, the error below should *not* be added.
  -/
  let gkrError  := gkrErrorUB F H K
  -- *TODO*: Include optional soundness error
  -- We account for the grinding at the very end
  (baseError + gkrError) / 2 ^ c.grindBitsLookup

/- Parsed from https://github.com/ethereum/soundcalc/blob/main/soundcalc/zkvms/sp1/sp1.toml -/
def sp1CoreLookup : LookupCfg where
  field := koalaBear4
  rowsT := 0
  rowsL := 4194304       -- 2 ^ 22
  numColumnsS := 107
  numLookupsM := 1911
  grindBitsLookup := 12

def sp1CompressLookup : LookupCfg where
  field := koalaBear4
  rowsT := 0
  rowsL := 2097152       -- 2 ^ 21
  numColumnsS := 6
  numLookupsM := 53
  grindBitsLookup := 12

def sp1ShrinkLookup : LookupCfg where
  field := koalaBear4
  rowsT := 0
  rowsL := 524288        -- 2 ^ 19
  numColumnsS := 6
  numLookupsM := 53
  grindBitsLookup := 12

/-! ## S6 exit criteria:
    - `secBits` evaluates correctly on the three sp1 circuits (core, compress, shrink)
    - `log2UB` bounds the float formula's exact-rational analogue from above
-/

theorem sp1_core_lookup_bits : secBits sp1CoreLookup.errUB = 100 := by native_decide
theorem sp1_compress_lookup_bits : secBits sp1CompressLookup.errUB = 107 := by native_decide
theorem sp1_shrink_lookup_bits : secBits sp1ShrinkLookup.errUB = 109 := by native_decide

/-- `log_2 x ≤ c/m` reduces to the integer inequality `x^m ≤ 2^c`.
    This will be used to upper-bound the error of `log2UB`.
    Human-stated theorem; AI-assisted proof and comments. -/
theorem logb_le_div {x m c : ℕ}
  (hm : 0 < m)
  (hc : 1 ≤ c)
  (h : x ^ m ≤ 2 ^ c) :
  Real.logb 2 x ≤ (c : ℝ) / m := by
-- cast `m`'s positivity from `ℕ` to `ℝ`
have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
-- split on whether `x = 0` (`logb` is `0` by convention) or `x > 0`
rcases Nat.eq_zero_or_pos x with hx0 | hxpos
· -- case `x = 0`: `logb 2 0 = 0 ≤ c/m` trivially
  subst hx0
  -- `logb 2 0 = 0` by Mathlib convention
  simp only [Nat.cast_zero, Real.logb_zero]
  -- `c/m ≥ 0` since both are naturals cast to `ℝ`
  positivity
· -- `case x > 0`: same argument as before, now via the abstract certificate `h`
  -- transport the given certificate into `ℝ`
  have hcertR : (x:ℝ) ^ m ≤ (2:ℝ) ^ c := by exact_mod_cast h
  -- apply monotonicity of `logb` base `2` to the certificate
  have hstep : Real.logb 2 ((x:ℝ) ^ m) ≤ Real.logb 2 ((2:ℝ) ^ c) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hcertR
  -- unfold `logb` of a power on both sides and simplify `logb 2 2 = 1`
  -- hstep : `↑m * Real.logb 2 ↑x ≤ ↑c`
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hstep
  -- clear the denominator and reorder the product to match hstep's shape
  rw [le_div_iff₀ hmR, mul_comm]
  -- close by casting hstep across the ℚ/ℝ boundary the goal now needs
  exact_mod_cast hstep

/-- `(c-1)/m < log_2 x` reduces to the integer inequality `2^(c-1) < x^m`.
    This will be used to lower-bound the error of `log2UB`.
    Human-stated theorem; AI-assisted proof and comments. -/
theorem div_lt_logb {x m c : ℕ}
    (hm : 0 < m)
    (hc : 1 ≤ c)
    (h  : 2 ^ (c - 1) < x ^ m) :
    ((c : ℝ) - 1) / m < Real.logb 2 x := by
  -- cast `m`'s positivity from `ℕ` to `ℝ`
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  -- `x` must be positive: `x = 0` would force `x^m = 0`, contradicting `2^(c-1) < 0`
  have hxpos : 0 < x := by
    by_contra hx0
    push Not at hx0
    interval_cases x
    simp only [zero_pow hm.ne'] at h
    exact absurd h (Nat.not_succ_le_zero _)
  -- relate `ℕ` truncated subtraction to real subtraction, valid since `hc : 1 ≤ c`
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    push_cast [Nat.cast_sub hc]
    simp
  -- transport the strict certificate into `ℝ`, keeping the exponent typed as `ℕ`
  have hcertR : (2:ℝ) ^ (c - 1 : ℕ) < (x:ℝ) ^ m := by exact_mod_cast h
  -- apply strict monotonicity of `logb` base `2`; now needs positivity of the LEFT argument
  have hstep : Real.logb 2 ((2:ℝ) ^ (c - 1 : ℕ)) < Real.logb 2 ((x:ℝ) ^ m) :=
    Real.logb_lt_logb (by norm_num) (by positivity) hcertR
  -- simplify `logb 2 (2^(c-1)) = (c-1)`: unfold `logb_pow` then `logb 2 2 = 1`
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hstep
  -- separately unfold `logb 2 (x^m) = m * logb 2 x`
  rw [Real.logb_pow] at hstep
  -- replace `ℕ` subtraction cast with real subtraction in `hstep`
  rw [hcast] at hstep
  -- clear the denominator and reorder product to match `hstep`'s shape
  rw [div_lt_iff₀ hmR, mul_comm]
  -- close: `hstep` gives exactly `(c:ℝ) - 1 < ↑m * logb 2 ↑x`
  linarith

/--
    Assuming `x^m ≤ 2^c`, `2^(c-1) < x^m`, `c ≥ 1`, `m > 0`, the above theorems
    give us the following:

    - `c/m` upper-bounds `log_2 x`
    - `(c-1)/m` lower-bounds `log_2 x` (tightly).

    Hence, `c/m` is at most `c - (c-1)/m = 1/m` far from the real logarithm.

    Before moving to showing directly that our `log2UB` is a good approximation,
    we first cast the above results to `c = Nat clog2(x^m)` - an essential component
    of our approximation. Assumption-wise, we get that:

    - `x^m ≤ 2 ^ {clog2(x^m)} ≤ x^m + 1`         [Trivially verified]
    - `2^{clog2(x^m) - 1} ≤ (x^m + 1) - 2 < x^m` [Verified as long as `x^m > 1`]
    - `c ≥ 1`                                    [Verified as long as `x^m > 1`]
    - `m > 0`                                    [By definition of `m`]

    Below, we prove the above facts relating to assumptions.
-/

private theorem clog2_hceil {x m : ℕ} :
  x^m ≤ 2^(Nat.clog 2 (x^m)) := by
  refine Nat.le_pow_clog ?_ (x ^ m)
  linarith

private theorem clog2_hfloor {x m : ℕ} (hxm: 1 < x^m):
  2^(Nat.clog 2 (x^m) - 1) < x^m :=
  Nat.pow_pred_clog_lt_self (by norm_num) hxm

private theorem clog2_hc {x m : ℕ} (hxm: 1 < x^m):
  Nat.clog 2 (x^m) ≥ 1 :=
  Nat.clog_pos (by norm_num) hxm

/- We cast the general-purpose theorems to our `c = Nat clog2(x^m)` setting,
   using only the assumptions we have identified (`hm hxm`). -/
private theorem clog2_upper_bound {x m : ℕ}
  (hxm: 1 < x^m)
  (hm: 0 < m) :
  Real.logb 2 x ≤ ((Nat.clog 2 (x^m)) : ℝ) / m := by
  -- Invoking the auxiliary theorems to get the required assumptions for `logb_le_div`
  have hceil : x^m ≤ 2^(Nat.clog 2 (x^m)) := by apply clog2_hceil
  have hc : 1 ≤ Nat.clog 2 (x^m) := by apply clog2_hc hxm
  apply logb_le_div hm hc hceil

private theorem clog2_lower_bound {x m : ℕ}
  (hxm: 1 < x^m)
  (hm: 0 < m) :
  (((Nat.clog 2 (x^m)) - 1) : ℝ) / m < Real.logb 2 x := by
  -- Invoking the auxiliary theorems to get the required assumptions for `div_lt_logb`
  have hfloor : 2^(Nat.clog 2 (x^m) - 1) < x^m := by apply clog2_hfloor hxm
  have hc : 1 ≤ Nat.clog 2 (x^m) := by apply clog2_hc hxm
  apply div_lt_logb hm hc hfloor

/-
    With the above theorems, we prove that our approximation
    of the real logarithm (`log2UB`) is well-bounded.
-/

/- `log2UB x m` upper-bounds `Real log 2 x` -/
theorem log2UB_upper_bound {x m : ℕ}
  (hxm: 1 < x^m)
  (hm: 0 < m) :
  Real.logb 2 x ≤ log2UB x m := by
  unfold log2UB
  push_cast
  apply clog2_upper_bound hxm hm

/- `log2UB x m - 1/m` lower-bounds `Real log 2 x` -/
theorem log2UB_lower_bound {x m : ℕ}
  (hxm: 1 < x^m)
  (hm: 0 < m) :
  (log2UB x m) - (1 : ℚ) /m < Real.logb 2 x := by
  unfold log2UB
  push_cast
  have hdiv: ((Nat.clog 2 (x ^ m) : ℝ) - 1) / m =
       (Nat.clog 2 (x ^ m) : ℝ) / m - 1 / m := by ring
  rw [← hdiv]
  apply clog2_lower_bound hxm hm

/- Packing the two intermediate theorems together -/
theorem log2UB_approx_bound {x m : ℕ}
  (hxm: 1 < x^m)
  (hm: 0 < m) :
  (log2UB x m) - (1 : ℚ) /m < Real.logb 2 x
  ∧
  Real.logb 2 x ≤ log2UB x m := by
  constructor
  apply log2UB_lower_bound hxm hm
  apply log2UB_upper_bound hxm hm

end Soundcalc.Lookup
