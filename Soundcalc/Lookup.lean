import Soundcalc.Field.Core
import Soundcalc.Common.Log

/-!
# `Soundcalc.Lookup` — LogUp and GKR soundness errors (roadmap S6)
  Mirrors `soundcalc/lookup/logup.py` and `soundcalc/lookup/gkr.py`.
* `LookupCfg` holds all the parameters needed to evaluate the lookup soundness
  error.
* `log2UB` and its certified enclosure theorems live in `Soundcalc.Common.Log`.
-/

namespace Soundcalc

structure LookupCfg where
  name            : String
  field           : FieldParams
  isLogUpMultivar : Bool           -- false = univariate (e.g., Airbender); true = multivariate (e.g., SP1)
  rowsT           : ℕ              -- Rows of "big" table `T`
  rowsL           : ℕ              -- Rows of "small" table `L` (looked up inside `T`)
  numColumnsS     : ℕ     := 1     -- Number of columns of `T` and `L` (`S=1` for single column case)
  numLookupsM     : ℕ     := 1     -- Number of lookups performed on `T`
  grindBitsLookup : ℕ     := 0     -- PoW grinding (expressed in bits of security)
  /- Auxiliary soundness error added on top of the grind-scaled error (Python: `reduction_err`). -/
  reductionErr    : ℚ    := 0
  /-- Column-aggregation model (Python `multilinear_fingerprint`), independent of `isLogUpMultivar`.
      `true` ⇒ `R = max(⌈log₂ S⌉, 1)`; `false` ⇒ `R = S`. Defaults to `isLogUpMultivar`, matching
      the Python default (`multivariate ⇒ true`), but a univariate lookup can still set it. -/
  multilinearFingerprint : Bool := isLogUpMultivar

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

    - Multivariate (`multilinear = true`):  `R = max(⌈log₂ S⌉, 1)` (SP1 path).
    - Univariate   (`multilinear = false`): `R = S`                 (Airbender logup path). -/
def columnAggregFactor (S : ℕ) (multilinear : Bool) : ℚ :=
  if multilinear then max (log2UB S 64) 1 else (S : ℚ)

def LookupCfg.errUB (c : LookupCfg) : ℚ :=
  let H         := c.rowsL + c.rowsT
  let R         := columnAggregFactor c.numColumnsS c.multilinearFingerprint
  let baseError := ((c.numLookupsM * H : ℚ) * R) / c.field.card
  -- Multivariate only: GKR reduction term and auxiliary reduction error.
  let gkrError  := if c.isLogUpMultivar then gkrErrorUB c.field H c.numLookupsM + c.reductionErr else 0
  (baseError + gkrError) / 2 ^ c.grindBitsLookup

/-! ## Soundness of the rational lookup cell

`errUB` is rational only because every `log₂` in it is replaced by the dyadic over-approximation
`log2UB · 64`: once in `columnAggregFactor` (`R = max(⌈log₂ S⌉, 1)`, multivariate path) and twice
inside `gkrErrorUB` (`n = log₂(alphabet)`, `m = log₂ M`). Both sites sit under expressions that are
*increasing* in the logarithm — `R` multiplies the base error, and `½·nm·(3nm+1)` is increasing in
`nm ≥ 0` — so over-approximating the logs over-approximates the cell.

This is the lookup counterpart of `jbrErrLinear_conservative`, and it is what makes `errUB` an
honest upper bound rather than merely a rational stand-in. -/

/-- Logarithms of naturals are nonnegative (`logb 2 0 = 0` by convention, `logb 2 x ≥ 0` for
`x ≥ 1`) — needed because `½·nm·(3nm+1)` is only increasing on `nm ≥ 0`. -/
theorem logb_nat_nonneg (x : ℕ) : 0 ≤ Real.logb 2 (x : ℝ) := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  · have h1 : (1 : ℕ) ≤ x := hx
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h1)

/-- The **true** column-aggregation multiplier, with the genuine `log₂`. -/
noncomputable def trueColumnAggregFactor (S : ℕ) (multilinear : Bool) : ℝ :=
  if multilinear then max (Real.logb 2 (S : ℝ)) 1 else (S : ℝ)

/-- The **true** GKR reduction error, with the genuine `log₂`s. -/
noncomputable def trueGkrError (F : FieldParams) (alphabetSize numLookupsM : ℕ) : ℝ :=
  let n := Real.logb 2 (alphabetSize : ℝ)
  let m := Real.logb 2 (numLookupsM : ℝ)
  let nm := n + m
  (1 / 2 * nm * (3 * nm + 1) / (F.card : ℝ))

/-- The **true** real-valued lookup error: `errUB` with every `log2UB` replaced by `Real.logb 2`. -/
noncomputable def LookupCfg.trueErrUB (c : LookupCfg) : ℝ :=
  let H         := c.rowsL + c.rowsT
  let R         := trueColumnAggregFactor c.numColumnsS c.multilinearFingerprint
  let baseError := ((c.numLookupsM : ℝ) * (H : ℝ) * R) / (c.field.card : ℝ)
  let gkrError  := if c.isLogUpMultivar then
                     trueGkrError c.field H c.numLookupsM + (c.reductionErr : ℝ) else 0
  (baseError + gkrError) / 2 ^ c.grindBitsLookup

/-- `columnAggregFactor` over-approximates its true counterpart. -/
theorem trueColumnAggregFactor_le (S : ℕ) (multilinear : Bool) :
    trueColumnAggregFactor S multilinear ≤ ((columnAggregFactor S multilinear : ℚ) : ℝ) := by
  unfold trueColumnAggregFactor columnAggregFactor
  cases multilinear with
  | false => simp
  | true =>
    -- Bound each branch of the left `max` against the whole right-hand `max`, rather than
    -- pushing casts through `max` on both sides.
    have hUB : ((log2UB S 64 : ℚ) : ℝ) ≤ ((max (log2UB S 64) 1 : ℚ) : ℝ) := by
      have h : (log2UB S 64 : ℚ) ≤ max (log2UB S 64) 1 := le_max_left _ _
      exact_mod_cast h
    have h1 : (1 : ℝ) ≤ ((max (log2UB S 64) 1 : ℚ) : ℝ) := by
      have h : (1 : ℚ) ≤ max (log2UB S 64) 1 := le_max_right _ _
      exact_mod_cast h
    refine max_le ?_ h1
    exact le_trans (logb_le_log2UB S (m := 64) (by norm_num)) hUB

/-- `gkrErrorUB` over-approximates its true counterpart: `nm ↦ ½·nm·(3nm+1)` is increasing on
`nm ≥ 0`, and each `log₂` is over-approximated. -/
theorem trueGkrError_le (F : FieldParams) (alphabetSize numLookupsM : ℕ) :
    trueGkrError F alphabetSize numLookupsM
      ≤ ((gkrErrorUB F alphabetSize numLookupsM : ℚ) : ℝ) := by
  have hcard : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast F.card_pos
  have hn := logb_le_log2UB alphabetSize (m := 64) (by norm_num)
  have hm := logb_le_log2UB numLookupsM (m := 64) (by norm_num)
  have hn0 := logb_nat_nonneg alphabetSize
  have hm0 := logb_nat_nonneg numLookupsM
  unfold trueGkrError gkrErrorUB
  push_cast
  gcongr
  linarith

/-- **The rational lookup cell over-approximates the true one.** -/
theorem LookupCfg.errUB_conservative (c : LookupCfg) :
    c.trueErrUB ≤ ((c.errUB : ℚ) : ℝ) := by
  have hcard : (0 : ℝ) < (c.field.card : ℝ) := by exact_mod_cast c.field.card_pos
  have hR := trueColumnAggregFactor_le c.numColumnsS c.multilinearFingerprint
  have hG := trueGkrError_le c.field (c.rowsL + c.rowsT) c.numLookupsM
  simp only [LookupCfg.trueErrUB, LookupCfg.errUB]
  -- `gcongr` cannot descend through the multivariate `if`, so split first; in each branch the
  -- two sides differ only at `R` (and, multivariate, at the GKR term), both in context.
  split_ifs with h
  · push_cast; gcongr
  · push_cast; gcongr

end Soundcalc
