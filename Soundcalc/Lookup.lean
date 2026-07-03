import Soundcalc.Field
import Soundcalc.Common.Log

/-!
# `Soundcalc.Lookup` — LogUp and GKR soundness errors (roadmap S6)
  Mirrors `soundcalc/lookup/logup.py` and `soundcalc/lookup/gkr.py`.
* `LookupCfg` holds all the parameters needed to evaluate the lookup soundness
  error.
* `log2UB` and its certified enclosure theorems live in `Soundcalc.Common.Log`.
-/

/-
* *TODO*: The current formalization only captures the multivariate setting, as SP1
  only considers lookup errors of this type. While the structure now supports
  the univariate setting, a complete formalization comes later in the roadmap.
  Explicit TODO markers have been added throughout this file for this purpose.
-/

namespace Soundcalc

structure LookupCfg where
  name            : String
  field           : FieldParams
  isLogUpMultivar : Bool           -- Maps the `LogUpType` enum (`univariate` or `multivariate`)
  rowsT           : ℕ              -- Rows of "big" table `T`
  rowsL           : ℕ              -- Rows of "small" table `L` (looked up inside `T`)
  numColumnsS     : ℕ     := 1     -- Number of columns of `T` and `L` (`S=1` for single column case)
  numLookupsM     : ℕ     := 1     -- Number of lookups performed on `T`
  grindBitsLookup : ℕ     := 0     -- PoW grinding (expressed in bits of security)
  /- Boolean switch supporting univariate/multivariate lookups.
    *TODO* No semantics yet; will affect `columnAggregFactor`-/
  isMultilinear   : Bool  := false
  /- (optional field) Auxiliary soundness error; unused within SP1. -/
  reductionErr    : Float := 0.0

  /- *TODO*: whenever `isLogUpMultivar` is true, `isMultilinear` must
     also be. The calling protocol must ensure structures are well-formed.
     This replaces soundcalc's __post_init__; comes later on in our roadmap. -/

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

end Soundcalc
