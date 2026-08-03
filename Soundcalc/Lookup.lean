import Soundcalc.Field.Core
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

end Soundcalc
