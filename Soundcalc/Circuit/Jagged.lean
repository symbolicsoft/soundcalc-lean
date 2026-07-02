import Mathlib
import Soundcalc.Regime
import Soundcalc.PCS.FRI

namespace Soundcalc

private abbrev N := Nat
private abbrev Q := Rat

/-!
# Jagged circuit error bounds

Pure integer `|F|` terms for the jagged reduction and zerocheck protocols
(corresponding to `circuits/jagged.py`).

With `ℓ = ⌈log₂ d⌉ + ⌈log₂ b⌉ = 21 + 8 = 29`:

* **reduceErr**: `(⌈log₂ w⌉ + 2ℓ + 2(2ℓ + 2)) / |F|`
  where `w` is the trace width.

* **zerocheckErr**: `(C + (deg + 2) ⌈log₂ H⌉) / |F|`
  where `C` is the constraint count, `deg` is the AIR max degree, and `H` is
  the trace length.
-/

/-- Parameters for a jagged circuit instance. -/
structure JaggedCfg where
  field          : FieldParams
  denseLen       : N    -- e.g. 2^21 (FRI dimension d)
  batchSize      : N    -- e.g. 193  (contributes ⌈log₂ b⌉ to ℓ)
  traceWidth     : N    -- e.g. 3741
  traceLength    : N    -- e.g. 2^22 (one gotcha: use trace length, not FRI dimension)
  numConstraints : N    -- e.g. 3412
  airMaxDegree   : N    -- e.g. 3

/-- Reduction soundness error.

`ℓ = ⌈log₂ denseLen⌉ + ⌈log₂ batchSize⌉`; the formula counts variables checked
in two rounds of the jagged sumcheck (width term + linear and quadratic bookkeeping). -/
def JaggedCfg.reduceErr (c : JaggedCfg) : Q :=
  let l := Nat.clog 2 c.denseLen + Nat.clog 2 c.batchSize  -- 21 + 8 = 29
  ((Nat.clog 2 c.traceWidth : Q) + 2 * l + 2 * (2 * l + 2)) / (c.field.card : Q)

/-- Zerocheck soundness error.

Standard AIR zerocheck: `C` constraint terms plus `(deg + 2)` per sumcheck variable
over `⌈log₂ H⌉` variables. -/
def JaggedCfg.zerocheckErr (c : JaggedCfg) : Q :=
  ((c.numConstraints : Q) + (c.airMaxDegree + 2) * Nat.clog 2 c.traceLength)
  / (c.field.card : Q)

/-! ## Jagged reduction proof size

In the Jagged proof system (used by SP1), the dense FRI interaction is only part of the proof.
On top of it sits the *Jagged reduction*: two sumcheck protocols that reduce the multilinear
constraint system down to the dense FRI oracle.

Source: `soundcalc/circuits/jagged.py`, `JaggedPCS._reduction_proof_size_bits`.

The helper `sumcheckSizeBits degree numVars fieldBits` gives the transcript size of one
sumcheck with a degree-`degree` polynomial in `numVars` variables.  The formula is verbatim
from the Python:

    (numVars * (degree + 2) + 2) * fieldBits

`getJaggedReductionSizeBits denseTraceLen batchSize fieldBits` runs two such sumchecks:

1. **Jagged sumcheck** over `logTrace` variables, where
       `logTrace = ⌈log₂ denseTraceLen⌉ + ⌈log₂ batchSize⌉`

2. **Jagged evaluation sumcheck** over `2 * logTrace + 2` variables.

Both use degree 2. -/

def sumcheckSizeBits (degree numVars fieldBits : N) : N :=
  (numVars * (degree + 2) + 2) * fieldBits

def getJaggedReductionSizeBits (denseTraceLen batchSize fieldBits : N) : N :=
  let logTrace := Nat.clog 2 denseTraceLen + Nat.clog 2 batchSize
  sumcheckSizeBits 2 logTrace fieldBits + sumcheckSizeBits 2 (2 * logTrace + 2) fieldBits

/-! ## Full Jagged proof size

`getJaggedProofSizeBits` = `getFRIProofSizeBits` + `getJaggedReductionSizeBits`.

This matches `JaggedPCS.get_proof_size_bits` / `get_expected_proof_size_bits` in the
soundcalc Python, which is what the SP1 report numbers are computed from.

Note: lookups are *not* included in the soundcalc proof-size estimate (they appear only in
the security-level table); `getJaggedProofSizeBits` therefore matches the report exactly
without any lookup term. -/

def getJaggedProofSizeBits
    (hashSizeBits fieldSizeBits batchSize numQueries denseTraceLen domainSize : N)
    (foldingFactors : List N)
    (rate : ℚ)
    (expected : Bool) : N :=
  getFRIProofSizeBits
      hashSizeBits fieldSizeBits batchSize numQueries domainSize foldingFactors rate expected +
  getJaggedReductionSizeBits denseTraceLen batchSize fieldSizeBits

/-! ## Jagged proof sizes

Parameters per circuit (from `soundcalc/zkvms/sp1/sp1.toml`):

| circuit  | denseTraceLen | ρ    | domainSize        | batchSize | numQueries | foldRounds |
|----------|---------------|------|-------------------|-----------|------------|------------|
| core     | 2^21          | 1/4  | 2^21/(1/4) = 2^23 | 193       | 124        | 21 × 2     |
| compress | 2^20          | 1/4  | 2^20/(1/4) = 2^22 | 128       | 124        | 20 × 2     |
| shrink   | 2^18          | 1/8  | 2^18/(1/8) = 2^21 | 128       | 94         | 18 × 2     |

`hashSizeBits = 248` for all three.
Sizes are floor-divided by `KIB = 8192` to match the KiB figures in the report.
-/

-- core: 918 KiB (expected) / 1479 KiB (worst case)
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 193 124 (2^21) (2^23) (List.replicate 21 2) (1/4 : ℚ) true  / KIB = 918  := by native_decide
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 193 124 (2^21) (2^23) (List.replicate 21 2) (1/4 : ℚ) false / KIB = 1479 := by native_decide
-- compress: 735 KiB (expected) / 1267 KiB (worst case)
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 124 (2^20) (2^22) (List.replicate 20 2) (1/4 : ℚ) true  / KIB = 735  := by native_decide
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 124 (2^20) (2^22) (List.replicate 20 2) (1/4 : ℚ) false / KIB = 1267 := by native_decide
-- shrink: 529 KiB (expected) / 887 KiB (worst case)
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 94  (2^18) (2^21) (List.replicate 18 2) (1/8 : ℚ) true  / KIB = 529  := by native_decide
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 94  (2^18) (2^21) (List.replicate 18 2) (1/8 : ℚ) false / KIB = 887  := by native_decide

end Soundcalc
