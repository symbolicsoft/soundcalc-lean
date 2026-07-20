import Mathlib
import Soundcalc.PCS.FRI
import Soundcalc.Lookup

open Soundcalc

namespace Soundcalc

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
  name           : String
  field          : FieldParams
  proofSystName  : String
  /- The three fields below expand the `JaggedPCS` structure. -/
  densePCS       : FRIConfig
  traceLength    : N    -- e.g. 2^22 (one gotcha: use trace length, not FRI dimension)
  traceWidth     : N    -- e.g. 3741
  numConstraints : N    -- e.g. 3412
  airMaxDegree   : N    -- e.g. 3
  lookups        : List LookupCfg := []
  /-- Every sub-protocol must run over the same field as the jagged circuit itself. -/
  h_densePCS_field : densePCS.field = field := by rfl
  h_lookups_field  : lookups.all (·.field == field) = true := by decide

/-- Reduction soundness error.

`ℓ = ⌈log₂ denseLen⌉ + ⌈log₂ batchSize⌉`; the formula counts variables checked
in two rounds of the jagged sumcheck (width term + linear and quadratic bookkeeping). -/
def JaggedCfg.reduceErr (c : JaggedCfg) : Q :=
  let l := Nat.clog 2 c.densePCS.denseLen + Nat.clog 2 c.densePCS.batchSize  -- 21 + 8 = 29
  ((Nat.clog 2 c.traceWidth : Q) + 2 * l + 2 * (2 * l + 2)) / (c.field.card : Q)

/-- Zerocheck soundness error.

Standard AIR zerocheck: `C` constraint terms plus `(deg + 2)` per sumcheck variable
over `⌈log₂ H⌉` variables. -/
def JaggedCfg.zerocheckErr (c : JaggedCfg) : Q :=
  ((c.numConstraints : Q) + (c.airMaxDegree + 2) * Nat.clog 2 c.traceLength)
  / (c.field.card : Q)


/--
  Enumerates all the soundness errors of a Jagged circuit.
-/
def JaggedCfg.listErrs (c: JaggedCfg) : List ℚ := do
  let mut l : List ℚ := []
  l := c.reduceErr :: l
  l := c.zerocheckErr :: l
  let fcfg := c.densePCS
  l := (fcfg.batchingErr (UDR fcfg.field)) :: l
  for i in List.range fcfg.foldingFactors.length do
    l := (fcfg.commitErr (UDR fcfg.field) i) :: l
  l := (fcfg.queryErr (UDR fcfg.field)) :: l
  for lcfg in c.lookups do
    l := lcfg.errUB :: l
  l

/--
  Total soundness error of a Jagged circuit.
  Computed as the maximum of all the soundness errors.
-/
def JaggedCfg.totalErr (c : JaggedCfg) : ℚ :=
  match (listErrs c).maximum with
  | some m => m
  | none   => 0

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

private def sumcheckSizeBits (degree numVars fieldBits : N) : N :=
  (numVars * (degree + 2) + 2) * fieldBits

private def getJaggedReductionSizeBits (denseTraceLen batchSize fieldBits : N) : N :=
  let logTrace := Nat.clog 2 denseTraceLen + Nat.clog 2 batchSize
  sumcheckSizeBits 2 logTrace fieldBits + sumcheckSizeBits 2 (2 * logTrace + 2) fieldBits

/-! ## Full Jagged proof size

`getJaggedProofSizeBits` = `proofSizePCS` + `getJaggedReductionSizeBits`.

This matches `JaggedPCS.get_proof_size_bits` / `get_expected_proof_size_bits` in the
soundcalc Python, which is what the SP1 report numbers are computed from.

Note: lookups are *not* included in the soundcalc proof-size estimate (they appear only in
the security-level table); `getJaggedProofSizeBits` therefore matches the report exactly
without any lookup term. -/

private def getJaggedProofSizeBits (c: JaggedCfg) (expected: Bool) : ℕ :=
  let fieldSizeBits := c.densePCS.field.elementSizeBits
  let batchSize := c.densePCS.batchSize
  let denseTraceLen := c.densePCS.denseLen

  let proofSizePCS :=
    if expected then c.densePCS.proofSizeExp
    else c.densePCS.proofSizeWorst

  proofSizePCS + getJaggedReductionSizeBits denseTraceLen batchSize fieldSizeBits

def JaggedCfg.proofSizeExp (c: JaggedCfg) : ℕ :=
  getJaggedProofSizeBits c true

def JaggedCfg.proofSizeWorst (c: JaggedCfg) : ℕ :=
  getJaggedProofSizeBits c false

end Soundcalc
