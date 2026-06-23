import Mathlib
import Soundcalc.Regime        -- brings in FieldParams, Rate, Regime, UDR, koalaBear4
                               -- and transitively SecBits (secBits)
import Soundcalc.Common.Utils  -- getSizeOfMerkleMultiProofBits

open Soundcalc

/-!
# FRI soundness configuration

Verbatim from the spec: `FRIConfig`, `FRIConfig.batchingErr`,
`FRIConfig.commitErr`, `FRIConfig.queryErr`, and the *statement* of
`FRIConfig.earlyStop_ok`.

`ρ` is stored as `Rate` (the subtype `{ρ : ℚ // 0 < ρ ∧ ρ < 1}`) so the
constraint is enforced at construction time and Regime's field signatures are
satisfied without any conversion at call sites.
-/

abbrev N := Nat
abbrev Q := Rat

/-! ## FRI configuration -/

structure FRIConfig where
  field          : FieldParams
  ρ              : Rate          -- rate, constrained to (0,1) by the Rate subtype
  denseLen       : N             -- = 2^21 for SP1 core
  batchSize      : N             -- = 193
  numQueries     : N             -- = 124
  foldingFactors : List N        -- = [2,2,...] (21 entries)
  earlyStopDeg   : N             -- = 4
  grindQuery     : N             -- = 16
  grindBatch     : N             -- = 5

def FRIConfig.batchingErr (c : FRIConfig) (R : Regime) : Q :=
  R.errMultilinear c.ρ c.denseLen c.batchSize / 2 ^ c.grindBatch

def FRIConfig.commitErr (c : FRIConfig) (R : Regime) (i : N) : Q :=
  let acc := (c.foldingFactors.take (i + 1)).foldl (· * ·) 1
  R.errPowers c.ρ (c.denseLen / acc) (c.foldingFactors.getD i 1)

def FRIConfig.queryErr (c : FRIConfig) (R : Regime) : Q :=
  (1 - R.θ c.ρ c.denseLen) ^ c.numQueries / 2 ^ c.grindQuery

/-! ## SP1 core config

`denseLen` is the FRI dimension `d`; `n = d/ρ = 2^23`.  The trace length
(`2^22`, used by zerocheck) is a *separate* quantity and deliberately
does **not** appear in `FRIConfig`. -/

def sp1CoreFRI : FRIConfig where
  field          := koalaBear4
  ρ              := ⟨1 / 4, by norm_num⟩   -- 0 < 1/4 < 1, proved at definition time
  denseLen       := 2 ^ 21
  batchSize      := 193
  numQueries     := 124
  foldingFactors := List.replicate 21 2
  earlyStopDeg   := 4
  grindQuery     := 16
  grindBatch     := 5

/-! ## Early-stop side condition

The statement is the spec's, with explicit `ℚ` coercions made visible:
`c.denseLen / (c.ρ : Q)` mixes `ℕ` and `ℚ`; the cast `(c.ρ : Q)` extracts
the value from the `Rate` subtype. -/

theorem FRIConfig.earlyStop_ok (c : FRIConfig) (hc : c = sp1CoreFRI) :
    ((c.denseLen : Q) / (c.ρ : Q)) / ((c.foldingFactors.foldl (· * ·) 1 : N) : Q)
      = (c.earlyStopDeg : Q) := by
  subst hc
  simp only [sp1CoreFRI]
  norm_num [show ((List.replicate 21 2).foldl (· * ·) 1 : N) = 2097152 from by decide]

/-! ## Exit criteria

`queryErr` is fully determined by `θ = (1−ρ)/2`, so it closes now:
`(1 − 3/8)^124 / 2^16 = (5/8)^124 / 2^16`, whose `⌊−log₂⌋` is `100`. -/

example : secBits (sp1CoreFRI.queryErr (UDR koalaBear4)) = 100 := by native_decide

example : secBits (sp1CoreFRI.batchingErr (UDR koalaBear4)) = 104 := by native_decide
example : secBits (sp1CoreFRI.commitErr (UDR koalaBear4) 0) = 103 := by native_decide
example : secBits (sp1CoreFRI.commitErr (UDR koalaBear4) 20) = 122 := by native_decide

/-! ## FRI proof size -/

/-- Proof size (or expected proof size) of a BCS-transformed FRI interaction in bits.

    Structure:
    * Initial round: one Merkle root + one multi-proof for all `numQueries` queries
      (the `batchSize` initial functions share a single commitment).
    * Each folding round: one root + one multi-proof; siblings are grouped into one
      leaf so `tupleSize = foldingFactor` and `numLeafs = n / foldingFactor`.
    * Final round: the low-degree polynomial sent in the clear
      (`rate * n_final * fieldSizeBits` bits). -/
def getFRIProofSizeBits
    (hashSizeBits fieldSizeBits batchSize numQueries domainSize : N)
    (foldingFactors : List N)
    (rate : ℚ)
    (expected : Bool) : N :=
  let initBits :=
    hashSizeBits +
    getSizeOfMerkleMultiProofBits
      domainSize numQueries batchSize fieldSizeBits hashSizeBits expected
  let (totalBits, finalN) :=
    foldingFactors.foldl (fun (acc : N × N) factor =>
      let (bits, n) := acc
      let n' := n / factor
      let newBits :=
        bits + hashSizeBits +
        getSizeOfMerkleMultiProofBits
          n' numQueries factor fieldSizeBits hashSizeBits expected
      (newBits, n'))
    (initBits, domainSize)
  -- rate * finalN * fieldSizeBits, keeping arithmetic in ℕ via num/den
  totalBits + rate.num.toNat * finalN * fieldSizeBits / rate.den

/-! ## Proof size exit criteria

`koalaBear4FieldBits` is the number of bits needed to represent one element of KoalaBear⁴:
4 coefficients × ⌈log₂ p⌉ bits each, where p = `koalaBearPrime`. -/

def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

def koalaBear4FieldBits : N := 4 * ceilLog2 koalaBearPrime

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
       logTrace = ⌈log₂ denseTraceLen⌉ + ⌈log₂ batchSize⌉

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

/-!
Parameters per circuit (from `soundcalc/zkvms/sp1/sp1.toml`):

| circuit  | denseTraceLen | ρ    | domainSize        | batchSize | numQueries | foldRounds |
|----------|---------------|------|-------------------|-----------|------------|------------|
| core     | 2^21          | 1/4  | 2^21/(1/4) = 2^23 | 193       | 124        | 21 × 2     |
| compress | 2^20          | 1/4  | 2^20/(1/4) = 2^22 | 128       | 124        | 20 × 2     |
| shrink   | 2^18          | 1/8  | 2^18/(1/8) = 2^21 | 128       | 94         | 18 × 2     |

`hashSizeBits = 248` for all three.
Sizes are floor-divided by `KIB = 8192` to match the KiB figures in the report. -/

-- FRI-only sizes (getFRIProofSizeBits, matching the Python get_FRI_proof_size_bits):
-- core: 913 KiB (expected) / 1474 KiB (worst case)
example : getFRIProofSizeBits 248 koalaBear4FieldBits 193 124 (2^23) (List.replicate 21 2) (1/4 : ℚ) true  / KIB = 913  := by native_decide
example : getFRIProofSizeBits 248 koalaBear4FieldBits 193 124 (2^23) (List.replicate 21 2) (1/4 : ℚ) false / KIB = 1474 := by native_decide
-- compress: 730 KiB (expected) / 1261 KiB (worst case)
example : getFRIProofSizeBits 248 koalaBear4FieldBits 128 124 (2^22) (List.replicate 20 2) (1/4 : ℚ) true  / KIB = 730  := by native_decide
example : getFRIProofSizeBits 248 koalaBear4FieldBits 128 124 (2^22) (List.replicate 20 2) (1/4 : ℚ) false / KIB = 1261 := by native_decide
-- shrink: 524 KiB (expected) / 882 KiB (worst case)
example : getFRIProofSizeBits 248 koalaBear4FieldBits 128 94  (2^21) (List.replicate 18 2) (1/8 : ℚ) true  / KIB = 524  := by native_decide
example : getFRIProofSizeBits 248 koalaBear4FieldBits 128 94  (2^21) (List.replicate 18 2) (1/8 : ℚ) false / KIB = 882  := by native_decide

-- Full Jagged proof sizes (getJaggedProofSizeBits, matching the SP1 report):
-- core: 918 KiB (expected) / 1479 KiB (worst case)
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 193 124 (2^21) (2^23) (List.replicate 21 2) (1/4 : ℚ) true  / KIB = 918  := by native_decide
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 193 124 (2^21) (2^23) (List.replicate 21 2) (1/4 : ℚ) false / KIB = 1479 := by native_decide
-- compress: 735 KiB (expected) / 1267 KiB (worst case)
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 124 (2^20) (2^22) (List.replicate 20 2) (1/4 : ℚ) true  / KIB = 735  := by native_decide
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 124 (2^20) (2^22) (List.replicate 20 2) (1/4 : ℚ) false / KIB = 1267 := by native_decide
-- shrink: 529 KiB (expected) / 887 KiB (worst case)
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 94  (2^18) (2^21) (List.replicate 18 2) (1/8 : ℚ) true  / KIB = 529  := by native_decide
example : getJaggedProofSizeBits 248 koalaBear4FieldBits 128 94  (2^18) (2^21) (List.replicate 18 2) (1/8 : ℚ) false / KIB = 887  := by native_decide
