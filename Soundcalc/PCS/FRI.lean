import Mathlib
import Soundcalc.Regime        -- brings in Rate, Regime, UDR (and Field transitively)
import Soundcalc.Common.Utils  -- getSizeOfMerkleMultiProofBits
import Soundcalc.Field          -- certified koalaBear4.elementSizeBits (= 124)

open Soundcalc

/-!
# FRI soundness configuration

Generic structures and error formulas: `FRIConfig`, `FRIConfig.batchingErr`,
`FRIConfig.commitErr`, `FRIConfig.queryErr`, and `getFRIProofSizeBits`.
SP1-specific instances and exit criteria live in `Soundcalc.ZkVM.SP1`.
Jagged-layer proof size helpers (`sumcheckSizeBits`, `getJaggedReductionSizeBits`,
`getJaggedProofSizeBits`) live in `Soundcalc.Circuit.Jagged`.

`ρ` is stored as `Rate` (the subtype `{ρ : ℚ // 0 < ρ ∧ ρ < 1}`) so the
constraint is enforced at construction time and Regime's field signatures are
satisfied without any conversion at call sites.
-/

abbrev N := Nat
abbrev Q := Rat

/-! ## FRI configuration -/

structure FRIConfig where
  field          : Field.FieldParams
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

`koalaBear4FieldBits` is the number of bits to represent one element of KoalaBear⁴
(`4 · ⌈log₂ p⌉`).  Rather than recompute it with a private `⌈log₂⌉`, we reuse the
*certified* field-element size from `Soundcalc.Field`, where `koalaBear4_elementBits`
proves `elementSizeBits = 124`. -/

def koalaBear4FieldBits : N := Soundcalc.Field.koalaBear4.elementSizeBits

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
