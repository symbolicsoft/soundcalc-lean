import Mathlib

namespace Soundcalc

/-- 1 KiB in bits (1024 bytes × 8). -/
def KIB : ℕ := 1024 * 8

/-- Compute ρ+. See page 16 of Ha22. -/
def getRhoPlus (H : ℕ) (D : ℚ) (maxCombo : ℕ) : ℚ :=
  (H + maxCombo : ℚ) / D

/-- Ceiling division `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Size of a single Merkle path in bits (leaf + sibling + co-path). -/
def getSizeOfMerkleProofBits
    (numLeafs tupleSize elementSizeBits hashSizeBits : ℕ) : ℕ :=
  let leafSize  := tupleSize * elementSizeBits
  let sibling   := min (tupleSize * elementSizeBits) hashSizeBits
  let treeDepth := Nat.clog 2 numLeafs
  let coPath    := (treeDepth - 1) * hashSizeBits
  leafSize + sibling + coPath

/-- Expected size of a Merkle multi-proof in bits (inclusion-exclusion formula).
    See https://xn--2-umb.com/25/merkle-multi-proof/#expected-value-1 -/
def getSizeOfMerkleMultiProofBitsExpected
    (numLeafs numOpenings tupleSize elementSizeBits hashSizeBits : ℕ) : ℕ :=
  let leafsSize := numOpenings * tupleSize * elementSizeBits
  let treeDepth := Nat.clog 2 numLeafs
  let numHashes :=
    ∑ d ∈ Finset.Icc 1 treeDepth,
      ceilDiv ((2 ^ d - 1) ^ numOpenings - (2 ^ d - 2) ^ numOpenings)
              (2 ^ (d * (numOpenings - 1)))
  leafsSize + numHashes * hashSizeBits

/-- Worst-case (`expected = false`) or expected (`expected = true`) size of a
    Merkle multi-proof in bits. -/
def getSizeOfMerkleMultiProofBits
    (numLeafs numOpenings tupleSize elementSizeBits hashSizeBits : ℕ)
    (expected : Bool) : ℕ :=
  if expected then
    getSizeOfMerkleMultiProofBitsExpected
      numLeafs numOpenings tupleSize elementSizeBits hashSizeBits
  else
    numOpenings * getSizeOfMerkleProofBits numLeafs tupleSize elementSizeBits hashSizeBits

end Soundcalc
