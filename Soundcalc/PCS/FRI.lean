import Mathlib
import Soundcalc.Regime        -- brings in Rate, Regime, UDR (and Field transitively)
import Soundcalc.Common.Utils  -- getSizeOfMerkleMultiProofBits
import Soundcalc.Field.KoalaBear   -- certified koalaBear4.elementSizeBits (= 124)
import Soundcalc.Common.Log

open Soundcalc

namespace Soundcalc

/-!
# FRI soundness configuration

Generic structures and error formulas: `FRIConfig`, `FRIConfig.batchingErr`,
`FRIConfig.commitErr`, `FRIConfig.queryErr`.
Proof sizes are computed from `getFRIProofSizeBits`, with `FRIConfig.proofSizeExp`
and `FRIConfig.proofSizeWorst` being the calling API.
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
  hashBits       : N
  ρ              : Rate          -- rate, constrained to (0,1) by the Rate subtype
  field          : FieldParams
  denseLen       : N             -- = 2^21 for SP1 core
  batchSize      : N             -- = 193
  powerBatch     : Bool
  multilinBatch  : Bool
  numQueries     : N             -- = 124
  foldingFactors : List N        -- = [2,2,...] (21 entries)
  earlyStopDeg   : N             -- = 4
  grindQuery     : N             -- = 16
  grindBatch     : N             := 0
  grindCommit    : N             := 0        -- = 5 for Airbender; 0 keeps SP1 configs valid
  /-- After all folds, the residual domain size equals `earlyStopDeg`. -/
  h_earlyStop    : ((denseLen : Q) / (ρ : Q)) / ((foldingFactors.foldl (· * ·) 1 : N) : Q)
                   = (earlyStopDeg : Q) := by native_decide

/-- Powers-batching error: uses `errPowers` (Airbender's `power_batching = true` path)
    then applies the batching grind. -/
def FRIConfig.batchingErr (c : FRIConfig) (R : Regime) : Q :=
  if c.powerBatch then  R.errPowers c.ρ c.denseLen c.batchSize / 2 ^ c.grindBatch
  else R.errMultilinear c.ρ c.denseLen c.batchSize / 2 ^ c.grindBatch

def FRIConfig.commitErr (c : FRIConfig) (R : Regime) (i : N) : Q :=
  let acc : ℕ := (c.foldingFactors.take (i + 1)).foldl (· * ·) 1
  R.errPowers c.ρ ((c.denseLen : ℚ) / acc) (c.foldingFactors.getD i 1) / 2 ^ c.grindCommit

def FRIConfig.queryErr (c : FRIConfig) (R : Regime) : Q :=
  (1 - R.θLB c.ρ c.denseLen) ^ c.numQueries / 2 ^ c.grindQuery

/--
  Domain size, after low-degree extension

  `.toNat` is justified, as the input to `round`
  is always nonnegative, given that:
  - `c.denseLen` is a `Nat`;
  - `c.ρ` is of type `Rate` (0 < ρ < 1, ρ ∈ ℚ).
  Moreover, for relevant configs no rounding occurs
  at all (`ρ ∈ {1/2, 1/4, 1/8}`)
-/
def FRIConfig.D (c: FRIConfig) : ℕ :=
  (round ((c.denseLen : ℚ) / (c.ρ : ℚ))).toNat

/--
  Log of the dense length, computed in the Python `soundcalc` as:
  `int(round(log2(trace_length)))`

  `.toNat` is justified, as `log2UB` is always
  a natural number for relevant configs, given that:
  - `c.denseLen` is a `Nat > 0` (and not just a `Nat`).
-/
def FRIConfig.h (c: FRIConfig) : N :=
  (round (log2UB c.denseLen 64)).toNat

/--
  Number of folding rounds.
-/
def FRIConfig.rounds (c: FRIConfig) : N :=
  c.foldingFactors.length

/--
  Enumerates all the soundness errors of a FRI PCS.
-/
def FRIConfig.listErrs (c: FRIConfig) (R: Regime) : List ℚ := do
  let mut l : List ℚ := []
  l := l ++ [c.batchingErr R]
  for i in List.range c.foldingFactors.length do
    l := l ++ [c.commitErr R i]
  l := l ++ [c.queryErr R]
  l

/-! ## FRI proof size -/

/-- Proof size (or expected proof size) of a BCS-transformed FRI interaction in bits.

    Structure:
    * Initial round: one Merkle root + one multi-proof for all `numQueries` queries
      (the `batchSize` initial functions share a single commitment).
    * Each folding round: one root + one multi-proof; siblings are grouped into one
      leaf so `tupleSize = foldingFactor` and `numLeafs = n / foldingFactor`.
    * Final round: the low-degree polynomial sent in the clear
      (`rate * n_final * fieldSizeBits` bits). -/
private def getFRIProofSizeBits (hashSizeBits fieldSizeBits batchSize numQueries domainSize : N)
    (foldingFactors : List N) (rate : Q) (expected : Bool) : N :=
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

def FRIConfig.proofSizeExp (c : FRIConfig) : N :=
  getFRIProofSizeBits c.hashBits c.field.elementSizeBits c.batchSize c.numQueries
    c.D c.foldingFactors (c.ρ : Q) true

def FRIConfig.proofSizeWorst (c : FRIConfig) : N :=
  getFRIProofSizeBits c.hashBits c.field.elementSizeBits c.batchSize c.numQueries
    c.D c.foldingFactors (c.ρ : Q) false

end Soundcalc
