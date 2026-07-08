import Mathlib
import Soundcalc.Regime        -- brings in Rate, Regime, UDR (and Field transitively)
import Soundcalc.Common.Utils  -- getSizeOfMerkleMultiProofBits
import Soundcalc.Field         -- certified koalaBear4.elementSizeBits (= 124)
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
  traceLen       : N
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
  grindCommit    : N             := 0
  gapToRadius    : Option Float  := none

def FRIConfig.batchingErr (c : FRIConfig) (R : Regime) : Q :=
  R.errMultilinear c.ρ c.denseLen c.batchSize / 2 ^ c.grindBatch

def FRIConfig.commitErr (c : FRIConfig) (R : Regime) (i : N) : Q :=
  let acc := (c.foldingFactors.take (i + 1)).foldl (· * ·) 1
  R.errPowers c.ρ (c.denseLen / acc) (c.foldingFactors.getD i 1)

def FRIConfig.queryErr (c : FRIConfig) (R : Regime) : Q :=
  (1 - R.θ c.ρ c.denseLen) ^ c.numQueries / 2 ^ c.grindQuery

/--
  Domain size, after low-degree extension

  **TODO**: formal semantic refinement later.

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
  Note: as remarked in `ZkVM/SP1.lean`, the Python `soundcalc` refers
  to `trace_length` as the *dense* trace length! (our `denseLen`).
  This is confirmed by the renderer.

  **TODO**: semantic refinement later.

  `.toNat` is justified, as `log2UB` is always
  a natural number for relevant configs, given that:
  - `c.denseLen` is a `Nat > 0` (and not just a `Nat`).
-/
def FRIConfig.h (c: FRIConfig) : N :=
  (round (log2UB c.denseLen 64)).toNat

/--
  Number of folding rounds.
  **TODO**: semantic refinement later.
  Python's runtime assert is currently
  modelled as a per-configuration theorem
  `FRIConfig.earlyStop_ok`.
  (e.g., in SP1 core of `ZkVM/SP1.Lean`)
-/
def FRIConfig.rounds (c: FRIConfig) : N :=
  c.foldingFactors.length

/-! ## FRI proof size -/

/-- Proof size (or expected proof size) of a BCS-transformed FRI interaction in bits.

    Structure:
    * Initial round: one Merkle root + one multi-proof for all `numQueries` queries
      (the `batchSize` initial functions share a single commitment).
    * Each folding round: one root + one multi-proof; siblings are grouped into one
      leaf so `tupleSize = foldingFactor` and `numLeafs = n / foldingFactor`.
    * Final round: the low-degree polynomial sent in the clear
      (`rate * n_final * fieldSizeBits` bits). -/

private def getFRIProofSizeBits (c: FRIConfig) (expected: Bool) : ℕ :=
  let hashSizeBits := c.hashBits
  let fieldSizeBits := c.field.elementSizeBits
  let batchSize := c.batchSize
  let numQueries := c.numQueries
  let domainSize := c.D
  let foldingFactors := c.foldingFactors
  let rate := (c.ρ : ℚ) -- casting the rate to a rational to access `.num`/`.den`

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

def FRIConfig.proofSizeExp (c: FRIConfig) : ℕ :=
  getFRIProofSizeBits c true

def FRIConfig.proofSizeWorst (c: FRIConfig) : ℕ :=
  getFRIProofSizeBits c false

end Soundcalc
