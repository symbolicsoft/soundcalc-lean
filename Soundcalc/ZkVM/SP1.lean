import Soundcalc.Circuit.Jagged
import Soundcalc.PCS.FRI
import Soundcalc.Lookup

/-! Field definitions at `Soundcalc` namespace level so that downstream files
    (e.g. `SoundcalcIO.ZkVM.SP1`) can access them via `open Soundcalc`. -/
namespace Soundcalc

/-- The KoalaBear prime: `p = 2^31 - 2^24 + 1`, a Mersenne-like prime chosen for
    efficient Montgomery reduction on 32-bit hardware. -/
def koalaBearPrime : ℕ := 2 ^ 31 - 2 ^ 24 + 1

/-- KoalaBear degree-4 extension field (used in SP1 / Plonky3).
    Element count: `p^4` where `p` is the KoalaBear prime. -/
def koalaBear4 : FieldParams := { card := koalaBearPrime ^ 4 }

end Soundcalc

open Soundcalc
open Soundcalc.Lookup

/-!
# SP1 zkVM — circuit instances

Hand-crafted parameter instances for the three SP1 circuits (core, compress, shrink),
covering all three protocol layers.  Source: `soundcalc/zkvms/sp1/sp1.toml` and
`circuits/jagged.py`.
-/

/-! ## Regime

Concrete instantiation for SP1's FRI-based sumcheck, verifying that the symbolic
formula reduces to the expected closed form and achieves the claimed security level.

Parameters:
* field : KoalaBear degree-4 extension, `|F| = p^4` where `p = 2^31 - 2^24 + 1`
* rate  : `ρ = 1/4`
* dim   : `2^21` (trace column degree)
* batch : `193` rounds, so `⌈log₂ 193⌉ = 8` (since `2^7 = 128 < 193 ≤ 256 = 2^8`)
-/

/-- The `errMultilinear` formula for `(ρ, dim, batch) = (1/4, 2^21, 193)` simplifies to
    `(3/8 · 2^23 + 1) / |F| · 8`.

    Derivation: `θ = (1 - 1/4)/2 = 3/8`, `dim / ρ = 2^21 / (1/4) = 2^23`, `⌈log₂ 193⌉ = 8`. -/
example : (UDR koalaBear4).errMultilinear ⟨1/4, by norm_num⟩ (2 ^ 21) 193
    = (3 / 8 * (2 : ℚ) ^ 23 + 1) / (koalaBear4.card : ℚ) * 8 := by
  have hlog : Nat.clog 2 193 = 8 := by decide
  simp only [UDR, hlog]
  push_cast
  ring

/-- The raw `errMultilinear` value has `secBits = 99`.

    Note: the 104-bit claim in SP1 belongs to `batchingErr`, which divides
    `errMultilinear` by `2 ^ grindBatch = 32`, adding 5 bits (99 + 5 = 104). -/
example : secBits ((UDR koalaBear4).errMultilinear ⟨1/4, by norm_num⟩ (2 ^ 21) 193) = 99 := by
  have hlog : Nat.clog 2 193 = 8 := by decide
  simp only [UDR, hlog]
  push_cast
  norm_num [secBits, koalaBear4, koalaBearPrime]
  native_decide

/-! ## Jagged -/

/-!
Parameters from `circuits/jagged.py`:
* `denseLen = 2^21`, `batchSize = 193` → `ℓ = 21 + 8 = 29`
* `traceWidth = 3741`, `numConstraints = 3412`, `airMaxDegree = 3`
* `traceLength = 2^22` (the "length gotcha": trace rows, not FRI domain size)
-/
def sp1Core : JaggedCfg where
  field          := koalaBear4
  denseLen       := 2 ^ 21
  batchSize      := 193
  traceWidth     := 3741
  traceLength    := 2 ^ 22
  numConstraints := 3412
  airMaxDegree   := 3

/-!
Exit criteria: `secBits (sp1Core.reduceErr) = 116` and `secBits (sp1Core.zerocheckErr) = 112`.

Derivation sketch:
* `ℓ = 29`, numerator of `reduceErr = 12 + 58 + 120 = 190`, `secBits = ⌊log₂(|F|/190)⌋ = 116`
* numerator of `zerocheckErr = 3412 + 5·22 = 3522`, `secBits = ⌊log₂(|F|/3522)⌋ = 112`
-/
example : secBits sp1Core.reduceErr = 116 := by native_decide
example : secBits sp1Core.zerocheckErr = 112 := by native_decide

/-! ## FRI

`denseLen` is the FRI dimension `d`; `n = d/ρ = 2^23`. The trace length
(`2^22`, used by zerocheck) is a *separate* quantity and deliberately
does **not** appear in `FRIConfig`. -/
def sp1CoreFRI : FRIConfig where
  field          := koalaBear4
  ρ              := ⟨1 / 4, by norm_num⟩
  denseLen       := 2 ^ 21
  batchSize      := 193
  numQueries     := 124
  foldingFactors := List.replicate 21 2
  earlyStopDeg   := 4
  grindQuery     := 16
  grindBatch     := 5

/-! Early-stop side condition: `(denseLen / ρ) / ∏ foldingFactors = earlyStopDeg`.

The explicit `ℚ` coercions mirror the spec: `(c.ρ : Q)` extracts the value
from the `Rate` subtype. -/
theorem FRIConfig.earlyStop_ok (c : FRIConfig) (hc : c = sp1CoreFRI) :
    ((c.denseLen : Q) / (c.ρ : Q)) / ((c.foldingFactors.foldl (· * ·) 1 : N) : Q)
      = (c.earlyStopDeg : Q) := by
  subst hc
  simp only [sp1CoreFRI]
  norm_num [show ((List.replicate 21 2).foldl (· * ·) 1 : N) = 2097152 from by decide]

/-! `queryErr = (1 − 3/8)^124 / 2^16 = (5/8)^124 / 2^16`, whose `⌊−log₂⌋` is `100`. -/
example : secBits (sp1CoreFRI.queryErr   (UDR koalaBear4))     = 100 := by native_decide
example : secBits (sp1CoreFRI.batchingErr (UDR koalaBear4))    = 104 := by native_decide
example : secBits (sp1CoreFRI.commitErr  (UDR koalaBear4)  0)  = 103 := by native_decide
example : secBits (sp1CoreFRI.commitErr  (UDR koalaBear4) 20)  = 122 := by native_decide

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

/-! ## Lookup

Parsed from https://github.com/ethereum/soundcalc/blob/main/soundcalc/zkvms/sp1/sp1.toml
-/

def sp1CoreLookup : LookupCfg where
  field           := Field.koalaBear4
  rowsT           := 0
  rowsL           := 4194304    -- 2 ^ 22
  numColumnsS     := 107
  numLookupsM     := 1911
  grindBitsLookup := 12

def sp1CompressLookup : LookupCfg where
  field           := Field.koalaBear4
  rowsT           := 0
  rowsL           := 2097152    -- 2 ^ 21
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

def sp1ShrinkLookup : LookupCfg where
  field           := Field.koalaBear4
  rowsT           := 0
  rowsL           := 524288     -- 2 ^ 19
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

/-! S6 exit criteria: `secBits` evaluates correctly on all three SP1 circuits. -/
theorem sp1_core_lookup_bits : secBits sp1CoreLookup.errUB = 100 := by native_decide
theorem sp1_compress_lookup_bits : secBits sp1CompressLookup.errUB = 107 := by native_decide
theorem sp1_shrink_lookup_bits : secBits sp1ShrinkLookup.errUB = 109 := by native_decide
