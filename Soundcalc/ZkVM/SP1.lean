import Soundcalc.Circuit.Jagged
import Soundcalc.SecBits
import Soundcalc.PCS.FRI
import Soundcalc.Lookup
import Soundcalc.Field.KoalaBear
import Soundcalc.ZkVM

namespace Soundcalc


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
* field : KoalaBear degree-4 extension, `|F| = koalaBear4.card`
* rate  : `ρ = 1/4`
* dim   : `2^21` (trace column degree)
* batch : `193` rounds, so `⌈log₂ 193⌉ = 8` (since `2^7 = 128 < 193 ≤ 256 = 2^8`)
-/

/-- The `errMultilinear` formula for `(ρ, dim, batch) = (1/4, 2^21, 193)` simplifies to
    `(3/8 · 2^23 + 1) / |F| · 8`.

    Derivation: `θ = (1 - 1/4)/2 = 3/8`, `dim / ρ = 2^21 / (1/4) = 2^23`, `⌈log₂ 193⌉ = 8`. -/
example : (UDR koalaBear4).errMultilinear Rate.quarter (2 ^ 21) 193
    = (3 / 8 * (2 : ℚ) ^ 23 + 1) / (koalaBear4.card : ℚ) * 8 := by
  have hlog : Nat.clog 2 193 = 8 := by decide
  simp only [UDR, hlog]
  push_cast
  ring

/-- The raw `errMultilinear` value has `secBits = 99`.

    Note: the 104-bit claim in SP1 belongs to `batchingErr`, which divides
    `errMultilinear` by `2 ^ grindBatch = 32`, adding 5 bits (99 + 5 = 104). -/
example : secBits ((UDR koalaBear4).errMultilinear Rate.quarter (2 ^ 21) 193) = 99 := by
  have hlog : Nat.clog 2 193 = 8 := by decide
  simp only [UDR, hlog]
  push_cast
  norm_num [secBits, koalaBear4, FieldParams.card]
  native_decide

/-! ## FRI

`denseLen` is used to evaluate the FRI domain size `D` as
`FRIConfig.D = denseLen/ρ = 2^23`. The trace length
(`2^22`, used by zerocheck) is a *separate* quantity. -/
def sp1CoreFRI : FRIConfig where
  hashBits       := 248
  field          := koalaBear4
  ρ              := Rate.quarter
  denseLen       := 2 ^ 21
  batchSize      := 193
  powerBatch     := false
  multilinBatch  := true
  numQueries     := 124
  foldingFactors := List.replicate 21 2
  earlyStopDeg   := 4
  grindQuery     := 16
  grindBatch     := 5

/-! `queryErr = (1 − 3/8)^124 / 2^16 = (5/8)^124 / 2^16`, whose `⌊−log₂⌋` is `100`. -/
example : secBits (sp1CoreFRI.queryErr   (UDR koalaBear4))     = 100 := by native_decide
example : secBits (sp1CoreFRI.batchingErr (UDR koalaBear4))    = 104 := by native_decide
example : secBits (sp1CoreFRI.commitErr  (UDR koalaBear4)  0)  = 103 := by native_decide
example : secBits (sp1CoreFRI.commitErr  (UDR koalaBear4) 20)  = 122 := by native_decide

/-! ## FRI proof sizes

Parameters per circuit (from `soundcalc/zkvms/sp1/sp1.toml`):

| circuit  | denseTraceLen | ρ    | domainSize        | batchSize | numQueries | foldRounds |
|----------|---------------|------|-------------------|-----------|------------|------------|
| core     | 2^21          | 1/4  | 2^21/(1/4) = 2^23 | 193       | 124        | 21 × 2     |
| compress | 2^20          | 1/4  | 2^20/(1/4) = 2^22 | 128       | 124        | 20 × 2     |
| shrink   | 2^18          | 1/8  | 2^18/(1/8) = 2^21 | 128       | 94         | 18 × 2     |

`hashSizeBits = 248` for all three.
Sizes are floor-divided by `KIB = 8192` to match the KiB figures in the report.
-/

/-! ## FRI proof size exit criteria -/

def sp1CompressFRI : FRIConfig where
  hashBits        := 248
  ρ               := Rate.quarter
  field           := koalaBear4
  denseLen        := 1048576
  batchSize       := 128
  powerBatch      := false
  multilinBatch   := true
  numQueries      := 124
  foldingFactors  := List.replicate 20 2
  earlyStopDeg    := 4
  grindQuery      := 16
  grindBatch      := 5

def sp1ShrinkFRI : FRIConfig where
  hashBits        := 248
  ρ               := Rate.eighth
  field           := koalaBear4
  denseLen        := 262144
  batchSize       := 128
  powerBatch      := false
  multilinBatch   := true
  numQueries      := 94
  foldingFactors  := List.replicate 18 2
  earlyStopDeg    := 8
  grindQuery      := 22
  grindBatch      := 5

-- FRI-only sizes (matching the Python get_FRI_proof_size_bits):
-- core: 913 KiB (expected) / 1474 KiB (worst case)
example : sp1CoreFRI.proofSizeExp       / KIB = 913  := by native_decide
example : sp1CoreFRI.proofSizeWorst     / KIB = 1474 := by native_decide
-- compress: 730 KiB (expected) / 1261 KiB (worst case)
example : sp1CompressFRI.proofSizeExp   / KIB = 730  := by native_decide
example : sp1CompressFRI.proofSizeWorst / KIB = 1261 := by native_decide
-- shrink: 524 KiB (expected) / 882 KiB (worst case)
example : sp1ShrinkFRI.proofSizeExp     / KIB = 524  := by native_decide
example : sp1ShrinkFRI.proofSizeWorst   / KIB = 882  := by native_decide

/-! ## Lookup

Parsed from https://github.com/ethereum/soundcalc/blob/main/soundcalc/zkvms/sp1/sp1.toml
-/

def sp1CoreLookup : LookupCfg where
  name            := "lookup"
  field           := koalaBear4
  isLogUpMultivar := true
  rowsT           := 0
  rowsL           := 4194304    -- 2 ^ 22
  numColumnsS     := 107
  numLookupsM     := 1911
  grindBitsLookup := 12

def sp1CompressLookup : LookupCfg where
  name            := "lookup"
  field           := koalaBear4
  isLogUpMultivar := true
  rowsT           := 0
  rowsL           := 2097152    -- 2 ^ 21
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

def sp1ShrinkLookup : LookupCfg where
  name            := "lookup"
  field           := koalaBear4
  isLogUpMultivar := true
  rowsT           := 0
  rowsL           := 524288     -- 2 ^ 19
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

/-! ## Jagged -/

/-!
Parameters from `circuits/jagged.py`:
* `denseLen = 2^21`, `batchSize = 193` → `ℓ = 21 + 8 = 29`
* `traceWidth = 3741`, `numConstraints = 3412`, `airMaxDegree = 3`
* `traceLength = 2^22` (the "length gotcha": trace rows, not FRI domain size)
-/
def sp1CoreJagged : JaggedCfg where
  name           := "core"
  field          := koalaBear4
  densePCS       := .fri sp1CoreFRI
  traceWidth     := 3741
  traceLength    := 2 ^ 22
  numConstraints := 3412
  airMaxDegree   := 3
  lookups        := [sp1CoreLookup]

/-!
Core cell derivation (asserted below in `sp1CoreJagged.ExitCriteria`):
* `ℓ = 29`, numerator of `reduceErr = 12 + 58 + 120 = 190`, `secBits = ⌊log₂(|F|/190)⌋ = 116`
* numerator of `zerocheckErr = 3412 + 5·22 = 3522`, `secBits = ⌊log₂(|F|/3522)⌋ = 112`
-/

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

def sp1CompressJagged : JaggedCfg where
  name            := "compress"
  field           := koalaBear4
  densePCS        := .fri sp1CompressFRI
  traceLength     := 2097152
  traceWidth      := 326
  numConstraints  := 204
  airMaxDegree    := 3
  lookups         := [sp1CompressLookup]

def sp1ShrinkJagged : JaggedCfg where
  name            := "shrink"
  field           := koalaBear4
  densePCS        := .fri sp1ShrinkFRI
  traceLength     := 524288
  traceWidth      := 326
  numConstraints  := 204
  airMaxDegree    := 3
  lookups         := [sp1ShrinkLookup]

/-!
  S6 exit criteria: `secBits` evaluates correctly on all three SP1 circuits.
  Used within `scripts/AxiomsGuard.lean`
-/
theorem sp1_core_lookup_bits : secBits sp1CoreLookup.errUB = 100 := by native_decide

/-! ## Jagged exit criteria (bundled)

One `JaggedCfg.ExitCriteria` per circuit replaces the scattered reduce/zerocheck, lookup-bit,
and proof-size `example`s. Row entries: query | batching | reduce | zerocheck | commit×folds |
lookup. Cross-checked against <https://github.com/ethereum/soundcalc/blob/main/reports/sp1.md>. -/

-- core: 918 KiB (expected) / 1479 KiB (worst case)
example : sp1CoreJagged.ExitCriteria
    (reduceBits := 116) (zerocheckBits := 112) (lookupBits := [100])
    (rowBits := [116, 112, 104, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
                  114, 115, 116, 117, 118, 119, 120, 121, 121, 122, 100, 100])
    (totalBits := 100)
    (proofSizeExpKib := 918) (proofSizeWorstKib := 1479) := by
  native_decide

-- compress: 735 KiB (expected) / 1267 KiB (worst case)
example : sp1CompressJagged.ExitCriteria
    (reduceBits := 116) (zerocheckBits := 115) (lookupBits := [107])
    (rowBits := [116, 115, 105, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
                  115, 116, 117, 118, 119, 120, 121, 121, 122, 100, 107])
    (totalBits := 100)
    (proofSizeExpKib := 735) (proofSizeWorstKib := 1267) := by
  native_decide


-- shrink: 529 KiB (expected) / 887 KiB (worst case)
example : sp1ShrinkJagged.ExitCriteria
    (reduceBits := 116) (zerocheckBits := 115) (lookupBits := [109])
    (rowBits := [116, 115, 106, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
                  116, 117, 118, 119, 120, 120, 121, 100, 109])
    (totalBits := 100)
    (proofSizeExpKib := 529) (proofSizeWorstKib := 887) := by
  native_decide

/-! ## SP1 (all circuits)

Bundles all of SP1's circuits into the generic `ZkVM` (`Soundcalc.ZkVM`). Each
`JaggedCfg` already enforces its own FRI/lookup field consistency
(`h_densePCS_field`/`h_lookups_field`); `ZkVM.h_circuits_field` additionally
enforces that every circuit agrees with the zkVM's own `field`. Metadata from
`soundcalc/zkvms/sp1/sp1.toml`'s `[zkevm]` section. -/
def sp1 : ZkVM where
  name         := "SP1"
  field        := koalaBear4
  version      := "6.1.0"
  circuits     := [.jagged sp1CoreJagged,
                   .jagged sp1CompressJagged,
                   .jagged sp1ShrinkJagged]

end Soundcalc
