import Soundcalc.Circuit.DeepAli
import Soundcalc.PCS.FRI
import Soundcalc.Lookup
import Soundcalc.Field.Goldilocks

/-!
# ZisK soundness configuration

ZisK is a DEEP-ALI zkVM (over Goldilocks³), so — like Pico — it only needs
`Soundcalc.Circuit.DeepAli`. Every literal below is derived from
`soundcalc/zkvms/zisk/zisk.toml` and cross-checked, cell by cell, against
`reports/zisk.md` (<https://github.com/ethereum/soundcalc/blob/main/reports/zisk.md>).

## Two-regime strategy

* **UDR** (`ziskUDR`): classical unique-decoding threshold, shared by every circuit.
* **JBR**: Johnson Bound Regime. Unlike Airbender/OpenVM/Pico — which leave the gap
  to BCHKS25's default formula — every ZisK circuit **pins** its gap via
  `gap_to_radius`. In `soundcalc`'s `get_proximity_parameter` the proximity
  parameter is `1 - √ρ - gap`; here the variable named `η` *is that gap* (note
  `θ = (1 - η) - √ρ`), so pinning `gap_to_radius` means passing `JBR`'s optional
  `gapToRadius = some gap`, collapsing `etaLB = etaUB = gap`. Every ZisK
  `gap_to_radius` is an exact multiple of `1/3000`.

`g = 2^40` is the same `√ρ`-enclosure granularity used by Airbender/OpenVM/Pico.
-/

namespace Soundcalc

/-! ## Zisk config constructors

Each circuit's `FRIConfig`/`LookupCfg`/`JBR` regime shares the same Goldilocks constants; these
helpers bake those in so every instance below is a one-liner. Each call still produces a *separate*
object, free to diverge later. -/

/-- `JBR` over Goldilocks, `g = 2^40`, `gap = n/3000`. -/
abbrev ziskJBR (n : ℕ) : Regime := JBR goldilocks3 (2 ^ 40) (some (n / 3000))

/-- Univariate-logup lookup over Goldilocks, no grinding. -/
abbrev ziskLookup (name : String) (rowsT rowsL numColumnsS numLookupsM : ℕ) : LookupCfg where
  name := name; field := goldilocks3; isLogUpMultivar := false
  rowsT := rowsT; rowsL := rowsL; numColumnsS := numColumnsS; numLookupsM := numLookupsM
  grindBitsLookup := 0

/-- FRI over Goldilocks: power batching, 256-bit hash, no batch/commit grinding.
    `h_earlyStop` is an auto-param, so it is discharged by `native_decide` on the *concrete*
    arguments at each call site (it cannot be proved from the symbolic parameters here). -/
abbrev ziskFRI (ρ : Rate) (denseLen batchSize numQueries earlyStopDeg grindQuery : ℕ)
    (foldingFactors : List ℕ)
    (h_earlyStop :
      ((denseLen : Q) / (ρ : Q)) / ((foldingFactors.foldl (· * ·) 1 : N) : Q) = (earlyStopDeg : Q)
      := by native_decide) : FRIConfig where
  hashBits := 256; field := goldilocks3; ρ := ρ
  denseLen := denseLen; batchSize := batchSize; numQueries := numQueries
  foldingFactors := foldingFactors; earlyStopDeg := earlyStopDeg
  powerBatch := true; multilinBatch := false
  grindQuery := grindQuery; grindBatch := 0; grindCommit := 0
  h_earlyStop := h_earlyStop

/-! ## Regimes -/

abbrev ziskUDR : Regime := UDR goldilocks3

/-- `Dma`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDmaJBR := ziskJBR 16
/-- `DmaMemCpy`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskDmaMemCpyJBR := ziskJBR 15
/-- `DmaInputCpy`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskDmaInputCpyJBR := ziskJBR 14
/-- `Dma64Aligned`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskDma64AlignedJBR := ziskJBR 17
/-- `Dma64AlignedInputCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDma64AlignedInputCpyJBR := ziskJBR 16
/-- `Dma64AlignedMemSet`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskDma64AlignedMemSetJBR := ziskJBR 15
/-- `Dma64AlignedMem`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDma64AlignedMemJBR := ziskJBR 16
/-- `Dma64AlignedMemCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDma64AlignedMemCpyJBR := ziskJBR 16
/-- `DmaUnaligned`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDmaUnalignedJBR := ziskJBR 16
/-- `DmaPrePost`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskDmaPrePostJBR := ziskJBR 18
/-- `DmaPrePostMemCpy`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskDmaPrePostMemCpyJBR := ziskJBR 17
/-- `DmaPrePostInputCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDmaPrePostInputCpyJBR := ziskJBR 16
/-- `Main`: gap_to_radius = 0.006333333333333333 = 19/3000. -/
abbrev ziskMainJBR := ziskJBR 19
/-- `Rom`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskRomJBR := ziskJBR 15
/-- `Mem`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskMemJBR := ziskJBR 17
/-- `RomData`: gap_to_radius = 0.004333333333333333 = 13/3000. -/
abbrev ziskRomDataJBR := ziskJBR 13
/-- `InputData`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskInputDataJBR := ziskJBR 14
/-- `MemAlign`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskMemAlignJBR := ziskJBR 17
/-- `MemAlignByte`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskMemAlignByteJBR := ziskJBR 16
/-- `MemAlignReadByte`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskMemAlignReadByteJBR := ziskJBR 15
/-- `MemAlignWriteByte`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskMemAlignWriteByteJBR := ziskJBR 16
/-- `Arith`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskArithJBR := ziskJBR 17
/-- `Binary`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskBinaryJBR := ziskJBR 18
/-- `BinaryAdd`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskBinaryAddJBR := ziskJBR 15
/-- `BinaryExtension`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskBinaryExtensionJBR := ziskJBR 18
/-- `Add256`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskAdd256JBR := ziskJBR 15
/-- `ArithEq`: gap_to_radius = 0.007333333333333333 = 22/3000. -/
abbrev ziskArithEqJBR := ziskJBR 22
/-- `ArithEq384`: gap_to_radius = 0.007666666666666666 = 23/3000. -/
abbrev ziskArithEq384JBR := ziskJBR 23
/-- `Keccakf`: gap_to_radius = 0.007333333333333333 = 22/3000. -/
abbrev ziskKeccakfJBR := ziskJBR 22
/-- `Sha256f`: gap_to_radius = 0.006666666666666666 = 20/3000. -/
abbrev ziskSha256fJBR := ziskJBR 20
/-- `Poseidon2`: gap_to_radius = 0.004 = 12/3000. -/
abbrev ziskPoseidon2JBR := ziskJBR 12
/-- `Blake2br`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskBlake2brJBR := ziskJBR 18
/-- `SpecifiedRanges`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskSpecifiedRangesJBR := ziskJBR 16
/-- `VirtualTable0`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskVirtualTable0JBR := ziskJBR 17
/-- `VirtualTable1`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskVirtualTable1JBR := ziskJBR 18
/-- `DmaPrePost-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskDmaPrePostCompressorJBR := ziskJBR 14
/-- `ArithEq-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskArithEqCompressorJBR := ziskJBR 14
/-- `ArithEq384-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskArithEq384CompressorJBR := ziskJBR 14
/-- `Keccakf-compressor`: gap_to_radius = 0.006333333333333333 = 19/3000. -/
abbrev ziskKeccakfCompressorJBR := ziskJBR 19
/-- `Sha256f-compressor`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskSha256fCompressorJBR := ziskJBR 16
/-- `Blake2br-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskBlake2brCompressorJBR := ziskJBR 14
/-- `Recursive2`: gap_to_radius = 0.004 = 12/3000. -/
abbrev ziskRecursive2JBR := ziskJBR 12
/-- `Final`: gap_to_radius = 0.003333333333333333 = 10/3000. -/
abbrev ziskFinalJBR := ziskJBR 10
/-- `Final_Compressed`: gap_to_radius = 0.003333333333333333 = 10/3000. -/
abbrev ziskFinalCompressedJBR := ziskJBR 10

/-! ## Dma -/

def ziskDmaFRI := ziskFRI Rate.half 2097152 46 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1
def ziskDmaLookupGsum77 := ziskLookup "Lookup_gsum_[77]" 0 2097152 2 1
def ziskDmaLookupGsum8001 := ziskLookup "Lookup_gsum_[8001]" 0 2097152 7 1
def ziskDmaPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 1
def ziskDmaPermutationGsum8000 := ziskLookup "Permutation_gsum_[8000]" 0 2097152 11 2
def ziskDmaRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 1
def ziskDmaRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2
def ziskDmaRangeCheckGsum104 := ziskLookup "Range Check_gsum_[104]" 0 2097152 1 2

def ziskDmaDeepAli : DeepAliCfg where
  name           := "Dma"
  field          := goldilocks3
  densePCS       := .fri ziskDmaFRI
  numConstraints := 49
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaLookupGsum5000,
                     ziskDmaLookupGsum77,
                     ziskDmaLookupGsum8001,
                     ziskDmaPermutationGsum10,
                     ziskDmaPermutationGsum8000,
                     ziskDmaRangeCheckGsum102,
                     ziskDmaRangeCheckGsum103,
                     ziskDmaRangeCheckGsum104]

-- Dma: 748 KiB (expected) / 1142 KiB (worst case).
example : ziskDmaDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 166, 169, 168, 168,
                166, 170, 169, 169])
    (totalBits := 111)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  native_decide
example : ziskDmaDeepAli.ExitCriteria ziskDmaJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 179, 161, 166, 169, 168, 168,
                166, 170, 169, 169])
    (totalBits := 128)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  native_decide

/-! ## DmaMemCpy -/

def ziskDmaMemCpyFRI := ziskFRI Rate.half 2097152 33 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaMemCpyLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1
def ziskDmaMemCpyLookupGsum77 := ziskLookup "Lookup_gsum_[77]" 0 2097152 2 1
def ziskDmaMemCpyLookupGsum8001 := ziskLookup "Lookup_gsum_[8001]" 0 2097152 7 1
def ziskDmaMemCpyPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 1
def ziskDmaMemCpyPermutationGsum8000 := ziskLookup "Permutation_gsum_[8000]" 0 2097152 11 2
def ziskDmaMemCpyRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 1
def ziskDmaMemCpyRangeCheckGsum104 := ziskLookup "Range Check_gsum_[104]" 0 2097152 1 2

def ziskDmaMemCpyDeepAli : DeepAliCfg where
  name           := "DmaMemCpy"
  field          := goldilocks3
  densePCS       := .fri ziskDmaMemCpyFRI
  numConstraints := 22
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaMemCpyLookupGsum5000,
                     ziskDmaMemCpyLookupGsum77,
                     ziskDmaMemCpyLookupGsum8001,
                     ziskDmaMemCpyPermutationGsum10,
                     ziskDmaMemCpyPermutationGsum8000,
                     ziskDmaMemCpyRangeCheckGsum102,
                     ziskDmaMemCpyRangeCheckGsum104]

-- DmaMemCpy: 679 KiB (expected) / 1072 KiB (worst case).
example : ziskDmaMemCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 187, 168, 166, 169, 168, 168,
                166, 170, 169])
    (totalBits := 111)
    (proofSizeExpKib := 679) (proofSizeWorstKib := 1072) := by
  native_decide
example : ziskDmaMemCpyDeepAli.ExitCriteria ziskDmaMemCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 180, 161, 166, 169, 168, 168,
                166, 170, 169])
    (totalBits := 128)
    (proofSizeExpKib := 679) (proofSizeWorstKib := 1072) := by
  native_decide

/-! ## DmaInputCpy -/

def ziskDmaInputCpyFRI := ziskFRI Rate.half 2097152 27 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaInputCpyLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1
def ziskDmaInputCpyLookupGsum8001 := ziskLookup "Lookup_gsum_[8001]" 0 2097152 7 1
def ziskDmaInputCpyPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 1
def ziskDmaInputCpyPermutationGsum8000 := ziskLookup "Permutation_gsum_[8000]" 0 2097152 11 2
def ziskDmaInputCpyRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 1
def ziskDmaInputCpyRangeCheckGsum104 := ziskLookup "Range Check_gsum_[104]" 0 2097152 1 1
def ziskDmaInputCpyRangeCheckGsum105 := ziskLookup "Range Check_gsum_[105]" 0 2097152 1 1

def ziskDmaInputCpyDeepAli : DeepAliCfg where
  name           := "DmaInputCpy"
  field          := goldilocks3
  densePCS       := .fri ziskDmaInputCpyFRI
  numConstraints := 20
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaInputCpyLookupGsum5000,
                     ziskDmaInputCpyLookupGsum8001,
                     ziskDmaInputCpyPermutationGsum10,
                     ziskDmaInputCpyPermutationGsum8000,
                     ziskDmaInputCpyRangeCheckGsum102,
                     ziskDmaInputCpyRangeCheckGsum104,
                     ziskDmaInputCpyRangeCheckGsum105]

-- DmaInputCpy: 646 KiB (expected) / 1040 KiB (worst case).
example : ziskDmaInputCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [166, 168, 168, 166, 170, 170, 170])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 166, 168, 168, 166,
                170, 170, 170])
    (totalBits := 111)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  native_decide
example : ziskDmaInputCpyDeepAli.ExitCriteria ziskDmaInputCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [166, 168, 168, 166, 170, 170, 170])
    (rowBits := [133, 137, 140, 143, 146, 149, 153, 128, 180, 161, 166, 168, 168, 166,
                170, 170, 170])
    (totalBits := 128)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  native_decide

/-! ## Dma64Aligned -/

def ziskDma64AlignedFRI := ziskFRI Rate.half 2097152 62 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskDma64AlignedDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 2097152 11 1
def ziskDma64AlignedDirectGsum8200 := ziskLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def ziskDma64AlignedLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def ziskDma64AlignedLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 2097152 2 4
def ziskDma64AlignedPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 9
def ziskDma64AlignedRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 8
def ziskDma64AlignedRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2

def ziskDma64AlignedDeepAli : DeepAliCfg where
  name           := "Dma64Aligned"
  field          := goldilocks3
  densePCS       := .fri ziskDma64AlignedFRI
  numConstraints := 88
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDma64AlignedDirectGsum5000,
                     ziskDma64AlignedDirectGsum8200,
                     ziskDma64AlignedLookupGsum5000,
                     ziskDma64AlignedLookupGsum88,
                     ziskDma64AlignedPermutationGsum10,
                     ziskDma64AlignedRangeCheckGsum102,
                     ziskDma64AlignedRangeCheckGsum103]

-- Dma64Aligned: 838 KiB (expected) / 1233 KiB (worst case).
example : ziskDma64AlignedDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 167, 165, 167, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 167,
                165, 167, 169])
    (totalBits := 111)
    (proofSizeExpKib := 838) (proofSizeWorstKib := 1233) := by
  native_decide
example : ziskDma64AlignedDeepAli.ExitCriteria ziskDma64AlignedJBR
    (aliBits := 178) (deepBits := 162)
    (lookupBits := [167, 166, 167, 167, 165, 167, 169])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 178, 162, 167, 166, 167, 167,
                165, 167, 169])
    (totalBits := 128)
    (proofSizeExpKib := 838) (proofSizeWorstKib := 1233) := by
  native_decide

/-! ## Dma64AlignedInputCpy -/

def ziskDma64AlignedInputCpyFRI := ziskFRI Rate.half 2097152 44 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDma64AlignedInputCpyDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 2097152 11 1
def ziskDma64AlignedInputCpyDirectGsum8200 := ziskLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def ziskDma64AlignedInputCpyLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def ziskDma64AlignedInputCpyLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 2097152 2 4
def ziskDma64AlignedInputCpyPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 4
def ziskDma64AlignedInputCpyRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 8
def ziskDma64AlignedInputCpyRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2

def ziskDma64AlignedInputCpyDeepAli : DeepAliCfg where
  name           := "Dma64AlignedInputCpy"
  field          := goldilocks3
  densePCS       := .fri ziskDma64AlignedInputCpyFRI
  numConstraints := 52
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDma64AlignedInputCpyDirectGsum5000,
                     ziskDma64AlignedInputCpyDirectGsum8200,
                     ziskDma64AlignedInputCpyLookupGsum5000,
                     ziskDma64AlignedInputCpyLookupGsum88,
                     ziskDma64AlignedInputCpyPermutationGsum10,
                     ziskDma64AlignedInputCpyRangeCheckGsum102,
                     ziskDma64AlignedInputCpyRangeCheckGsum103]

-- Dma64AlignedInputCpy: 738 KiB (expected) / 1131 KiB (worst case).
example : ziskDma64AlignedInputCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [167, 166, 167, 167, 166, 167, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 167, 166, 167, 167,
                166, 167, 169])
    (totalBits := 111)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  native_decide
example : ziskDma64AlignedInputCpyDeepAli.ExitCriteria ziskDma64AlignedInputCpyJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [167, 166, 167, 167, 166, 167, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 179, 161, 167, 166, 167, 167,
                166, 167, 169])
    (totalBits := 128)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  native_decide

/-! ## Dma64AlignedMemSet -/

def ziskDma64AlignedMemSetFRI := ziskFRI Rate.half 2097152 30 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDma64AlignedMemSetDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 2097152 11 1
def ziskDma64AlignedMemSetDirectGsum8200 := ziskLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def ziskDma64AlignedMemSetLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def ziskDma64AlignedMemSetPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 8
def ziskDma64AlignedMemSetRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2

def ziskDma64AlignedMemSetDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMemSet"
  field          := goldilocks3
  densePCS       := .fri ziskDma64AlignedMemSetFRI
  numConstraints := 62
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDma64AlignedMemSetDirectGsum5000,
                     ziskDma64AlignedMemSetDirectGsum8200,
                     ziskDma64AlignedMemSetLookupGsum5000,
                     ziskDma64AlignedMemSetPermutationGsum10,
                     ziskDma64AlignedMemSetRangeCheckGsum103]

-- Dma64AlignedMemSet: 662 KiB (expected) / 1056 KiB (worst case).
example : ziskDma64AlignedMemSetDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 186, 168, 167, 166, 167, 165,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 662) (proofSizeWorstKib := 1056) := by
  native_decide
example : ziskDma64AlignedMemSetDeepAli.ExitCriteria ziskDma64AlignedMemSetJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 178, 161, 167, 166, 167, 165,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 662) (proofSizeWorstKib := 1056) := by
  native_decide

/-! ## Dma64AlignedMem -/

def ziskDma64AlignedMemFRI := ziskFRI Rate.half 2097152 46 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDma64AlignedMemDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 2097152 11 1
def ziskDma64AlignedMemDirectGsum8200 := ziskLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def ziskDma64AlignedMemLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def ziskDma64AlignedMemPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 9
def ziskDma64AlignedMemRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2

def ziskDma64AlignedMemDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMem"
  field          := goldilocks3
  densePCS       := .fri ziskDma64AlignedMemFRI
  numConstraints := 81
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDma64AlignedMemDirectGsum5000,
                     ziskDma64AlignedMemDirectGsum8200,
                     ziskDma64AlignedMemLookupGsum5000,
                     ziskDma64AlignedMemPermutationGsum10,
                     ziskDma64AlignedMemRangeCheckGsum103]

-- Dma64AlignedMem: 748 KiB (expected) / 1142 KiB (worst case).
example : ziskDma64AlignedMemDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 165,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  native_decide
example : ziskDma64AlignedMemDeepAli.ExitCriteria ziskDma64AlignedMemJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 166, 167, 165,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  native_decide

/-! ## Dma64AlignedMemCpy -/

def ziskDma64AlignedMemCpyFRI := ziskFRI Rate.half 2097152 52 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDma64AlignedMemCpyDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 2097152 11 1
def ziskDma64AlignedMemCpyDirectGsum8200 := ziskLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def ziskDma64AlignedMemCpyLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def ziskDma64AlignedMemCpyPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 17
def ziskDma64AlignedMemCpyRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2

def ziskDma64AlignedMemCpyDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMemCpy"
  field          := goldilocks3
  densePCS       := .fri ziskDma64AlignedMemCpyFRI
  numConstraints := 69
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDma64AlignedMemCpyDirectGsum5000,
                     ziskDma64AlignedMemCpyDirectGsum8200,
                     ziskDma64AlignedMemCpyLookupGsum5000,
                     ziskDma64AlignedMemCpyPermutationGsum10,
                     ziskDma64AlignedMemCpyRangeCheckGsum103]

-- Dma64AlignedMemCpy: 781 KiB (expected) / 1174 KiB (worst case).
example : ziskDma64AlignedMemCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 164, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 164,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  native_decide
example : ziskDma64AlignedMemCpyDeepAli.ExitCriteria ziskDma64AlignedMemCpyJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 164, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 166, 167, 164,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  native_decide

/-! ## DmaUnaligned -/

def ziskDmaUnalignedFRI := ziskFRI Rate.half 2097152 52 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaUnalignedDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 2097152 11 1
def ziskDmaUnalignedDirectGsum8201 := ziskLookup "Direct_gsum_[8201]" 2097152 2097152 18 1
def ziskDmaUnalignedLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def ziskDmaUnalignedLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 2097152 2 4
def ziskDmaUnalignedPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 2097152 2097152 6 2
def ziskDmaUnalignedRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 2

def ziskDmaUnalignedDeepAli : DeepAliCfg where
  name           := "DmaUnaligned"
  field          := goldilocks3
  densePCS       := .fri ziskDmaUnalignedFRI
  numConstraints := 75
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaUnalignedDirectGsum5000,
                     ziskDmaUnalignedDirectGsum8201,
                     ziskDmaUnalignedLookupGsum5000,
                     ziskDmaUnalignedLookupGsum88,
                     ziskDmaUnalignedPermutationGsum10,
                     ziskDmaUnalignedRangeCheckGsum103]

-- DmaUnaligned: 781 KiB (expected) / 1174 KiB (worst case).
example : ziskDmaUnalignedDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 165, 167, 167, 166, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 165, 167, 167,
                166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  native_decide
example : ziskDmaUnalignedDeepAli.ExitCriteria ziskDmaUnalignedJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 165, 167, 167, 166, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 165, 167, 167,
                166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  native_decide

/-! ## DmaPrePost -/

def ziskDmaPrePostFRI := ziskFRI Rate.half 2097152 83 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaPrePostLookupGsum8002 := ziskLookup "Lookup_gsum_[8002]" 0 2097152 6 1
def ziskDmaPrePostLookupGsum8003 := ziskLookup "Lookup_gsum_[8003]" 0 2097152 3 1
def ziskDmaPrePostLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 2097152 2 12
def ziskDmaPrePostPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 4
def ziskDmaPrePostPermutationGsum8000 := ziskLookup "Permutation_gsum_[8000]" 2097152 0 11 1

def ziskDmaPrePostDeepAli : DeepAliCfg where
  name           := "DmaPrePost"
  field          := goldilocks3
  densePCS       := .fri ziskDmaPrePostFRI
  numConstraints := 69
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaPrePostLookupGsum8002,
                     ziskDmaPrePostLookupGsum8003,
                     ziskDmaPrePostLookupGsum88,
                     ziskDmaPrePostPermutationGsum10,
                     ziskDmaPrePostPermutationGsum8000]

-- DmaPrePost: 951 KiB (expected) / 1346 KiB (worst case).
example : ziskDmaPrePostDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [168, 169, 166, 166, 167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 185, 168, 168, 169, 166, 166,
                167])
    (totalBits := 111)
    (proofSizeExpKib := 951) (proofSizeWorstKib := 1346) := by
  native_decide
example : ziskDmaPrePostDeepAli.ExitCriteria ziskDmaPrePostJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 169, 166, 166, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 155, 128, 179, 162, 168, 169, 166, 166,
                167])
    (totalBits := 128)
    (proofSizeExpKib := 951) (proofSizeWorstKib := 1346) := by
  native_decide

/-! ## DmaPrePostMemCpy -/

def ziskDmaPrePostMemCpyFRI := ziskFRI Rate.half 2097152 70 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaPrePostMemCpyLookupGsum8002 := ziskLookup "Lookup_gsum_[8002]" 0 2097152 6 1
def ziskDmaPrePostMemCpyLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 2097152 2 12
def ziskDmaPrePostMemCpyPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 4
def ziskDmaPrePostMemCpyPermutationGsum8000 := ziskLookup "Permutation_gsum_[8000]" 2097152 0 11 1

def ziskDmaPrePostMemCpyDeepAli : DeepAliCfg where
  name           := "DmaPrePostMemCpy"
  field          := goldilocks3
  densePCS       := .fri ziskDmaPrePostMemCpyFRI
  numConstraints := 38
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaPrePostMemCpyLookupGsum8002,
                     ziskDmaPrePostMemCpyLookupGsum88,
                     ziskDmaPrePostMemCpyPermutationGsum10,
                     ziskDmaPrePostMemCpyPermutationGsum8000]

-- DmaPrePostMemCpy: 881 KiB (expected) / 1276 KiB (worst case).
example : ziskDmaPrePostMemCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [168, 166, 166, 167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 186, 168, 168, 166, 166, 167])
    (totalBits := 111)
    (proofSizeExpKib := 881) (proofSizeWorstKib := 1276) := by
  native_decide
example : ziskDmaPrePostMemCpyDeepAli.ExitCriteria ziskDmaPrePostMemCpyJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 166, 166, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 168, 166, 166, 167])
    (totalBits := 128)
    (proofSizeExpKib := 881) (proofSizeWorstKib := 1276) := by
  native_decide

/-! ## DmaPrePostInputCpy -/

def ziskDmaPrePostInputCpyFRI := ziskFRI Rate.half 2097152 44 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskDmaPrePostInputCpyLookupGsum8002 := ziskLookup "Lookup_gsum_[8002]" 0 2097152 6 1
def ziskDmaPrePostInputCpyLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 2097152 2 8
def ziskDmaPrePostInputCpyPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 2
def ziskDmaPrePostInputCpyPermutationGsum8000 := ziskLookup "Permutation_gsum_[8000]" 2097152 0 11 1

def ziskDmaPrePostInputCpyDeepAli : DeepAliCfg where
  name           := "DmaPrePostInputCpy"
  field          := goldilocks3
  densePCS       := .fri ziskDmaPrePostInputCpyFRI
  numConstraints := 20
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskDmaPrePostInputCpyLookupGsum8002,
                     ziskDmaPrePostInputCpyLookupGsum88,
                     ziskDmaPrePostInputCpyPermutationGsum10,
                     ziskDmaPrePostInputCpyPermutationGsum8000]

-- DmaPrePostInputCpy: 738 KiB (expected) / 1131 KiB (worst case).
example : ziskDmaPrePostInputCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [168, 166, 167, 167])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 187, 168, 168, 166, 167, 167])
    (totalBits := 111)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  native_decide
example : ziskDmaPrePostInputCpyDeepAli.ExitCriteria ziskDmaPrePostInputCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [168, 166, 167, 167])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 180, 161, 168, 166, 167, 167])
    (totalBits := 128)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  native_decide

/-! ## Main -/

def ziskMainFRI := ziskFRI Rate.half 4194304 61 230 32 16 [8, 8, 8, 8, 8, 8]

def ziskMainDirectGsum1000 := ziskLookup "Direct_gsum_[1000]" 4194304 4194304 5 1
def ziskMainLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 0 4194304 11 1
def ziskMainLookupGsum7890 := ziskLookup "Lookup_gsum_[7890]" 0 4194304 11 1
def ziskMainPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 4194304 4194304 6 34
def ziskMainRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 4194304 1 34
def ziskMainRangeCheckGsum106 := ziskLookup "Range Check_gsum_[106]" 0 4194304 1 1

def ziskMainDeepAli : DeepAliCfg where
  name           := "Main"
  field          := goldilocks3
  densePCS       := .fri ziskMainFRI
  numConstraints := 144
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMainDirectGsum1000,
                     ziskMainLookupGsum5000,
                     ziskMainLookupGsum7890,
                     ziskMainPermutationGsum10,
                     ziskMainRangeCheckGsum102,
                     ziskMainRangeCheckGsum106]

-- Main: 890 KiB (expected) / 1292 KiB (worst case).
example : ziskMainDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 167)
    (lookupBits := [166, 166, 166, 161, 164, 169])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 184, 167, 166, 166, 166, 161,
                164, 169])
    (totalBits := 111)
    (proofSizeExpKib := 890) (proofSizeWorstKib := 1292) := by
  native_decide
example : ziskMainDeepAli.ExitCriteria ziskMainJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [166, 166, 166, 161, 164, 169])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 178, 161, 166, 166, 166, 161,
                164, 169])
    (totalBits := 128)
    (proofSizeExpKib := 890) (proofSizeWorstKib := 1292) := by
  native_decide

/-! ## Rom -/

def ziskRomFRI := ziskFRI Rate.half 4194304 18 221 32 20 [8, 8, 8, 8, 8, 8]

def ziskRomLookupGsum7890 := ziskLookup "Lookup_gsum_[7890]" 4194304 0 11 1

def ziskRomDeepAli : DeepAliCfg where
  name           := "Rom"
  field          := goldilocks3
  densePCS       := .fri ziskRomFRI
  numConstraints := 3
  airMaxDegree   := 2
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskRomLookupGsum7890]

-- Rom: 635 KiB (expected) / 1019 KiB (worst case).
example : ziskRomDeepAli.ExitCriteria ziskUDR
    (aliBits := 190) (deepBits := 168)
    (lookupBits := [166])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 190, 168, 166])
    (totalBits := 111)
    (proofSizeExpKib := 635) (proofSizeWorstKib := 1019) := by
  native_decide
example : ziskRomDeepAli.ExitCriteria ziskRomJBR
    (aliBits := 183) (deepBits := 161)
    (lookupBits := [166])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 183, 161, 166])
    (totalBits := 128)
    (proofSizeExpKib := 635) (proofSizeWorstKib := 1019) := by
  native_decide

/-! ## Mem -/

def ziskMemFRI := ziskFRI Rate.half 4194304 29 230 32 16 [8, 8, 8, 8, 8, 8]

def ziskMemDirectGsum11 := ziskLookup "Direct_gsum_[11]" 4194304 4194304 6 1
def ziskMemPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 4194304 0 6 1
def ziskMemRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 4194304 1 1
def ziskMemRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 4194304 1 5
def ziskMemRangeCheckGsum104 := ziskLookup "Range Check_gsum_[104]" 0 4194304 1 1

def ziskMemDeepAli : DeepAliCfg where
  name           := "Mem"
  field          := goldilocks3
  densePCS       := .fri ziskMemFRI
  numConstraints := 34
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemDirectGsum11, ziskMemPermutationGsum10, ziskMemRangeCheckGsum102, ziskMemRangeCheckGsum103, ziskMemRangeCheckGsum104]

-- Mem: 718 KiB (expected) / 1120 KiB (worst case).
example : ziskMemDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 167)
    (lookupBits := [166, 167, 169, 167, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 186, 167, 166, 167, 169, 167,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 718) (proofSizeWorstKib := 1120) := by
  native_decide
example : ziskMemDeepAli.ExitCriteria ziskMemJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [166, 167, 169, 167, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 179, 161, 166, 167, 169, 167,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 718) (proofSizeWorstKib := 1120) := by
  native_decide

/-! ## RomData -/

def ziskRomDataFRI := ziskFRI Rate.half 2097152 19 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskRomDataDirectGsum11 := ziskLookup "Direct_gsum_[11]" 2097152 2097152 6 1
def ziskRomDataPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 2097152 0 6 1
def ziskRomDataRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 3

def ziskRomDataDeepAli : DeepAliCfg where
  name           := "RomData"
  field          := goldilocks3
  densePCS       := .fri ziskRomDataFRI
  numConstraints := 23
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskRomDataDirectGsum11, ziskRomDataPermutationGsum10, ziskRomDataRangeCheckGsum102]

-- RomData: 603 KiB (expected) / 997 KiB (worst case).
example : ziskRomDataDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [167, 168, 169])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 167, 168, 169])
    (totalBits := 111)
    (proofSizeExpKib := 603) (proofSizeWorstKib := 997) := by
  native_decide
example : ziskRomDataDeepAli.ExitCriteria ziskRomDataJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [167, 168, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 180, 161, 167, 168, 169])
    (totalBits := 128)
    (proofSizeExpKib := 603) (proofSizeWorstKib := 997) := by
  native_decide

/-! ## InputData -/

def ziskInputDataFRI := ziskFRI Rate.half 2097152 27 229 32 16 [8, 8, 8, 8, 8, 4]

def ziskInputDataDirectGsum11 := ziskLookup "Direct_gsum_[11]" 2097152 2097152 6 1
def ziskInputDataPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 2097152 0 6 1
def ziskInputDataRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 2097152 1 1
def ziskInputDataRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 2097152 1 8

def ziskInputDataDeepAli : DeepAliCfg where
  name           := "InputData"
  field          := goldilocks3
  densePCS       := .fri ziskInputDataFRI
  numConstraints := 30
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskInputDataDirectGsum11, ziskInputDataPermutationGsum10, ziskInputDataRangeCheckGsum102, ziskInputDataRangeCheckGsum103]

-- InputData: 646 KiB (expected) / 1040 KiB (worst case).
example : ziskInputDataDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [167, 168, 170, 167])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 167, 168, 170, 167])
    (totalBits := 111)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  native_decide
example : ziskInputDataDeepAli.ExitCriteria ziskInputDataJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [167, 168, 170, 167])
    (rowBits := [133, 137, 140, 143, 146, 149, 153, 128, 179, 161, 167, 168, 170, 167])
    (totalBits := 128)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  native_decide

/-! ## MemAlign -/

def ziskMemAlignFRI := ziskFRI Rate.half 2097152 59 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskMemAlignLookupGsum133 := ziskLookup "Lookup_gsum_[133]" 0 2097152 6 1
def ziskMemAlignPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 2097152 6 1
def ziskMemAlignRangeCheckGsum107 := ziskLookup "Range Check_gsum_[107]" 0 2097152 1 8

def ziskMemAlignDeepAli : DeepAliCfg where
  name           := "MemAlign"
  field          := goldilocks3
  densePCS       := .fri ziskMemAlignFRI
  numConstraints := 40
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemAlignLookupGsum133, ziskMemAlignPermutationGsum10, ziskMemAlignRangeCheckGsum107]

-- MemAlign: 821 KiB (expected) / 1217 KiB (worst case).
example : ziskMemAlignDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [168, 168, 167])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 168, 168, 167])
    (totalBits := 111)
    (proofSizeExpKib := 821) (proofSizeWorstKib := 1217) := by
  native_decide
example : ziskMemAlignDeepAli.ExitCriteria ziskMemAlignJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 168, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 168, 168, 167])
    (totalBits := 128)
    (proofSizeExpKib := 821) (proofSizeWorstKib := 1217) := by
  native_decide

/-! ## MemAlignByte -/

def ziskMemAlignByteFRI := ziskFRI Rate.half 4194304 25 229 32 16 [8, 8, 8, 8, 8, 8]

def ziskMemAlignByteDirectGsum10 := ziskLookup "Direct_gsum_[10]" 4194304 4194304 6 1
def ziskMemAlignByteLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 4194304 2 1
def ziskMemAlignBytePermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 4194304 4194304 6 2
def ziskMemAlignByteRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 4194304 1 1
def ziskMemAlignByteRangeCheckGsum107 := ziskLookup "Range Check_gsum_[107]" 0 4194304 1 1

def ziskMemAlignByteDeepAli : DeepAliCfg where
  name           := "MemAlignByte"
  field          := goldilocks3
  densePCS       := .fri ziskMemAlignByteFRI
  numConstraints := 16
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemAlignByteDirectGsum10,
                     ziskMemAlignByteLookupGsum88,
                     ziskMemAlignBytePermutationGsum10,
                     ziskMemAlignByteRangeCheckGsum103,
                     ziskMemAlignByteRangeCheckGsum107]

-- MemAlignByte: 694 KiB (expected) / 1093 KiB (worst case).
example : ziskMemAlignByteDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 167)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 187, 167, 166, 168, 165, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 694) (proofSizeWorstKib := 1093) := by
  native_decide
example : ziskMemAlignByteDeepAli.ExitCriteria ziskMemAlignByteJBR
    (aliBits := 180) (deepBits := 160)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 180, 160, 166, 168, 165, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 694) (proofSizeWorstKib := 1093) := by
  native_decide

/-! ## MemAlignReadByte -/

def ziskMemAlignReadByteFRI := ziskFRI Rate.half 4194304 18 229 32 16 [8, 8, 8, 8, 8, 8]

def ziskMemAlignReadByteDirectGsum10 := ziskLookup "Direct_gsum_[10]" 4194304 4194304 6 1
def ziskMemAlignReadByteLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 4194304 2 1
def ziskMemAlignReadBytePermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 4194304 4194304 6 1
def ziskMemAlignReadByteRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 4194304 1 1

def ziskMemAlignReadByteDeepAli : DeepAliCfg where
  name           := "MemAlignReadByte"
  field          := goldilocks3
  densePCS       := .fri ziskMemAlignReadByteFRI
  numConstraints := 10
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemAlignReadByteDirectGsum10,
                     ziskMemAlignReadByteLookupGsum88,
                     ziskMemAlignReadBytePermutationGsum10,
                     ziskMemAlignReadByteRangeCheckGsum103]

-- MemAlignReadByte: 656 KiB (expected) / 1056 KiB (worst case).
example : ziskMemAlignReadByteDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 168, 166, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 168, 166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  native_decide
example : ziskMemAlignReadByteDeepAli.ExitCriteria ziskMemAlignReadByteJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 168, 166, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 168, 166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  native_decide

/-! ## MemAlignWriteByte -/

def ziskMemAlignWriteByteFRI := ziskFRI Rate.half 4194304 23 229 32 16 [8, 8, 8, 8, 8, 8]

def ziskMemAlignWriteByteDirectGsum10 := ziskLookup "Direct_gsum_[10]" 4194304 4194304 6 1
def ziskMemAlignWriteByteLookupGsum88 := ziskLookup "Lookup_gsum_[88]" 0 4194304 2 1
def ziskMemAlignWriteBytePermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 4194304 4194304 6 2
def ziskMemAlignWriteByteRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 4194304 1 1
def ziskMemAlignWriteByteRangeCheckGsum107 := ziskLookup "Range Check_gsum_[107]" 0 4194304 1 1

def ziskMemAlignWriteByteDeepAli : DeepAliCfg where
  name           := "MemAlignWriteByte"
  field          := goldilocks3
  densePCS       := .fri ziskMemAlignWriteByteFRI
  numConstraints := 15
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemAlignWriteByteDirectGsum10,
                     ziskMemAlignWriteByteLookupGsum88,
                     ziskMemAlignWriteBytePermutationGsum10,
                     ziskMemAlignWriteByteRangeCheckGsum103,
                     ziskMemAlignWriteByteRangeCheckGsum107]

-- MemAlignWriteByte: 683 KiB (expected) / 1082 KiB (worst case).
example : ziskMemAlignWriteByteDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 168, 165, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 683) (proofSizeWorstKib := 1082) := by
  native_decide
example : ziskMemAlignWriteByteDeepAli.ExitCriteria ziskMemAlignWriteByteJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 168, 165, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 683) (proofSizeWorstKib := 1082) := by
  native_decide

/-! ## Arith -/

def ziskArithFRI := ziskFRI Rate.half 2097152 64 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskArithLookupGsum330 := ziskLookup "Lookup_gsum_[330]" 0 2097152 2 23
def ziskArithLookupGsum331 := ziskLookup "Lookup_gsum_[331]" 0 2097152 4 1
def ziskArithLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1

def ziskArithDeepAli : DeepAliCfg where
  name           := "Arith"
  field          := goldilocks3
  densePCS       := .fri ziskArithFRI
  numConstraints := 65
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskArithLookupGsum330, ziskArithLookupGsum331, ziskArithLookupGsum5000]

-- Arith: 848 KiB (expected) / 1244 KiB (worst case).
example : ziskArithDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [165, 168, 166])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 165, 168, 166])
    (totalBits := 111)
    (proofSizeExpKib := 848) (proofSizeWorstKib := 1244) := by
  native_decide
example : ziskArithDeepAli.ExitCriteria ziskArithJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [165, 168, 166])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 165, 168, 166])
    (totalBits := 128)
    (proofSizeExpKib := 848) (proofSizeWorstKib := 1244) := by
  native_decide

/-! ## Binary -/

def ziskBinaryFRI := ziskFRI Rate.half 4194304 49 230 32 16 [8, 8, 8, 8, 8, 8]

def ziskBinaryDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 4194304 11 1
def ziskBinaryLookupGsum125 := ziskLookup "Lookup_gsum_[125]" 0 4194304 7 8
def ziskBinaryLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 4194304 0 11 1

def ziskBinaryDeepAli : DeepAliCfg where
  name           := "Binary"
  field          := goldilocks3
  densePCS       := .fri ziskBinaryFRI
  numConstraints := 14
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskBinaryDirectGsum5000, ziskBinaryLookupGsum125, ziskBinaryLookupGsum5000]

-- Binary: 826 KiB (expected) / 1227 KiB (worst case).
example : ziskBinaryDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 164, 166])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 164, 166])
    (totalBits := 111)
    (proofSizeExpKib := 826) (proofSizeWorstKib := 1227) := by
  native_decide
example : ziskBinaryDeepAli.ExitCriteria ziskBinaryJBR
    (aliBits := 181) (deepBits := 161)
    (lookupBits := [166, 164, 166])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 181, 161, 166, 164, 166])
    (totalBits := 128)
    (proofSizeExpKib := 826) (proofSizeWorstKib := 1227) := by
  native_decide

/-! ## BinaryAdd -/

def ziskBinaryAddFRI := ziskFRI Rate.half 4194304 18 229 32 16 [8, 8, 8, 8, 8, 8]

def ziskBinaryAddDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 4194304 11 1
def ziskBinaryAddLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 4194304 0 11 1
def ziskBinaryAddRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 4194304 1 4

def ziskBinaryAddDeepAli : DeepAliCfg where
  name           := "BinaryAdd"
  field          := goldilocks3
  densePCS       := .fri ziskBinaryAddFRI
  numConstraints := 9
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskBinaryAddDirectGsum5000, ziskBinaryAddLookupGsum5000, ziskBinaryAddRangeCheckGsum103]

-- BinaryAdd: 656 KiB (expected) / 1056 KiB (worst case).
example : ziskBinaryAddDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 166, 167])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 166, 167])
    (totalBits := 111)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  native_decide
example : ziskBinaryAddDeepAli.ExitCriteria ziskBinaryAddJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 166, 167])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 166, 167])
    (totalBits := 128)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  native_decide

/-! ## BinaryExtension -/

def ziskBinaryExtensionFRI := ziskFRI Rate.half 4194304 40 230 32 16 [8, 8, 8, 8, 8, 8]

def ziskBinaryExtensionDirectGsum5000 := ziskLookup "Direct_gsum_[5000]" 0 4194304 11 1
def ziskBinaryExtensionLookupGsum124 := ziskLookup "Lookup_gsum_[124]" 0 4194304 7 8
def ziskBinaryExtensionLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 4194304 0 11 1
def ziskBinaryExtensionRangeCheckGsum102 := ziskLookup "Range Check_gsum_[102]" 0 4194304 1 1

def ziskBinaryExtensionDeepAli : DeepAliCfg where
  name           := "BinaryExtension"
  field          := goldilocks3
  densePCS       := .fri ziskBinaryExtensionFRI
  numConstraints := 8
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskBinaryExtensionDirectGsum5000,
                     ziskBinaryExtensionLookupGsum124,
                     ziskBinaryExtensionLookupGsum5000,
                     ziskBinaryExtensionRangeCheckGsum102]

-- BinaryExtension: 777 KiB (expected) / 1179 KiB (worst case).
example : ziskBinaryExtensionDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 164, 166, 169])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 164, 166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 777) (proofSizeWorstKib := 1179) := by
  native_decide
example : ziskBinaryExtensionDeepAli.ExitCriteria ziskBinaryExtensionJBR
    (aliBits := 182) (deepBits := 161)
    (lookupBits := [166, 164, 166, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 182, 161, 166, 164, 166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 777) (proofSizeWorstKib := 1179) := by
  native_decide

/-! ## Add256 -/

def ziskAdd256FRI := ziskFRI Rate.half 1048576 69 229 64 16 [8, 8, 8, 8, 8]

def ziskAdd256LookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 1048576 0 11 1
def ziskAdd256PermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 1048576 6 16
def ziskAdd256RangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 1048576 1 16

def ziskAdd256DeepAli : DeepAliCfg where
  name           := "Add256"
  field          := goldilocks3
  densePCS       := .fri ziskAdd256FRI
  numConstraints := 36
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskAdd256LookupGsum5000, ziskAdd256PermutationGsum10, ziskAdd256RangeCheckGsum103]

-- Add256: 816 KiB (expected) / 1165 KiB (worst case).
example : ziskAdd256DeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 169)
    (lookupBits := [168, 165, 167])
    (rowBits := [166, 173, 176, 179, 182, 185, 111, 186, 169, 168, 165, 167])
    (totalBits := 111)
    (proofSizeExpKib := 816) (proofSizeWorstKib := 1165) := by
  native_decide
example : ziskAdd256DeepAli.ExitCriteria ziskAdd256JBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 165, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 128, 179, 162, 168, 165, 167])
    (totalBits := 128)
    (proofSizeExpKib := 816) (proofSizeWorstKib := 1165) := by
  native_decide

/-! ## ArithEq -/

def ziskArithEqFRI := ziskFRI Rate.half 1048576 470 231 64 16 [8, 8, 8, 8, 8]

def ziskArithEqLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 1048576 0 11 1
def ziskArithEqLookupGsum5002 := ziskLookup "Lookup_gsum_[5002]" 0 1048576 2 2
def ziskArithEqPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 1048576 6 2
def ziskArithEqRangeCheckGsum103_104 := ziskLookup "Range Check_gsum_[103, 104]" 0 1048576 1 3
def ziskArithEqRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 1048576 1 7
def ziskArithEqRangeCheckGsum108 := ziskLookup "Range Check_gsum_[108]" 0 1048576 1 6

def ziskArithEqDeepAli : DeepAliCfg where
  name           := "ArithEq"
  field          := goldilocks3
  densePCS       := .fri ziskArithEqFRI
  numConstraints := 103
  airMaxDegree   := 3
  maxCombo       := 36
  grindDeep      := 0
  lookups        := [ziskArithEqLookupGsum5000,
                     ziskArithEqLookupGsum5002,
                     ziskArithEqPermutationGsum10,
                     ziskArithEqRangeCheckGsum103_104,
                     ziskArithEqRangeCheckGsum103,
                     ziskArithEqRangeCheckGsum108]

-- ArithEq: 2994 KiB (expected) / 3346 KiB (worst case).
example : ziskArithEqDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 169)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [164, 173, 176, 179, 182, 185, 111, 185, 169, 168, 169, 168, 170, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 2994) (proofSizeWorstKib := 3346) := by
  native_decide
example : ziskArithEqDeepAli.ExitCriteria ziskArithEqJBR
    (aliBits := 178) (deepBits := 163)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [133, 142, 145, 148, 151, 154, 128, 178, 163, 168, 169, 168, 170, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 2994) (proofSizeWorstKib := 3346) := by
  native_decide

/-! ## ArithEq384 -/

def ziskArithEq384FRI := ziskFRI Rate.half 1048576 536 232 64 16 [8, 8, 8, 8, 8]

def ziskArithEq384LookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 1048576 0 11 1
def ziskArithEq384LookupGsum5002 := ziskLookup "Lookup_gsum_[5002]" 0 1048576 2 2
def ziskArithEq384PermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 1048576 6 2
def ziskArithEq384RangeCheckGsum103_104 := ziskLookup "Range Check_gsum_[103, 104]" 0 1048576 1 3
def ziskArithEq384RangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 1048576 1 7
def ziskArithEq384RangeCheckGsum108 := ziskLookup "Range Check_gsum_[108]" 0 1048576 1 6

def ziskArithEq384DeepAli : DeepAliCfg where
  name           := "ArithEq384"
  field          := goldilocks3
  densePCS       := .fri ziskArithEq384FRI
  numConstraints := 76
  airMaxDegree   := 3
  maxCombo       := 54
  grindDeep      := 0
  lookups        := [ziskArithEq384LookupGsum5000,
                     ziskArithEq384LookupGsum5002,
                     ziskArithEq384PermutationGsum10,
                     ziskArithEq384RangeCheckGsum103_104,
                     ziskArithEq384RangeCheckGsum103,
                     ziskArithEq384RangeCheckGsum108]

-- ArithEq384: 3366 KiB (expected) / 3720 KiB (worst case).
example : ziskArithEq384DeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 169)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [163, 173, 176, 179, 182, 185, 112, 185, 169, 168, 169, 168, 170, 169,
                169])
    (totalBits := 112)
    (proofSizeExpKib := 3366) (proofSizeWorstKib := 3720) := by
  native_decide
example : ziskArithEq384DeepAli.ExitCriteria ziskArithEq384JBR
    (aliBits := 179) (deepBits := 163)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [133, 142, 145, 148, 151, 154, 128, 179, 163, 168, 169, 168, 170, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 3366) (proofSizeWorstKib := 3720) := by
  native_decide

/-! ## Keccakf -/

def ziskKeccakfFRI := ziskFRI Rate.half 131072 4065 217 64 23 [8, 8, 8, 8]

def ziskKeccakfLookupGsum126 := ziskLookup "Lookup_gsum_[126]" 0 131072 4 534
def ziskKeccakfLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 131072 0 11 1
def ziskKeccakfPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 131072 6 25

def ziskKeccakfDeepAli : DeepAliCfg where
  name           := "Keccakf"
  field          := goldilocks3
  densePCS       := .fri ziskKeccakfFRI
  numConstraints := 2432
  airMaxDegree   := 3
  maxCombo       := 26
  grindDeep      := 0
  lookups        := [ziskKeccakfLookupGsum126, ziskKeccakfLookupGsum5000, ziskKeccakfPermutationGsum10]

-- Keccakf: 20975 KiB (expected) / 21244 KiB (worst case).
example : ziskKeccakfDeepAli.ExitCriteria ziskUDR
    (aliBits := 180) (deepBits := 172)
    (lookupBits := [163, 171, 167])
    (rowBits := [164, 176, 179, 182, 185, 113, 180, 172, 163, 171, 167])
    (totalBits := 113)
    (proofSizeExpKib := 20975) (proofSizeWorstKib := 21244) := by
  native_decide
example : ziskKeccakfDeepAli.ExitCriteria ziskKeccakfJBR
    (aliBits := 174) (deepBits := 166)
    (lookupBits := [163, 171, 167])
    (rowBits := [132, 145, 148, 151, 154, 128, 174, 166, 163, 171, 167])
    (totalBits := 128)
    (proofSizeExpKib := 20975) (proofSizeWorstKib := 21244) := by
  native_decide

/-! ## Sha256f -/

def ziskSha256fFRI := ziskFRI Rate.half 262144 1265 231 32 16 [8, 8, 8, 8, 4]

def ziskSha256fLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 262144 0 11 1
def ziskSha256fPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 262144 6 1
def ziskSha256fRangeCheckGsum109 := ziskLookup "Range Check_gsum_[109]" 0 262144 1 2

def ziskSha256fDeepAli : DeepAliCfg where
  name           := "Sha256f"
  field          := goldilocks3
  densePCS       := .fri ziskSha256fFRI
  numConstraints := 115
  airMaxDegree   := 3
  maxCombo       := 87
  grindDeep      := 0
  lookups        := [ziskSha256fLookupGsum5000, ziskSha256fPermutationGsum10, ziskSha256fRangeCheckGsum109]

-- Sha256f: 7215 KiB (expected) / 7549 KiB (worst case).
example : ziskSha256fDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 171)
    (lookupBits := [170, 171, 172])
    (rowBits := [164, 175, 178, 181, 184, 187, 111, 185, 171, 170, 171, 172])
    (totalBits := 111)
    (proofSizeExpKib := 7215) (proofSizeWorstKib := 7549) := by
  native_decide
example : ziskSha256fDeepAli.ExitCriteria ziskSha256fJBR
    (aliBits := 178) (deepBits := 165)
    (lookupBits := [170, 171, 172])
    (rowBits := [132, 143, 146, 149, 152, 155, 128, 178, 165, 170, 171, 172])
    (totalBits := 128)
    (proofSizeExpKib := 7215) (proofSizeWorstKib := 7549) := by
  native_decide

/-! ## Poseidon2 -/

def ziskPoseidon2FRI := ziskFRI Rate.quarter 131072 182 114 32 16 [8, 8, 8, 8, 4]

def ziskPoseidon2LookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 131072 0 11 1
def ziskPoseidon2PermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 131072 6 4

def ziskPoseidon2DeepAli : DeepAliCfg where
  name           := "Poseidon2"
  field          := goldilocks3
  densePCS       := .fri ziskPoseidon2FRI
  numConstraints := 85
  airMaxDegree   := 4
  maxCombo       := 17
  grindDeep      := 0
  lookups        := [ziskPoseidon2LookupGsum5000, ziskPoseidon2PermutationGsum10]

-- Poseidon2: 682 KiB (expected) / 832 KiB (worst case).
example : ziskPoseidon2DeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 172)
    (lookupBits := [171, 170])
    (rowBits := [166, 174, 177, 180, 183, 186, 93, 185, 172, 171, 170])
    (totalBits := 93)
    (proofSizeExpKib := 682) (proofSizeWorstKib := 832) := by
  native_decide
example : ziskPoseidon2DeepAli.ExitCriteria ziskPoseidon2JBR
    (aliBits := 177) (deepBits := 164)
    (lookupBits := [171, 170])
    (rowBits := [133, 140, 143, 146, 149, 153, 128, 177, 164, 171, 170])
    (totalBits := 128)
    (proofSizeExpKib := 682) (proofSizeWorstKib := 832) := by
  native_decide

/-! ## Blake2br -/

def ziskBlake2brFRI := ziskFRI Rate.half 262144 651 230 32 16 [8, 8, 8, 8, 4]

def ziskBlake2brLookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 262144 0 11 1
def ziskBlake2brPermutationGsum10 := ziskLookup "Permutation_gsum_[10]" 0 262144 6 4
def ziskBlake2brPermutationGsum127 := ziskLookup "Permutation_gsum_[127]" 262144 262144 3 1
def ziskBlake2brRangeCheckGsum103 := ziskLookup "Range Check_gsum_[103]" 0 262144 1 12

def ziskBlake2brDeepAli : DeepAliCfg where
  name           := "Blake2br"
  field          := goldilocks3
  densePCS       := .fri ziskBlake2brFRI
  numConstraints := 189
  airMaxDegree   := 3
  maxCombo       := 29
  grindDeep      := 0
  lookups        := [ziskBlake2brLookupGsum5000, ziskBlake2brPermutationGsum10, ziskBlake2brPermutationGsum127, ziskBlake2brRangeCheckGsum103]

-- Blake2br: 3874 KiB (expected) / 4207 KiB (worst case).
example : ziskBlake2brDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [170, 169, 171, 170])
    (rowBits := [165, 175, 178, 181, 184, 187, 111, 184, 171, 170, 169, 171, 170])
    (totalBits := 111)
    (proofSizeExpKib := 3874) (proofSizeWorstKib := 4207) := by
  native_decide
example : ziskBlake2brDeepAli.ExitCriteria ziskBlake2brJBR
    (aliBits := 177) (deepBits := 165)
    (lookupBits := [170, 169, 171, 170])
    (rowBits := [133, 142, 145, 148, 151, 155, 128, 177, 165, 170, 169, 171, 170])
    (totalBits := 128)
    (proofSizeExpKib := 3874) (proofSizeWorstKib := 4207) := by
  native_decide

/-! ## SpecifiedRanges -/

def ziskSpecifiedRangesFRI := ziskFRI Rate.half 1048576 107 229 64 16 [8, 8, 8, 8, 8]

def ziskSpecifiedRangesLookupGsum102 := ziskLookup "Lookup_gsum_[102]" 1048576 0 1 1
def ziskSpecifiedRangesLookupGsum103_104 := ziskLookup "Lookup_gsum_[103, 104]" 1048576 0 1 1
def ziskSpecifiedRangesLookupGsum104_105_106_107_108 := ziskLookup "Lookup_gsum_[104, 105, 106, 107, 108]" 1048576 0 1 1
def ziskSpecifiedRangesLookupGsum104 := ziskLookup "Lookup_gsum_[104]" 1048576 0 1 1
def ziskSpecifiedRangesLookupGsum108_109 := ziskLookup "Lookup_gsum_[108, 109]" 1048576 0 1 1
def ziskSpecifiedRangesLookupGsum108 := ziskLookup "Lookup_gsum_[108]" 1048576 0 1 1

def ziskSpecifiedRangesDeepAli : DeepAliCfg where
  name           := "SpecifiedRanges"
  field          := goldilocks3
  densePCS       := .fri ziskSpecifiedRangesFRI
  numConstraints := 16
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskSpecifiedRangesLookupGsum102,
                     ziskSpecifiedRangesLookupGsum103_104,
                     ziskSpecifiedRangesLookupGsum104_105_106_107_108,
                     ziskSpecifiedRangesLookupGsum104,
                     ziskSpecifiedRangesLookupGsum108_109,
                     ziskSpecifiedRangesLookupGsum108]

-- SpecifiedRanges: 1020 KiB (expected) / 1369 KiB (worst case).
example : ziskSpecifiedRangesDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 169)
    (lookupBits := [171, 171, 171, 171, 171, 171])
    (rowBits := [166, 173, 176, 179, 182, 185, 111, 187, 169, 171, 171, 171, 171, 171,
                171])
    (totalBits := 111)
    (proofSizeExpKib := 1020) (proofSizeWorstKib := 1369) := by
  native_decide
example : ziskSpecifiedRangesDeepAli.ExitCriteria ziskSpecifiedRangesJBR
    (aliBits := 180) (deepBits := 162)
    (lookupBits := [171, 171, 171, 171, 171, 171])
    (rowBits := [132, 139, 142, 145, 148, 151, 128, 180, 162, 171, 171, 171, 171, 171,
                171])
    (totalBits := 128)
    (proofSizeExpKib := 1020) (proofSizeWorstKib := 1369) := by
  native_decide

/-! ## VirtualTable0 -/

def ziskVirtualTable0FRI := ziskFRI Rate.half 2097152 69 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskVirtualTable0LookupGsum124_8001 := ziskLookup "Lookup_gsum_[124, 8001]" 2097152 0 7 1
def ziskVirtualTable0LookupGsum125_124 := ziskLookup "Lookup_gsum_[125, 124]" 2097152 0 7 1
def ziskVirtualTable0LookupGsum125 := ziskLookup "Lookup_gsum_[125]" 2097152 0 7 1
def ziskVirtualTable0LookupGsum126_331_8002_133_125 := ziskLookup "Lookup_gsum_[126, 331, 8002, 133, 125]" 2097152 0 7 1
def ziskVirtualTable0LookupGsum330 := ziskLookup "Lookup_gsum_[330]" 2097152 0 2 1
def ziskVirtualTable0LookupGsum5002_88_77_8003_126 := ziskLookup "Lookup_gsum_[5002, 88, 77, 8003, 126]" 2097152 0 4 1

def ziskVirtualTable0DeepAli : DeepAliCfg where
  name           := "VirtualTable0"
  field          := goldilocks3
  densePCS       := .fri ziskVirtualTable0FRI
  numConstraints := 6
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskVirtualTable0LookupGsum124_8001,
                     ziskVirtualTable0LookupGsum125_124,
                     ziskVirtualTable0LookupGsum125,
                     ziskVirtualTable0LookupGsum126_331_8002_133_125,
                     ziskVirtualTable0LookupGsum330,
                     ziskVirtualTable0LookupGsum5002_88_77_8003_126]

-- VirtualTable0: 875 KiB (expected) / 1270 KiB (worst case).
example : ziskVirtualTable0DeepAli.ExitCriteria ziskUDR
    (aliBits := 189) (deepBits := 168)
    (lookupBits := [168, 168, 168, 168, 169, 168])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 189, 168, 168, 168, 168, 168,
                169, 168])
    (totalBits := 111)
    (proofSizeExpKib := 875) (proofSizeWorstKib := 1270) := by
  native_decide
example : ziskVirtualTable0DeepAli.ExitCriteria ziskVirtualTable0JBR
    (aliBits := 182) (deepBits := 162)
    (lookupBits := [168, 168, 168, 168, 169, 168])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 182, 162, 168, 168, 168, 168,
                169, 168])
    (totalBits := 128)
    (proofSizeExpKib := 875) (proofSizeWorstKib := 1270) := by
  native_decide

/-! ## VirtualTable1 -/

def ziskVirtualTable1FRI := ziskFRI Rate.half 2097152 90 230 32 16 [8, 8, 8, 8, 8, 4]

def ziskVirtualTable1LookupGsum5000 := ziskLookup "Lookup_gsum_[5000]" 2097152 0 8 1

def ziskVirtualTable1DeepAli : DeepAliCfg where
  name           := "VirtualTable1"
  field          := goldilocks3
  densePCS       := .fri ziskVirtualTable1FRI
  numConstraints := 6
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskVirtualTable1LookupGsum5000]

-- VirtualTable1: 989 KiB (expected) / 1384 KiB (worst case).
example : ziskVirtualTable1DeepAli.ExitCriteria ziskUDR
    (aliBits := 189) (deepBits := 168)
    (lookupBits := [167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 189, 168, 167])
    (totalBits := 111)
    (proofSizeExpKib := 989) (proofSizeWorstKib := 1384) := by
  native_decide
example : ziskVirtualTable1DeepAli.ExitCriteria ziskVirtualTable1JBR
    (aliBits := 182) (deepBits := 162)
    (lookupBits := [167])
    (rowBits := [133, 139, 142, 145, 148, 151, 155, 128, 182, 162, 167])
    (totalBits := 128)
    (proofSizeExpKib := 989) (proofSizeWorstKib := 1384) := by
  native_decide

/-! ## DmaPrePost-compressor -/

def ziskDmaPrePostCompressorFRI := ziskFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def ziskDmaPrePostCompressorConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 262144 262144 2 36

def ziskDmaPrePostCompressorDeepAli : DeepAliCfg where
  name           := "DmaPrePost-compressor"
  field          := goldilocks3
  densePCS       := .fri ziskDmaPrePostCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskDmaPrePostCompressorConnectionGprod1]

-- DmaPrePost-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskDmaPrePostCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide
example : ziskDmaPrePostCompressorDeepAli.ExitCriteria ziskDmaPrePostCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide

/-! ## ArithEq-compressor -/

def ziskArithEqCompressorFRI := ziskFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def ziskArithEqCompressorConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 262144 262144 2 36

def ziskArithEqCompressorDeepAli : DeepAliCfg where
  name           := "ArithEq-compressor"
  field          := goldilocks3
  densePCS       := .fri ziskArithEqCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskArithEqCompressorConnectionGprod1]

-- ArithEq-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskArithEqCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide
example : ziskArithEqCompressorDeepAli.ExitCriteria ziskArithEqCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide

/-! ## ArithEq384-compressor -/

def ziskArithEq384CompressorFRI := ziskFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def ziskArithEq384CompressorConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 262144 262144 2 36

def ziskArithEq384CompressorDeepAli : DeepAliCfg where
  name           := "ArithEq384-compressor"
  field          := goldilocks3
  densePCS       := .fri ziskArithEq384CompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskArithEq384CompressorConnectionGprod1]

-- ArithEq384-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskArithEq384CompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide
example : ziskArithEq384CompressorDeepAli.ExitCriteria ziskArithEq384CompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide

/-! ## Keccakf-compressor -/

def ziskKeccakfCompressorFRI := ziskFRI Rate.quarter 1048576 198 110 32 20 [8, 8, 8, 8, 8, 4]

def ziskKeccakfCompressorConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 1048576 1048576 2 36

def ziskKeccakfCompressorDeepAli : DeepAliCfg where
  name           := "Keccakf-compressor"
  field          := goldilocks3
  densePCS       := .fri ziskKeccakfCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskKeccakfCompressorConnectionGprod1]

-- Keccakf-compressor: 771 KiB (expected) / 940 KiB (worst case).
example : ziskKeccakfCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 169)
    (lookupBits := [164])
    (rowBits := [163, 171, 174, 177, 180, 183, 186, 94, 184, 169, 164])
    (totalBits := 94)
    (proofSizeExpKib := 771) (proofSizeWorstKib := 940) := by
  native_decide
example : ziskKeccakfCompressorDeepAli.ExitCriteria ziskKeccakfCompressorJBR
    (aliBits := 177) (deepBits := 162)
    (lookupBits := [164])
    (rowBits := [133, 141, 144, 147, 150, 153, 156, 128, 177, 162, 164])
    (totalBits := 128)
    (proofSizeExpKib := 771) (proofSizeWorstKib := 940) := by
  native_decide

/-! ## Sha256f-compressor -/

def ziskSha256fCompressorFRI := ziskFRI Rate.quarter 524288 198 110 64 20 [8, 8, 8, 8, 8]

def ziskSha256fCompressorConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 524288 524288 2 36

def ziskSha256fCompressorDeepAli : DeepAliCfg where
  name           := "Sha256f-compressor"
  field          := goldilocks3
  densePCS       := .fri ziskSha256fCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskSha256fCompressorConnectionGprod1]

-- Sha256f-compressor: 743 KiB (expected) / 892 KiB (worst case).
example : ziskSha256fCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 170)
    (lookupBits := [165])
    (rowBits := [164, 172, 175, 178, 181, 184, 94, 184, 170, 165])
    (totalBits := 94)
    (proofSizeExpKib := 743) (proofSizeWorstKib := 892) := by
  native_decide
example : ziskSha256fCompressorDeepAli.ExitCriteria ziskSha256fCompressorJBR
    (aliBits := 176) (deepBits := 162)
    (lookupBits := [165])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 162, 165])
    (totalBits := 128)
    (proofSizeExpKib := 743) (proofSizeWorstKib := 892) := by
  native_decide

/-! ## Blake2br-compressor -/

def ziskBlake2brCompressorFRI := ziskFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def ziskBlake2brCompressorConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 262144 262144 2 36

def ziskBlake2brCompressorDeepAli : DeepAliCfg where
  name           := "Blake2br-compressor"
  field          := goldilocks3
  densePCS       := .fri ziskBlake2brCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskBlake2brCompressorConnectionGprod1]

-- Blake2br-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskBlake2brCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide
example : ziskBlake2brCompressorDeepAli.ExitCriteria ziskBlake2brCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  native_decide

/-! ## Recursive2 -/

def ziskRecursive2FRI := ziskFRI Rate.eighth 131072 145 73 32 20 [8, 8, 8, 8, 8]

def ziskRecursive2ConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 131072 131072 2 27

def ziskRecursive2DeepAli : DeepAliCfg where
  name           := "Recursive2"
  field          := goldilocks3
  densePCS       := .fri ziskRecursive2FRI
  numConstraints := 158
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [ziskRecursive2ConnectionGprod1]

-- Recursive2: 398 KiB (expected) / 487 KiB (worst case).
example : ziskRecursive2DeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [168])
    (rowBits := [166, 173, 176, 179, 182, 185, 80, 184, 171, 168])
    (totalBits := 80)
    (proofSizeExpKib := 398) (proofSizeWorstKib := 487) := by
  native_decide
example : ziskRecursive2DeepAli.ExitCriteria ziskRecursive2JBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [168])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 168])
    (totalBits := 128)
    (proofSizeExpKib := 398) (proofSizeWorstKib := 487) := by
  native_decide

/-! ## Final -/

def ziskFinalFRI := ziskFRI Rate.thirtysecond 65536 139 43 32 22 [16, 16, 16, 16]

def ziskFinalConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 65536 65536 2 24

def ziskFinalDeepAli : DeepAliCfg where
  name           := "Final"
  field          := goldilocks3
  densePCS       := .fri ziskFinalFRI
  numConstraints := 154
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [ziskFinalConnectionGprod1]

-- Final: 253 KiB (expected) / 292 KiB (worst case).
example : ziskFinalDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 172)
    (lookupBits := [169])
    (rowBits := [164, 172, 176, 180, 184, 63, 184, 172, 169])
    (totalBits := 63)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 292) := by
  native_decide
example : ziskFinalDeepAli.ExitCriteria ziskFinalJBR
    (aliBits := 175) (deepBits := 163)
    (lookupBits := [169])
    (rowBits := [133, 140, 144, 148, 152, 128, 175, 163, 169])
    (totalBits := 128)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 292) := by
  native_decide

/-! ## Final_Compressed -/

def ziskFinalCompressedFRI := ziskFRI Rate.sixteenth 32768 145 54 1024 22 [8, 8, 8]

def ziskFinalCompressedConnectionGprod1 := ziskLookup "Connection_gprod_[1]" 32768 32768 2 27

def ziskFinalCompressedDeepAli : DeepAliCfg where
  name           := "Final_Compressed"
  field          := goldilocks3
  densePCS       := .fri ziskFinalCompressedFRI
  numConstraints := 158
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [ziskFinalCompressedConnectionGprod1]

-- Final_Compressed: 269 KiB (expected) / 313 KiB (worst case).
example : ziskFinalCompressedDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 173)
    (lookupBits := [170])
    (rowBits := [166, 174, 177, 180, 71, 184, 173, 170])
    (totalBits := 71)
    (proofSizeExpKib := 269) (proofSizeWorstKib := 313) := by
  native_decide
example : ziskFinalCompressedDeepAli.ExitCriteria ziskFinalCompressedJBR
    (aliBits := 175) (deepBits := 164)
    (lookupBits := [170])
    (rowBits := [134, 141, 144, 147, 128, 175, 164, 170])
    (totalBits := 128)
    (proofSizeExpKib := 269) (proofSizeWorstKib := 313) := by
  native_decide

end Soundcalc
