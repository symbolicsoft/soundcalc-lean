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

/-! ## Regimes -/

abbrev ziskUDR : Regime := UDR goldilocks3

/-- `Dma`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDmaJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `DmaMemCpy`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskDmaMemCpyJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (15 / 3000))
/-- `DmaInputCpy`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskDmaInputCpyJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (14 / 3000))
/-- `Dma64Aligned`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskDma64AlignedJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (17 / 3000))
/-- `Dma64AlignedInputCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDma64AlignedInputCpyJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `Dma64AlignedMemSet`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskDma64AlignedMemSetJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (15 / 3000))
/-- `Dma64AlignedMem`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDma64AlignedMemJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `Dma64AlignedMemCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDma64AlignedMemCpyJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `DmaUnaligned`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDmaUnalignedJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `DmaPrePost`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskDmaPrePostJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (18 / 3000))
/-- `DmaPrePostMemCpy`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskDmaPrePostMemCpyJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (17 / 3000))
/-- `DmaPrePostInputCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskDmaPrePostInputCpyJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `Main`: gap_to_radius = 0.006333333333333333 = 19/3000. -/
abbrev ziskMainJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (19 / 3000))
/-- `Rom`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskRomJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (15 / 3000))
/-- `Mem`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskMemJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (17 / 3000))
/-- `RomData`: gap_to_radius = 0.004333333333333333 = 13/3000. -/
abbrev ziskRomDataJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (13 / 3000))
/-- `InputData`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskInputDataJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (14 / 3000))
/-- `MemAlign`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskMemAlignJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (17 / 3000))
/-- `MemAlignByte`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskMemAlignByteJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `MemAlignReadByte`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskMemAlignReadByteJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (15 / 3000))
/-- `MemAlignWriteByte`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskMemAlignWriteByteJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `Arith`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskArithJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (17 / 3000))
/-- `Binary`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskBinaryJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (18 / 3000))
/-- `BinaryAdd`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskBinaryAddJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (15 / 3000))
/-- `BinaryExtension`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskBinaryExtensionJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (18 / 3000))
/-- `Add256`: gap_to_radius = 0.005 = 15/3000. -/
abbrev ziskAdd256JBR : Regime := JBR goldilocks3 (2 ^ 40) (some (15 / 3000))
/-- `ArithEq`: gap_to_radius = 0.007333333333333333 = 22/3000. -/
abbrev ziskArithEqJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (22 / 3000))
/-- `ArithEq384`: gap_to_radius = 0.007666666666666666 = 23/3000. -/
abbrev ziskArithEq384JBR : Regime := JBR goldilocks3 (2 ^ 40) (some (23 / 3000))
/-- `Keccakf`: gap_to_radius = 0.007333333333333333 = 22/3000. -/
abbrev ziskKeccakfJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (22 / 3000))
/-- `Sha256f`: gap_to_radius = 0.006666666666666666 = 20/3000. -/
abbrev ziskSha256fJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (20 / 3000))
/-- `Poseidon2`: gap_to_radius = 0.004 = 12/3000. -/
abbrev ziskPoseidon2JBR : Regime := JBR goldilocks3 (2 ^ 40) (some (12 / 3000))
/-- `Blake2br`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskBlake2brJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (18 / 3000))
/-- `SpecifiedRanges`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskSpecifiedRangesJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `VirtualTable0`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev ziskVirtualTable0JBR : Regime := JBR goldilocks3 (2 ^ 40) (some (17 / 3000))
/-- `VirtualTable1`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev ziskVirtualTable1JBR : Regime := JBR goldilocks3 (2 ^ 40) (some (18 / 3000))
/-- `DmaPrePost-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskDmaPrePostCompressorJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (14 / 3000))
/-- `ArithEq-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskArithEqCompressorJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (14 / 3000))
/-- `ArithEq384-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskArithEq384CompressorJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (14 / 3000))
/-- `Keccakf-compressor`: gap_to_radius = 0.006333333333333333 = 19/3000. -/
abbrev ziskKeccakfCompressorJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (19 / 3000))
/-- `Sha256f-compressor`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev ziskSha256fCompressorJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (16 / 3000))
/-- `Blake2br-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev ziskBlake2brCompressorJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (14 / 3000))
/-- `Recursive2`: gap_to_radius = 0.004 = 12/3000. -/
abbrev ziskRecursive2JBR : Regime := JBR goldilocks3 (2 ^ 40) (some (12 / 3000))
/-- `Final`: gap_to_radius = 0.003333333333333333 = 10/3000. -/
abbrev ziskFinalJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (10 / 3000))
/-- `Final_Compressed`: gap_to_radius = 0.003333333333333333 = 10/3000. -/
abbrev ziskFinalCompressedJBR : Regime := JBR goldilocks3 (2 ^ 40) (some (10 / 3000))

/-! ## Dma -/

def ziskDmaFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 46
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaLookupGsum77 : LookupCfg where
  name := "Lookup_gsum_[77]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaLookupGsum8001 : LookupCfg where
  name := "Lookup_gsum_[8001]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaPermutationGsum8000 : LookupCfg where
  name := "Permutation_gsum_[8000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 2
  grindBitsLookup := 0
def ziskDmaRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0
def ziskDmaRangeCheckGsum104 : LookupCfg where
  name := "Range Check_gsum_[104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDmaDeepAli : DeepAliCfg where
  name           := "Dma"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma: 748 KiB (expected) / 1142 KiB (worst case).
example : ziskDmaDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 166, 169, 168, 168,
                166, 170, 169, 169])
    (totalBits := 111)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaDeepAli.ExitCriteria ziskDmaJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 179, 161, 166, 169, 168, 168,
                166, 170, 169, 169])
    (totalBits := 128)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaMemCpy -/

def ziskDmaMemCpyFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 33
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaMemCpyLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaMemCpyLookupGsum77 : LookupCfg where
  name := "Lookup_gsum_[77]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaMemCpyLookupGsum8001 : LookupCfg where
  name := "Lookup_gsum_[8001]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaMemCpyPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaMemCpyPermutationGsum8000 : LookupCfg where
  name := "Permutation_gsum_[8000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 2
  grindBitsLookup := 0
def ziskDmaMemCpyRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaMemCpyRangeCheckGsum104 : LookupCfg where
  name := "Range Check_gsum_[104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDmaMemCpyDeepAli : DeepAliCfg where
  name           := "DmaMemCpy"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaMemCpy: 679 KiB (expected) / 1072 KiB (worst case).
example : ziskDmaMemCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 187, 168, 166, 169, 168, 168,
                166, 170, 169])
    (totalBits := 111)
    (proofSizeExpKib := 679) (proofSizeWorstKib := 1072) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaMemCpyDeepAli.ExitCriteria ziskDmaMemCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 180, 161, 166, 169, 168, 168,
                166, 170, 169])
    (totalBits := 128)
    (proofSizeExpKib := 679) (proofSizeWorstKib := 1072) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaInputCpy -/

def ziskDmaInputCpyFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 27
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaInputCpyLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaInputCpyLookupGsum8001 : LookupCfg where
  name := "Lookup_gsum_[8001]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaInputCpyPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaInputCpyPermutationGsum8000 : LookupCfg where
  name := "Permutation_gsum_[8000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 2
  grindBitsLookup := 0
def ziskDmaInputCpyRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaInputCpyRangeCheckGsum104 : LookupCfg where
  name := "Range Check_gsum_[104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaInputCpyRangeCheckGsum105 : LookupCfg where
  name := "Range Check_gsum_[105]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskDmaInputCpyDeepAli : DeepAliCfg where
  name           := "DmaInputCpy"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaInputCpy: 646 KiB (expected) / 1040 KiB (worst case).
example : ziskDmaInputCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [166, 168, 168, 166, 170, 170, 170])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 166, 168, 168, 166,
                170, 170, 170])
    (totalBits := 111)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaInputCpyDeepAli.ExitCriteria ziskDmaInputCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [166, 168, 168, 166, 170, 170, 170])
    (rowBits := [133, 137, 140, 143, 146, 149, 153, 128, 180, 161, 166, 168, 168, 166,
                170, 170, 170])
    (totalBits := 128)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64Aligned -/

def ziskDma64AlignedFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 62
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDma64AlignedDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedDirectGsum8200 : LookupCfg where
  name := "Direct_gsum_[8200]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 10; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 4
  grindBitsLookup := 0
def ziskDma64AlignedPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 9
  grindBitsLookup := 0
def ziskDma64AlignedRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 8
  grindBitsLookup := 0
def ziskDma64AlignedRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDma64AlignedDeepAli : DeepAliCfg where
  name           := "Dma64Aligned"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64Aligned: 838 KiB (expected) / 1233 KiB (worst case).
example : ziskDma64AlignedDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 167, 165, 167, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 167,
                165, 167, 169])
    (totalBits := 111)
    (proofSizeExpKib := 838) (proofSizeWorstKib := 1233) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDma64AlignedDeepAli.ExitCriteria ziskDma64AlignedJBR
    (aliBits := 178) (deepBits := 162)
    (lookupBits := [167, 166, 167, 167, 165, 167, 169])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 178, 162, 167, 166, 167, 167,
                165, 167, 169])
    (totalBits := 128)
    (proofSizeExpKib := 838) (proofSizeWorstKib := 1233) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedInputCpy -/

def ziskDma64AlignedInputCpyFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 44
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDma64AlignedInputCpyDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedInputCpyDirectGsum8200 : LookupCfg where
  name := "Direct_gsum_[8200]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 10; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedInputCpyLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedInputCpyLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 4
  grindBitsLookup := 0
def ziskDma64AlignedInputCpyPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 4
  grindBitsLookup := 0
def ziskDma64AlignedInputCpyRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 8
  grindBitsLookup := 0
def ziskDma64AlignedInputCpyRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDma64AlignedInputCpyDeepAli : DeepAliCfg where
  name           := "Dma64AlignedInputCpy"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedInputCpy: 738 KiB (expected) / 1131 KiB (worst case).
example : ziskDma64AlignedInputCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [167, 166, 167, 167, 166, 167, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 167, 166, 167, 167,
                166, 167, 169])
    (totalBits := 111)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDma64AlignedInputCpyDeepAli.ExitCriteria ziskDma64AlignedInputCpyJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [167, 166, 167, 167, 166, 167, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 179, 161, 167, 166, 167, 167,
                166, 167, 169])
    (totalBits := 128)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedMemSet -/

def ziskDma64AlignedMemSetFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 30
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDma64AlignedMemSetDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemSetDirectGsum8200 : LookupCfg where
  name := "Direct_gsum_[8200]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 10; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemSetLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemSetPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 8
  grindBitsLookup := 0
def ziskDma64AlignedMemSetRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDma64AlignedMemSetDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMemSet"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedMemSet: 662 KiB (expected) / 1056 KiB (worst case).
example : ziskDma64AlignedMemSetDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 186, 168, 167, 166, 167, 165,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 662) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDma64AlignedMemSetDeepAli.ExitCriteria ziskDma64AlignedMemSetJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 178, 161, 167, 166, 167, 165,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 662) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedMem -/

def ziskDma64AlignedMemFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 46
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDma64AlignedMemDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemDirectGsum8200 : LookupCfg where
  name := "Direct_gsum_[8200]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 10; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 9
  grindBitsLookup := 0
def ziskDma64AlignedMemRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDma64AlignedMemDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMem"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedMem: 748 KiB (expected) / 1142 KiB (worst case).
example : ziskDma64AlignedMemDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 165,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDma64AlignedMemDeepAli.ExitCriteria ziskDma64AlignedMemJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 166, 167, 165,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedMemCpy -/

def ziskDma64AlignedMemCpyFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 52
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDma64AlignedMemCpyDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemCpyDirectGsum8200 : LookupCfg where
  name := "Direct_gsum_[8200]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 10; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemCpyLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDma64AlignedMemCpyPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 17
  grindBitsLookup := 0
def ziskDma64AlignedMemCpyRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDma64AlignedMemCpyDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMemCpy"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedMemCpy: 781 KiB (expected) / 1174 KiB (worst case).
example : ziskDma64AlignedMemCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 164, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 164,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDma64AlignedMemCpyDeepAli.ExitCriteria ziskDma64AlignedMemCpyJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 164, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 166, 167, 164,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaUnaligned -/

def ziskDmaUnalignedFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 52
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaUnalignedDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaUnalignedDirectGsum8201 : LookupCfg where
  name := "Direct_gsum_[8201]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 18; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaUnalignedLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaUnalignedLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 4
  grindBitsLookup := 0
def ziskDmaUnalignedPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 6; numLookupsM := 2
  grindBitsLookup := 0
def ziskDmaUnalignedRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskDmaUnalignedDeepAli : DeepAliCfg where
  name           := "DmaUnaligned"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaUnaligned: 781 KiB (expected) / 1174 KiB (worst case).
example : ziskDmaUnalignedDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 165, 167, 167, 166, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 165, 167, 167,
                166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaUnalignedDeepAli.ExitCriteria ziskDmaUnalignedJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 165, 167, 167, 166, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 165, 167, 167,
                166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePost -/

def ziskDmaPrePostFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 83
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaPrePostLookupGsum8002 : LookupCfg where
  name := "Lookup_gsum_[8002]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaPrePostLookupGsum8003 : LookupCfg where
  name := "Lookup_gsum_[8003]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 3; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaPrePostLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 12
  grindBitsLookup := 0
def ziskDmaPrePostPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 4
  grindBitsLookup := 0
def ziskDmaPrePostPermutationGsum8000 : LookupCfg where
  name := "Permutation_gsum_[8000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def ziskDmaPrePostDeepAli : DeepAliCfg where
  name           := "DmaPrePost"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePost: 951 KiB (expected) / 1346 KiB (worst case).
example : ziskDmaPrePostDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [168, 169, 166, 166, 167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 185, 168, 168, 169, 166, 166,
                167])
    (totalBits := 111)
    (proofSizeExpKib := 951) (proofSizeWorstKib := 1346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaPrePostDeepAli.ExitCriteria ziskDmaPrePostJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 169, 166, 166, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 155, 128, 179, 162, 168, 169, 166, 166,
                167])
    (totalBits := 128)
    (proofSizeExpKib := 951) (proofSizeWorstKib := 1346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePostMemCpy -/

def ziskDmaPrePostMemCpyFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 70
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaPrePostMemCpyLookupGsum8002 : LookupCfg where
  name := "Lookup_gsum_[8002]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaPrePostMemCpyLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 12
  grindBitsLookup := 0
def ziskDmaPrePostMemCpyPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 4
  grindBitsLookup := 0
def ziskDmaPrePostMemCpyPermutationGsum8000 : LookupCfg where
  name := "Permutation_gsum_[8000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def ziskDmaPrePostMemCpyDeepAli : DeepAliCfg where
  name           := "DmaPrePostMemCpy"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePostMemCpy: 881 KiB (expected) / 1276 KiB (worst case).
example : ziskDmaPrePostMemCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [168, 166, 166, 167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 186, 168, 168, 166, 166, 167])
    (totalBits := 111)
    (proofSizeExpKib := 881) (proofSizeWorstKib := 1276) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaPrePostMemCpyDeepAli.ExitCriteria ziskDmaPrePostMemCpyJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 166, 166, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 168, 166, 166, 167])
    (totalBits := 128)
    (proofSizeExpKib := 881) (proofSizeWorstKib := 1276) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePostInputCpy -/

def ziskDmaPrePostInputCpyFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 44
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaPrePostInputCpyLookupGsum8002 : LookupCfg where
  name := "Lookup_gsum_[8002]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskDmaPrePostInputCpyLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 8
  grindBitsLookup := 0
def ziskDmaPrePostInputCpyPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 2
  grindBitsLookup := 0
def ziskDmaPrePostInputCpyPermutationGsum8000 : LookupCfg where
  name := "Permutation_gsum_[8000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def ziskDmaPrePostInputCpyDeepAli : DeepAliCfg where
  name           := "DmaPrePostInputCpy"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePostInputCpy: 738 KiB (expected) / 1131 KiB (worst case).
example : ziskDmaPrePostInputCpyDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [168, 166, 167, 167])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 187, 168, 168, 166, 167, 167])
    (totalBits := 111)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaPrePostInputCpyDeepAli.ExitCriteria ziskDmaPrePostInputCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [168, 166, 167, 167])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 180, 161, 168, 166, 167, 167])
    (totalBits := 128)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Main -/

def ziskMainFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 61
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskMainDirectGsum1000 : LookupCfg where
  name := "Direct_gsum_[1000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 5; numLookupsM := 1
  grindBitsLookup := 0
def ziskMainLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskMainLookupGsum7890 : LookupCfg where
  name := "Lookup_gsum_[7890]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskMainPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 34
  grindBitsLookup := 0
def ziskMainRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 34
  grindBitsLookup := 0
def ziskMainRangeCheckGsum106 : LookupCfg where
  name := "Range Check_gsum_[106]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskMainDeepAli : DeepAliCfg where
  name           := "Main"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Main: 890 KiB (expected) / 1292 KiB (worst case).
example : ziskMainDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 167)
    (lookupBits := [166, 166, 166, 161, 164, 169])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 184, 167, 166, 166, 166, 161,
                164, 169])
    (totalBits := 111)
    (proofSizeExpKib := 890) (proofSizeWorstKib := 1292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskMainDeepAli.ExitCriteria ziskMainJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [166, 166, 166, 161, 164, 169])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 178, 161, 166, 166, 166, 161,
                164, 169])
    (totalBits := 128)
    (proofSizeExpKib := 890) (proofSizeWorstKib := 1292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Rom -/

def ziskRomFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 18
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 221
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskRomLookupGsum7890 : LookupCfg where
  name := "Lookup_gsum_[7890]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def ziskRomDeepAli : DeepAliCfg where
  name           := "Rom"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskRomFRI
  numConstraints := 3
  airMaxDegree   := 2
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskRomLookupGsum7890]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Rom: 635 KiB (expected) / 1019 KiB (worst case).
example : ziskRomDeepAli.ExitCriteria ziskUDR
    (aliBits := 190) (deepBits := 168)
    (lookupBits := [166])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 190, 168, 166])
    (totalBits := 111)
    (proofSizeExpKib := 635) (proofSizeWorstKib := 1019) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskRomDeepAli.ExitCriteria ziskRomJBR
    (aliBits := 183) (deepBits := 161)
    (lookupBits := [166])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 183, 161, 166])
    (totalBits := 128)
    (proofSizeExpKib := 635) (proofSizeWorstKib := 1019) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Mem -/

def ziskMemFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 29
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskMemDirectGsum11 : LookupCfg where
  name := "Direct_gsum_[11]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 0; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 5
  grindBitsLookup := 0
def ziskMemRangeCheckGsum104 : LookupCfg where
  name := "Range Check_gsum_[104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskMemDeepAli : DeepAliCfg where
  name           := "Mem"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskMemFRI
  numConstraints := 34
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemDirectGsum11, ziskMemPermutationGsum10, ziskMemRangeCheckGsum102, ziskMemRangeCheckGsum103, ziskMemRangeCheckGsum104]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Mem: 718 KiB (expected) / 1120 KiB (worst case).
example : ziskMemDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 167)
    (lookupBits := [166, 167, 169, 167, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 186, 167, 166, 167, 169, 167,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 718) (proofSizeWorstKib := 1120) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskMemDeepAli.ExitCriteria ziskMemJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [166, 167, 169, 167, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 179, 161, 166, 167, 169, 167,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 718) (proofSizeWorstKib := 1120) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## RomData -/

def ziskRomDataFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 19
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskRomDataDirectGsum11 : LookupCfg where
  name := "Direct_gsum_[11]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskRomDataPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskRomDataRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 3
  grindBitsLookup := 0

def ziskRomDataDeepAli : DeepAliCfg where
  name           := "RomData"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskRomDataFRI
  numConstraints := 23
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskRomDataDirectGsum11, ziskRomDataPermutationGsum10, ziskRomDataRangeCheckGsum102]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- RomData: 603 KiB (expected) / 997 KiB (worst case).
example : ziskRomDataDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [167, 168, 169])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 167, 168, 169])
    (totalBits := 111)
    (proofSizeExpKib := 603) (proofSizeWorstKib := 997) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskRomDataDeepAli.ExitCriteria ziskRomDataJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [167, 168, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 180, 161, 167, 168, 169])
    (totalBits := 128)
    (proofSizeExpKib := 603) (proofSizeWorstKib := 997) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## InputData -/

def ziskInputDataFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 27
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskInputDataDirectGsum11 : LookupCfg where
  name := "Direct_gsum_[11]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskInputDataPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskInputDataRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskInputDataRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 8
  grindBitsLookup := 0

def ziskInputDataDeepAli : DeepAliCfg where
  name           := "InputData"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskInputDataFRI
  numConstraints := 30
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskInputDataDirectGsum11, ziskInputDataPermutationGsum10, ziskInputDataRangeCheckGsum102, ziskInputDataRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- InputData: 646 KiB (expected) / 1040 KiB (worst case).
example : ziskInputDataDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [167, 168, 170, 167])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 167, 168, 170, 167])
    (totalBits := 111)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskInputDataDeepAli.ExitCriteria ziskInputDataJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [167, 168, 170, 167])
    (rowBits := [133, 137, 140, 143, 146, 149, 153, 128, 179, 161, 167, 168, 170, 167])
    (totalBits := 128)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlign -/

def ziskMemAlignFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 59
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskMemAlignLookupGsum133 : LookupCfg where
  name := "Lookup_gsum_[133]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignRangeCheckGsum107 : LookupCfg where
  name := "Range Check_gsum_[107]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 1; numLookupsM := 8
  grindBitsLookup := 0

def ziskMemAlignDeepAli : DeepAliCfg where
  name           := "MemAlign"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskMemAlignFRI
  numConstraints := 40
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskMemAlignLookupGsum133, ziskMemAlignPermutationGsum10, ziskMemAlignRangeCheckGsum107]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlign: 821 KiB (expected) / 1217 KiB (worst case).
example : ziskMemAlignDeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [168, 168, 167])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 168, 168, 167])
    (totalBits := 111)
    (proofSizeExpKib := 821) (proofSizeWorstKib := 1217) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskMemAlignDeepAli.ExitCriteria ziskMemAlignJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 168, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 168, 168, 167])
    (totalBits := 128)
    (proofSizeExpKib := 821) (proofSizeWorstKib := 1217) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlignByte -/

def ziskMemAlignByteFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 25
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskMemAlignByteDirectGsum10 : LookupCfg where
  name := "Direct_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignByteLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 2; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignBytePermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 2
  grindBitsLookup := 0
def ziskMemAlignByteRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignByteRangeCheckGsum107 : LookupCfg where
  name := "Range Check_gsum_[107]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskMemAlignByteDeepAli : DeepAliCfg where
  name           := "MemAlignByte"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlignByte: 694 KiB (expected) / 1093 KiB (worst case).
example : ziskMemAlignByteDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 167)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 187, 167, 166, 168, 165, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 694) (proofSizeWorstKib := 1093) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskMemAlignByteDeepAli.ExitCriteria ziskMemAlignByteJBR
    (aliBits := 180) (deepBits := 160)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 180, 160, 166, 168, 165, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 694) (proofSizeWorstKib := 1093) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlignReadByte -/

def ziskMemAlignReadByteFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 18
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskMemAlignReadByteDirectGsum10 : LookupCfg where
  name := "Direct_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignReadByteLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 2; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignReadBytePermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignReadByteRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskMemAlignReadByteDeepAli : DeepAliCfg where
  name           := "MemAlignReadByte"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlignReadByte: 656 KiB (expected) / 1056 KiB (worst case).
example : ziskMemAlignReadByteDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 168, 166, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 168, 166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskMemAlignReadByteDeepAli.ExitCriteria ziskMemAlignReadByteJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 168, 166, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 168, 166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlignWriteByte -/

def ziskMemAlignWriteByteFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 23
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskMemAlignWriteByteDirectGsum10 : LookupCfg where
  name := "Direct_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignWriteByteLookupGsum88 : LookupCfg where
  name := "Lookup_gsum_[88]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 2; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignWriteBytePermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 6; numLookupsM := 2
  grindBitsLookup := 0
def ziskMemAlignWriteByteRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskMemAlignWriteByteRangeCheckGsum107 : LookupCfg where
  name := "Range Check_gsum_[107]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskMemAlignWriteByteDeepAli : DeepAliCfg where
  name           := "MemAlignWriteByte"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlignWriteByte: 683 KiB (expected) / 1082 KiB (worst case).
example : ziskMemAlignWriteByteDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 168, 165, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 683) (proofSizeWorstKib := 1082) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskMemAlignWriteByteDeepAli.ExitCriteria ziskMemAlignWriteByteJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 168, 165, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 683) (proofSizeWorstKib := 1082) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Arith -/

def ziskArithFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 64
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskArithLookupGsum330 : LookupCfg where
  name := "Lookup_gsum_[330]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 2; numLookupsM := 23
  grindBitsLookup := 0
def ziskArithLookupGsum331 : LookupCfg where
  name := "Lookup_gsum_[331]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 2097152; numColumnsS := 4; numLookupsM := 1
  grindBitsLookup := 0
def ziskArithLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 2097152; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def ziskArithDeepAli : DeepAliCfg where
  name           := "Arith"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskArithFRI
  numConstraints := 65
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskArithLookupGsum330, ziskArithLookupGsum331, ziskArithLookupGsum5000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Arith: 848 KiB (expected) / 1244 KiB (worst case).
example : ziskArithDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [165, 168, 166])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 165, 168, 166])
    (totalBits := 111)
    (proofSizeExpKib := 848) (proofSizeWorstKib := 1244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskArithDeepAli.ExitCriteria ziskArithJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [165, 168, 166])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 165, 168, 166])
    (totalBits := 128)
    (proofSizeExpKib := 848) (proofSizeWorstKib := 1244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Binary -/

def ziskBinaryFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 49
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskBinaryDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskBinaryLookupGsum125 : LookupCfg where
  name := "Lookup_gsum_[125]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 7; numLookupsM := 8
  grindBitsLookup := 0
def ziskBinaryLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def ziskBinaryDeepAli : DeepAliCfg where
  name           := "Binary"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskBinaryFRI
  numConstraints := 14
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskBinaryDirectGsum5000, ziskBinaryLookupGsum125, ziskBinaryLookupGsum5000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Binary: 826 KiB (expected) / 1227 KiB (worst case).
example : ziskBinaryDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 164, 166])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 164, 166])
    (totalBits := 111)
    (proofSizeExpKib := 826) (proofSizeWorstKib := 1227) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskBinaryDeepAli.ExitCriteria ziskBinaryJBR
    (aliBits := 181) (deepBits := 161)
    (lookupBits := [166, 164, 166])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 181, 161, 166, 164, 166])
    (totalBits := 128)
    (proofSizeExpKib := 826) (proofSizeWorstKib := 1227) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## BinaryAdd -/

def ziskBinaryAddFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 18
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskBinaryAddDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskBinaryAddLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskBinaryAddRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 4
  grindBitsLookup := 0

def ziskBinaryAddDeepAli : DeepAliCfg where
  name           := "BinaryAdd"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskBinaryAddFRI
  numConstraints := 9
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskBinaryAddDirectGsum5000, ziskBinaryAddLookupGsum5000, ziskBinaryAddRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- BinaryAdd: 656 KiB (expected) / 1056 KiB (worst case).
example : ziskBinaryAddDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 166, 167])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 166, 167])
    (totalBits := 111)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskBinaryAddDeepAli.ExitCriteria ziskBinaryAddJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 166, 167])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 166, 167])
    (totalBits := 128)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## BinaryExtension -/

def ziskBinaryExtensionFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 4194304
  batchSize      := 40
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskBinaryExtensionDirectGsum5000 : LookupCfg where
  name := "Direct_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskBinaryExtensionLookupGsum124 : LookupCfg where
  name := "Lookup_gsum_[124]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 7; numLookupsM := 8
  grindBitsLookup := 0
def ziskBinaryExtensionLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskBinaryExtensionRangeCheckGsum102 : LookupCfg where
  name := "Range Check_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 4194304; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskBinaryExtensionDeepAli : DeepAliCfg where
  name           := "BinaryExtension"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- BinaryExtension: 777 KiB (expected) / 1179 KiB (worst case).
example : ziskBinaryExtensionDeepAli.ExitCriteria ziskUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 164, 166, 169])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 164, 166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 777) (proofSizeWorstKib := 1179) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskBinaryExtensionDeepAli.ExitCriteria ziskBinaryExtensionJBR
    (aliBits := 182) (deepBits := 161)
    (lookupBits := [166, 164, 166, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 182, 161, 166, 164, 166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 777) (proofSizeWorstKib := 1179) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Add256 -/

def ziskAdd256FRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 1048576
  batchSize      := 69
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 64
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskAdd256LookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskAdd256PermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 6; numLookupsM := 16
  grindBitsLookup := 0
def ziskAdd256RangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 16
  grindBitsLookup := 0

def ziskAdd256DeepAli : DeepAliCfg where
  name           := "Add256"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskAdd256FRI
  numConstraints := 36
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskAdd256LookupGsum5000, ziskAdd256PermutationGsum10, ziskAdd256RangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Add256: 816 KiB (expected) / 1165 KiB (worst case).
example : ziskAdd256DeepAli.ExitCriteria ziskUDR
    (aliBits := 186) (deepBits := 169)
    (lookupBits := [168, 165, 167])
    (rowBits := [166, 173, 176, 179, 182, 185, 111, 186, 169, 168, 165, 167])
    (totalBits := 111)
    (proofSizeExpKib := 816) (proofSizeWorstKib := 1165) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskAdd256DeepAli.ExitCriteria ziskAdd256JBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 165, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 128, 179, 162, 168, 165, 167])
    (totalBits := 128)
    (proofSizeExpKib := 816) (proofSizeWorstKib := 1165) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq -/

def ziskArithEqFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 1048576
  batchSize      := 470
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 231
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 64
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskArithEqLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskArithEqLookupGsum5002 : LookupCfg where
  name := "Lookup_gsum_[5002]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 2; numLookupsM := 2
  grindBitsLookup := 0
def ziskArithEqPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 6; numLookupsM := 2
  grindBitsLookup := 0
def ziskArithEqRangeCheckGsum103_104 : LookupCfg where
  name := "Range Check_gsum_[103, 104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 3
  grindBitsLookup := 0
def ziskArithEqRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 7
  grindBitsLookup := 0
def ziskArithEqRangeCheckGsum108 : LookupCfg where
  name := "Range Check_gsum_[108]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 6
  grindBitsLookup := 0

def ziskArithEqDeepAli : DeepAliCfg where
  name           := "ArithEq"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq: 2994 KiB (expected) / 3346 KiB (worst case).
example : ziskArithEqDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 169)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [164, 173, 176, 179, 182, 185, 111, 185, 169, 168, 169, 168, 170, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 2994) (proofSizeWorstKib := 3346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskArithEqDeepAli.ExitCriteria ziskArithEqJBR
    (aliBits := 178) (deepBits := 163)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [133, 142, 145, 148, 151, 154, 128, 178, 163, 168, 169, 168, 170, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 2994) (proofSizeWorstKib := 3346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq384 -/

def ziskArithEq384FRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 1048576
  batchSize      := 536
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 232
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 64
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskArithEq384LookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskArithEq384LookupGsum5002 : LookupCfg where
  name := "Lookup_gsum_[5002]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 2; numLookupsM := 2
  grindBitsLookup := 0
def ziskArithEq384PermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 6; numLookupsM := 2
  grindBitsLookup := 0
def ziskArithEq384RangeCheckGsum103_104 : LookupCfg where
  name := "Range Check_gsum_[103, 104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 3
  grindBitsLookup := 0
def ziskArithEq384RangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 7
  grindBitsLookup := 0
def ziskArithEq384RangeCheckGsum108 : LookupCfg where
  name := "Range Check_gsum_[108]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 1048576; numColumnsS := 1; numLookupsM := 6
  grindBitsLookup := 0

def ziskArithEq384DeepAli : DeepAliCfg where
  name           := "ArithEq384"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq384: 3366 KiB (expected) / 3720 KiB (worst case).
example : ziskArithEq384DeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 169)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [163, 173, 176, 179, 182, 185, 112, 185, 169, 168, 169, 168, 170, 169,
                169])
    (totalBits := 112)
    (proofSizeExpKib := 3366) (proofSizeWorstKib := 3720) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskArithEq384DeepAli.ExitCriteria ziskArithEq384JBR
    (aliBits := 179) (deepBits := 163)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [133, 142, 145, 148, 151, 154, 128, 179, 163, 168, 169, 168, 170, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 3366) (proofSizeWorstKib := 3720) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Keccakf -/

def ziskKeccakfFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 131072
  batchSize      := 4065
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 217
  foldingFactors := [8, 8, 8, 8]
  earlyStopDeg   := 64
  grindQuery     := 23
  grindBatch     := 0
  grindCommit    := 0

def ziskKeccakfLookupGsum126 : LookupCfg where
  name := "Lookup_gsum_[126]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 131072; numColumnsS := 4; numLookupsM := 534
  grindBitsLookup := 0
def ziskKeccakfLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 131072; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskKeccakfPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 131072; numColumnsS := 6; numLookupsM := 25
  grindBitsLookup := 0

def ziskKeccakfDeepAli : DeepAliCfg where
  name           := "Keccakf"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskKeccakfFRI
  numConstraints := 2432
  airMaxDegree   := 3
  maxCombo       := 26
  grindDeep      := 0
  lookups        := [ziskKeccakfLookupGsum126, ziskKeccakfLookupGsum5000, ziskKeccakfPermutationGsum10]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Keccakf: 20975 KiB (expected) / 21244 KiB (worst case).
example : ziskKeccakfDeepAli.ExitCriteria ziskUDR
    (aliBits := 180) (deepBits := 172)
    (lookupBits := [163, 171, 167])
    (rowBits := [164, 176, 179, 182, 185, 113, 180, 172, 163, 171, 167])
    (totalBits := 113)
    (proofSizeExpKib := 20975) (proofSizeWorstKib := 21244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskKeccakfDeepAli.ExitCriteria ziskKeccakfJBR
    (aliBits := 174) (deepBits := 166)
    (lookupBits := [163, 171, 167])
    (rowBits := [132, 145, 148, 151, 154, 128, 174, 166, 163, 171, 167])
    (totalBits := 128)
    (proofSizeExpKib := 20975) (proofSizeWorstKib := 21244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Sha256f -/

def ziskSha256fFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 262144
  batchSize      := 1265
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 231
  foldingFactors := [8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskSha256fLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskSha256fPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 262144; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0
def ziskSha256fRangeCheckGsum109 : LookupCfg where
  name := "Range Check_gsum_[109]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 262144; numColumnsS := 1; numLookupsM := 2
  grindBitsLookup := 0

def ziskSha256fDeepAli : DeepAliCfg where
  name           := "Sha256f"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskSha256fFRI
  numConstraints := 115
  airMaxDegree   := 3
  maxCombo       := 87
  grindDeep      := 0
  lookups        := [ziskSha256fLookupGsum5000, ziskSha256fPermutationGsum10, ziskSha256fRangeCheckGsum109]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Sha256f: 7215 KiB (expected) / 7549 KiB (worst case).
example : ziskSha256fDeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 171)
    (lookupBits := [170, 171, 172])
    (rowBits := [164, 175, 178, 181, 184, 187, 111, 185, 171, 170, 171, 172])
    (totalBits := 111)
    (proofSizeExpKib := 7215) (proofSizeWorstKib := 7549) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskSha256fDeepAli.ExitCriteria ziskSha256fJBR
    (aliBits := 178) (deepBits := 165)
    (lookupBits := [170, 171, 172])
    (rowBits := [132, 143, 146, 149, 152, 155, 128, 178, 165, 170, 171, 172])
    (totalBits := 128)
    (proofSizeExpKib := 7215) (proofSizeWorstKib := 7549) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Poseidon2 -/

def ziskPoseidon2FRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 131072
  batchSize      := 182
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 114
  foldingFactors := [8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskPoseidon2LookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 131072; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskPoseidon2PermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 131072; numColumnsS := 6; numLookupsM := 4
  grindBitsLookup := 0

def ziskPoseidon2DeepAli : DeepAliCfg where
  name           := "Poseidon2"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskPoseidon2FRI
  numConstraints := 85
  airMaxDegree   := 4
  maxCombo       := 17
  grindDeep      := 0
  lookups        := [ziskPoseidon2LookupGsum5000, ziskPoseidon2PermutationGsum10]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Poseidon2: 682 KiB (expected) / 832 KiB (worst case).
example : ziskPoseidon2DeepAli.ExitCriteria ziskUDR
    (aliBits := 185) (deepBits := 172)
    (lookupBits := [171, 170])
    (rowBits := [166, 174, 177, 180, 183, 186, 93, 185, 172, 171, 170])
    (totalBits := 93)
    (proofSizeExpKib := 682) (proofSizeWorstKib := 832) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskPoseidon2DeepAli.ExitCriteria ziskPoseidon2JBR
    (aliBits := 177) (deepBits := 164)
    (lookupBits := [171, 170])
    (rowBits := [133, 140, 143, 146, 149, 153, 128, 177, 164, 171, 170])
    (totalBits := 128)
    (proofSizeExpKib := 682) (proofSizeWorstKib := 832) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Blake2br -/

def ziskBlake2brFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 262144
  batchSize      := 651
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskBlake2brLookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 0; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0
def ziskBlake2brPermutationGsum10 : LookupCfg where
  name := "Permutation_gsum_[10]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 262144; numColumnsS := 6; numLookupsM := 4
  grindBitsLookup := 0
def ziskBlake2brPermutationGsum127 : LookupCfg where
  name := "Permutation_gsum_[127]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 262144; numColumnsS := 3; numLookupsM := 1
  grindBitsLookup := 0
def ziskBlake2brRangeCheckGsum103 : LookupCfg where
  name := "Range Check_gsum_[103]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 0; rowsL := 262144; numColumnsS := 1; numLookupsM := 12
  grindBitsLookup := 0

def ziskBlake2brDeepAli : DeepAliCfg where
  name           := "Blake2br"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskBlake2brFRI
  numConstraints := 189
  airMaxDegree   := 3
  maxCombo       := 29
  grindDeep      := 0
  lookups        := [ziskBlake2brLookupGsum5000, ziskBlake2brPermutationGsum10, ziskBlake2brPermutationGsum127, ziskBlake2brRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Blake2br: 3874 KiB (expected) / 4207 KiB (worst case).
example : ziskBlake2brDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [170, 169, 171, 170])
    (rowBits := [165, 175, 178, 181, 184, 187, 111, 184, 171, 170, 169, 171, 170])
    (totalBits := 111)
    (proofSizeExpKib := 3874) (proofSizeWorstKib := 4207) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskBlake2brDeepAli.ExitCriteria ziskBlake2brJBR
    (aliBits := 177) (deepBits := 165)
    (lookupBits := [170, 169, 171, 170])
    (rowBits := [133, 142, 145, 148, 151, 155, 128, 177, 165, 170, 169, 171, 170])
    (totalBits := 128)
    (proofSizeExpKib := 3874) (proofSizeWorstKib := 4207) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## SpecifiedRanges -/

def ziskSpecifiedRangesFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 1048576
  batchSize      := 107
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 229
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 64
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskSpecifiedRangesLookupGsum102 : LookupCfg where
  name := "Lookup_gsum_[102]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskSpecifiedRangesLookupGsum103_104 : LookupCfg where
  name := "Lookup_gsum_[103, 104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskSpecifiedRangesLookupGsum104_105_106_107_108 : LookupCfg where
  name := "Lookup_gsum_[104, 105, 106, 107, 108]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskSpecifiedRangesLookupGsum104 : LookupCfg where
  name := "Lookup_gsum_[104]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskSpecifiedRangesLookupGsum108_109 : LookupCfg where
  name := "Lookup_gsum_[108, 109]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0
def ziskSpecifiedRangesLookupGsum108 : LookupCfg where
  name := "Lookup_gsum_[108]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 0; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 0

def ziskSpecifiedRangesDeepAli : DeepAliCfg where
  name           := "SpecifiedRanges"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- SpecifiedRanges: 1020 KiB (expected) / 1369 KiB (worst case).
example : ziskSpecifiedRangesDeepAli.ExitCriteria ziskUDR
    (aliBits := 187) (deepBits := 169)
    (lookupBits := [171, 171, 171, 171, 171, 171])
    (rowBits := [166, 173, 176, 179, 182, 185, 111, 187, 169, 171, 171, 171, 171, 171,
                171])
    (totalBits := 111)
    (proofSizeExpKib := 1020) (proofSizeWorstKib := 1369) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskSpecifiedRangesDeepAli.ExitCriteria ziskSpecifiedRangesJBR
    (aliBits := 180) (deepBits := 162)
    (lookupBits := [171, 171, 171, 171, 171, 171])
    (rowBits := [132, 139, 142, 145, 148, 151, 128, 180, 162, 171, 171, 171, 171, 171,
                171])
    (totalBits := 128)
    (proofSizeExpKib := 1020) (proofSizeWorstKib := 1369) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## VirtualTable0 -/

def ziskVirtualTable0FRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 69
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskVirtualTable0LookupGsum124_8001 : LookupCfg where
  name := "Lookup_gsum_[124, 8001]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskVirtualTable0LookupGsum125_124 : LookupCfg where
  name := "Lookup_gsum_[125, 124]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskVirtualTable0LookupGsum125 : LookupCfg where
  name := "Lookup_gsum_[125]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskVirtualTable0LookupGsum126_331_8002_133_125 : LookupCfg where
  name := "Lookup_gsum_[126, 331, 8002, 133, 125]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 7; numLookupsM := 1
  grindBitsLookup := 0
def ziskVirtualTable0LookupGsum330 : LookupCfg where
  name := "Lookup_gsum_[330]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 2; numLookupsM := 1
  grindBitsLookup := 0
def ziskVirtualTable0LookupGsum5002_88_77_8003_126 : LookupCfg where
  name := "Lookup_gsum_[5002, 88, 77, 8003, 126]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 4; numLookupsM := 1
  grindBitsLookup := 0

def ziskVirtualTable0DeepAli : DeepAliCfg where
  name           := "VirtualTable0"
  proofSystName  := "DEEP-ALI"
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
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- VirtualTable0: 875 KiB (expected) / 1270 KiB (worst case).
example : ziskVirtualTable0DeepAli.ExitCriteria ziskUDR
    (aliBits := 189) (deepBits := 168)
    (lookupBits := [168, 168, 168, 168, 169, 168])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 189, 168, 168, 168, 168, 168,
                169, 168])
    (totalBits := 111)
    (proofSizeExpKib := 875) (proofSizeWorstKib := 1270) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskVirtualTable0DeepAli.ExitCriteria ziskVirtualTable0JBR
    (aliBits := 182) (deepBits := 162)
    (lookupBits := [168, 168, 168, 168, 169, 168])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 182, 162, 168, 168, 168, 168,
                169, 168])
    (totalBits := 128)
    (proofSizeExpKib := 875) (proofSizeWorstKib := 1270) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## VirtualTable1 -/

def ziskVirtualTable1FRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.half
  denseLen       := 2097152
  batchSize      := 90
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 230
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def ziskVirtualTable1LookupGsum5000 : LookupCfg where
  name := "Lookup_gsum_[5000]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 2097152; rowsL := 0; numColumnsS := 8; numLookupsM := 1
  grindBitsLookup := 0

def ziskVirtualTable1DeepAli : DeepAliCfg where
  name           := "VirtualTable1"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskVirtualTable1FRI
  numConstraints := 6
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [ziskVirtualTable1LookupGsum5000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- VirtualTable1: 989 KiB (expected) / 1384 KiB (worst case).
example : ziskVirtualTable1DeepAli.ExitCriteria ziskUDR
    (aliBits := 189) (deepBits := 168)
    (lookupBits := [167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 189, 168, 167])
    (totalBits := 111)
    (proofSizeExpKib := 989) (proofSizeWorstKib := 1384) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskVirtualTable1DeepAli.ExitCriteria ziskVirtualTable1JBR
    (aliBits := 182) (deepBits := 162)
    (lookupBits := [167])
    (rowBits := [133, 139, 142, 145, 148, 151, 155, 128, 182, 162, 167])
    (totalBits := 128)
    (proofSizeExpKib := 989) (proofSizeWorstKib := 1384) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePost-compressor -/

def ziskDmaPrePostCompressorFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 262144
  batchSize      := 198
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 110
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskDmaPrePostCompressorConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 262144; numColumnsS := 2; numLookupsM := 36
  grindBitsLookup := 0

def ziskDmaPrePostCompressorDeepAli : DeepAliCfg where
  name           := "DmaPrePost-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskDmaPrePostCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskDmaPrePostCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePost-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskDmaPrePostCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskDmaPrePostCompressorDeepAli.ExitCriteria ziskDmaPrePostCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq-compressor -/

def ziskArithEqCompressorFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 262144
  batchSize      := 198
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 110
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskArithEqCompressorConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 262144; numColumnsS := 2; numLookupsM := 36
  grindBitsLookup := 0

def ziskArithEqCompressorDeepAli : DeepAliCfg where
  name           := "ArithEq-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskArithEqCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskArithEqCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskArithEqCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskArithEqCompressorDeepAli.ExitCriteria ziskArithEqCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq384-compressor -/

def ziskArithEq384CompressorFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 262144
  batchSize      := 198
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 110
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskArithEq384CompressorConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 262144; numColumnsS := 2; numLookupsM := 36
  grindBitsLookup := 0

def ziskArithEq384CompressorDeepAli : DeepAliCfg where
  name           := "ArithEq384-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskArithEq384CompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskArithEq384CompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq384-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskArithEq384CompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskArithEq384CompressorDeepAli.ExitCriteria ziskArithEq384CompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Keccakf-compressor -/

def ziskKeccakfCompressorFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 1048576
  batchSize      := 198
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 110
  foldingFactors := [8, 8, 8, 8, 8, 4]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskKeccakfCompressorConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 1048576; numColumnsS := 2; numLookupsM := 36
  grindBitsLookup := 0

def ziskKeccakfCompressorDeepAli : DeepAliCfg where
  name           := "Keccakf-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskKeccakfCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskKeccakfCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Keccakf-compressor: 771 KiB (expected) / 940 KiB (worst case).
example : ziskKeccakfCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 169)
    (lookupBits := [164])
    (rowBits := [163, 171, 174, 177, 180, 183, 186, 94, 184, 169, 164])
    (totalBits := 94)
    (proofSizeExpKib := 771) (proofSizeWorstKib := 940) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskKeccakfCompressorDeepAli.ExitCriteria ziskKeccakfCompressorJBR
    (aliBits := 177) (deepBits := 162)
    (lookupBits := [164])
    (rowBits := [133, 141, 144, 147, 150, 153, 156, 128, 177, 162, 164])
    (totalBits := 128)
    (proofSizeExpKib := 771) (proofSizeWorstKib := 940) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Sha256f-compressor -/

def ziskSha256fCompressorFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 524288
  batchSize      := 198
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 110
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 64
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskSha256fCompressorConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 524288; rowsL := 524288; numColumnsS := 2; numLookupsM := 36
  grindBitsLookup := 0

def ziskSha256fCompressorDeepAli : DeepAliCfg where
  name           := "Sha256f-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskSha256fCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskSha256fCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Sha256f-compressor: 743 KiB (expected) / 892 KiB (worst case).
example : ziskSha256fCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 170)
    (lookupBits := [165])
    (rowBits := [164, 172, 175, 178, 181, 184, 94, 184, 170, 165])
    (totalBits := 94)
    (proofSizeExpKib := 743) (proofSizeWorstKib := 892) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskSha256fCompressorDeepAli.ExitCriteria ziskSha256fCompressorJBR
    (aliBits := 176) (deepBits := 162)
    (lookupBits := [165])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 162, 165])
    (totalBits := 128)
    (proofSizeExpKib := 743) (proofSizeWorstKib := 892) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Blake2br-compressor -/

def ziskBlake2brCompressorFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.quarter
  denseLen       := 262144
  batchSize      := 198
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 110
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskBlake2brCompressorConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 262144; rowsL := 262144; numColumnsS := 2; numLookupsM := 36
  grindBitsLookup := 0

def ziskBlake2brCompressorDeepAli : DeepAliCfg where
  name           := "Blake2br-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskBlake2brCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [ziskBlake2brCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Blake2br-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : ziskBlake2brCompressorDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskBlake2brCompressorDeepAli.ExitCriteria ziskBlake2brCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Recursive2 -/

def ziskRecursive2FRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.eighth
  denseLen       := 131072
  batchSize      := 145
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 73
  foldingFactors := [8, 8, 8, 8, 8]
  earlyStopDeg   := 32
  grindQuery     := 20
  grindBatch     := 0
  grindCommit    := 0

def ziskRecursive2ConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 131072; rowsL := 131072; numColumnsS := 2; numLookupsM := 27
  grindBitsLookup := 0

def ziskRecursive2DeepAli : DeepAliCfg where
  name           := "Recursive2"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskRecursive2FRI
  numConstraints := 158
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [ziskRecursive2ConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Recursive2: 398 KiB (expected) / 487 KiB (worst case).
example : ziskRecursive2DeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [168])
    (rowBits := [166, 173, 176, 179, 182, 185, 80, 184, 171, 168])
    (totalBits := 80)
    (proofSizeExpKib := 398) (proofSizeWorstKib := 487) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskRecursive2DeepAli.ExitCriteria ziskRecursive2JBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [168])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 168])
    (totalBits := 128)
    (proofSizeExpKib := 398) (proofSizeWorstKib := 487) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Final -/

def ziskFinalFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.thirtysecond
  denseLen       := 65536
  batchSize      := 139
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 43
  foldingFactors := [16, 16, 16, 16]
  earlyStopDeg   := 32
  grindQuery     := 22
  grindBatch     := 0
  grindCommit    := 0

def ziskFinalConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 65536; rowsL := 65536; numColumnsS := 2; numLookupsM := 24
  grindBitsLookup := 0

def ziskFinalDeepAli : DeepAliCfg where
  name           := "Final"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskFinalFRI
  numConstraints := 154
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [ziskFinalConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Final: 253 KiB (expected) / 292 KiB (worst case).
example : ziskFinalDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 172)
    (lookupBits := [169])
    (rowBits := [164, 172, 176, 180, 184, 63, 184, 172, 169])
    (totalBits := 63)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskFinalDeepAli.ExitCriteria ziskFinalJBR
    (aliBits := 175) (deepBits := 163)
    (lookupBits := [169])
    (rowBits := [133, 140, 144, 148, 152, 128, 175, 163, 169])
    (totalBits := 128)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Final_Compressed -/

def ziskFinalCompressedFRI : FRIConfig where
  hashBits       := 256
  field          := goldilocks3
  ρ              := Rate.sixteenth
  denseLen       := 32768
  batchSize      := 145
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 54
  foldingFactors := [8, 8, 8]
  earlyStopDeg   := 1024
  grindQuery     := 22
  grindBatch     := 0
  grindCommit    := 0

def ziskFinalCompressedConnectionGprod1 : LookupCfg where
  name := "Connection_gprod_[1]"; field := goldilocks3; isLogUpMultivar := false
  rowsT := 32768; rowsL := 32768; numColumnsS := 2; numLookupsM := 27
  grindBitsLookup := 0

def ziskFinalCompressedDeepAli : DeepAliCfg where
  name           := "Final_Compressed"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri ziskFinalCompressedFRI
  numConstraints := 158
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [ziskFinalCompressedConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Final_Compressed: 269 KiB (expected) / 313 KiB (worst case).
example : ziskFinalCompressedDeepAli.ExitCriteria ziskUDR
    (aliBits := 184) (deepBits := 173)
    (lookupBits := [170])
    (rowBits := [166, 174, 177, 180, 71, 184, 173, 170])
    (totalBits := 71)
    (proofSizeExpKib := 269) (proofSizeWorstKib := 313) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : ziskFinalCompressedDeepAli.ExitCriteria ziskFinalCompressedJBR
    (aliBits := 175) (deepBits := 164)
    (lookupBits := [170])
    (rowBits := [134, 141, 144, 147, 128, 175, 164, 170])
    (totalBits := 128)
    (proofSizeExpKib := 269) (proofSizeWorstKib := 313) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

end Soundcalc
