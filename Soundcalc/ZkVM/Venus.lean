import Soundcalc.Circuit.DeepAli
import Soundcalc.PCS.FRI
import Soundcalc.Lookup
import Soundcalc.Field.Goldilocks

/-!
# Venus soundness configuration

Venus is a DEEP-ALI zkVM (over Goldilocks³), so — like Pico — it only needs
`Soundcalc.Circuit.DeepAli`. Every literal below is derived from
`soundcalc/zkvms/venus/venus.toml` and cross-checked, cell by cell, against
`reports/venus.md` (<https://github.com/ethereum/soundcalc/blob/main/reports/venus.md>).

## Two-regime strategy

* **UDR** (`venusUDR`): classical unique-decoding threshold, shared by every circuit.
* **JBR**: Johnson Bound Regime. Unlike Airbender/OpenVM/Pico — which leave the gap
  to BCHKS25's default formula — every Venus circuit **pins** its gap via
  `gap_to_radius`. In `soundcalc`'s `get_proximity_parameter` the proximity
  parameter is `1 - √ρ - gap`; here the variable named `η` *is that gap* (note
  `θ = (1 - η) - √ρ`), so pinning `gap_to_radius` means passing `JBR`'s optional
  `gapToRadius = some gap`, collapsing `etaLB = etaUB = gap`. Every Venus
  `gap_to_radius` is an exact multiple of `1/3000`.

`g = 2^40` is the same `√ρ`-enclosure granularity used by Airbender/OpenVM/Pico.
-/

namespace Soundcalc

/-! ## Venus config constructors

Each circuit's `FRIConfig`/`LookupCfg`/`JBR` regime shares the same Goldilocks constants; these
helpers bake those in so every instance below is a one-liner. Each call still produces a *separate*
object, free to diverge later. -/

/-- `JBR` over Goldilocks, `g = 2^40`, `gap = n/3000`. -/
abbrev venusJBR (n : ℕ) : Regime := JBR goldilocks3 (2 ^ 40) (some (n / 3000))

/-- Univariate-logup lookup over Goldilocks, no grinding. -/
abbrev venusLookup (name : String) (rowsT rowsL numColumnsS numLookupsM : ℕ) : LookupCfg where
  name := name; field := goldilocks3; isLogUpMultivar := false
  rowsT := rowsT; rowsL := rowsL; numColumnsS := numColumnsS; numLookupsM := numLookupsM
  grindBitsLookup := 0

/-- FRI over Goldilocks: power batching, 256-bit hash, no batch/commit grinding.
    `h_earlyStop` is an auto-param, so it is discharged by `native_decide` on the *concrete*
    arguments at each call site (it cannot be proved from the symbolic parameters here). -/
abbrev venusFRI (ρ : Rate) (denseLen batchSize numQueries earlyStopDeg grindQuery : ℕ)
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

abbrev venusUDR : Regime := UDR goldilocks3

/-- `Dma`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusDmaJBR := venusJBR 16
/-- `DmaMemCpy`: gap_to_radius = 0.005 = 15/3000. -/
abbrev venusDmaMemCpyJBR := venusJBR 15
/-- `DmaInputCpy`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev venusDmaInputCpyJBR := venusJBR 14
/-- `Dma64Aligned`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev venusDma64AlignedJBR := venusJBR 17
/-- `Dma64AlignedInputCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusDma64AlignedInputCpyJBR := venusJBR 16
/-- `Dma64AlignedMemSet`: gap_to_radius = 0.005 = 15/3000. -/
abbrev venusDma64AlignedMemSetJBR := venusJBR 15
/-- `Dma64AlignedMem`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusDma64AlignedMemJBR := venusJBR 16
/-- `Dma64AlignedMemCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusDma64AlignedMemCpyJBR := venusJBR 16
/-- `DmaUnaligned`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusDmaUnalignedJBR := venusJBR 16
/-- `DmaPrePost`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev venusDmaPrePostJBR := venusJBR 18
/-- `DmaPrePostMemCpy`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev venusDmaPrePostMemCpyJBR := venusJBR 17
/-- `DmaPrePostInputCpy`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusDmaPrePostInputCpyJBR := venusJBR 16
/-- `Main`: gap_to_radius = 0.006333333333333333 = 19/3000. -/
abbrev venusMainJBR := venusJBR 19
/-- `Rom`: gap_to_radius = 0.005 = 15/3000. -/
abbrev venusRomJBR := venusJBR 15
/-- `Mem`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev venusMemJBR := venusJBR 17
/-- `RomData`: gap_to_radius = 0.004333333333333333 = 13/3000. -/
abbrev venusRomDataJBR := venusJBR 13
/-- `InputData`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev venusInputDataJBR := venusJBR 14
/-- `MemAlign`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev venusMemAlignJBR := venusJBR 17
/-- `MemAlignByte`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusMemAlignByteJBR := venusJBR 16
/-- `MemAlignReadByte`: gap_to_radius = 0.005 = 15/3000. -/
abbrev venusMemAlignReadByteJBR := venusJBR 15
/-- `MemAlignWriteByte`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusMemAlignWriteByteJBR := venusJBR 16
/-- `Arith`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev venusArithJBR := venusJBR 17
/-- `Binary`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev venusBinaryJBR := venusJBR 18
/-- `BinaryAdd`: gap_to_radius = 0.005 = 15/3000. -/
abbrev venusBinaryAddJBR := venusJBR 15
/-- `BinaryExtension`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev venusBinaryExtensionJBR := venusJBR 18
/-- `Add256`: gap_to_radius = 0.005 = 15/3000. -/
abbrev venusAdd256JBR := venusJBR 15
/-- `ArithEq`: gap_to_radius = 0.007333333333333333 = 22/3000. -/
abbrev venusArithEqJBR := venusJBR 22
/-- `ArithEq384`: gap_to_radius = 0.007666666666666666 = 23/3000. -/
abbrev venusArithEq384JBR := venusJBR 23
/-- `Keccakf`: gap_to_radius = 0.007333333333333333 = 22/3000. -/
abbrev venusKeccakfJBR := venusJBR 22
/-- `Sha256f`: gap_to_radius = 0.006666666666666666 = 20/3000. -/
abbrev venusSha256fJBR := venusJBR 20
/-- `Poseidon2`: gap_to_radius = 0.004 = 12/3000. -/
abbrev venusPoseidon2JBR := venusJBR 12
/-- `Blake2br`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev venusBlake2brJBR := venusJBR 18
/-- `SpecifiedRanges`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusSpecifiedRangesJBR := venusJBR 16
/-- `VirtualTable0`: gap_to_radius = 0.005666666666666667 = 17/3000. -/
abbrev venusVirtualTable0JBR := venusJBR 17
/-- `VirtualTable1`: gap_to_radius = 0.005999999999999999 = 18/3000. -/
abbrev venusVirtualTable1JBR := venusJBR 18
/-- `DmaPrePost-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev venusDmaPrePostCompressorJBR := venusJBR 14
/-- `ArithEq-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev venusArithEqCompressorJBR := venusJBR 14
/-- `ArithEq384-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev venusArithEq384CompressorJBR := venusJBR 14
/-- `Keccakf-compressor`: gap_to_radius = 0.006333333333333333 = 19/3000. -/
abbrev venusKeccakfCompressorJBR := venusJBR 19
/-- `Sha256f-compressor`: gap_to_radius = 0.005333333333333333 = 16/3000. -/
abbrev venusSha256fCompressorJBR := venusJBR 16
/-- `Blake2br-compressor`: gap_to_radius = 0.004666666666666667 = 14/3000. -/
abbrev venusBlake2brCompressorJBR := venusJBR 14
/-- `Recursive2`: gap_to_radius = 0.004 = 12/3000. -/
abbrev venusRecursive2JBR := venusJBR 12
/-- `Final`: gap_to_radius = 0.003333333333333333 = 10/3000. -/
abbrev venusFinalJBR := venusJBR 10
/-- `Final_Compressed`: gap_to_radius = 0.003333333333333333 = 10/3000. -/
abbrev venusFinalCompressedJBR := venusJBR 10

/-! ## Dma -/

def venusDmaFRI := venusFRI Rate.half 2097152 46 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1
def venusDmaLookupGsum77 := venusLookup "Lookup_gsum_[77]" 0 2097152 2 1
def venusDmaLookupGsum8001 := venusLookup "Lookup_gsum_[8001]" 0 2097152 7 1
def venusDmaPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 1
def venusDmaPermutationGsum8000 := venusLookup "Permutation_gsum_[8000]" 0 2097152 11 2
def venusDmaRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 1
def venusDmaRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2
def venusDmaRangeCheckGsum104 := venusLookup "Range Check_gsum_[104]" 0 2097152 1 2

def venusDmaDeepAli : DeepAliCfg where
  name           := "Dma"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaFRI
  numConstraints := 49
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaLookupGsum5000,
                     venusDmaLookupGsum77,
                     venusDmaLookupGsum8001,
                     venusDmaPermutationGsum10,
                     venusDmaPermutationGsum8000,
                     venusDmaRangeCheckGsum102,
                     venusDmaRangeCheckGsum103,
                     venusDmaRangeCheckGsum104]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma: 748 KiB (expected) / 1142 KiB (worst case).
example : venusDmaDeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 166, 169, 168, 168,
                166, 170, 169, 169])
    (totalBits := 111)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaDeepAli.ExitCriteria venusDmaJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 179, 161, 166, 169, 168, 168,
                166, 170, 169, 169])
    (totalBits := 128)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaMemCpy -/

def venusDmaMemCpyFRI := venusFRI Rate.half 2097152 33 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaMemCpyLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1
def venusDmaMemCpyLookupGsum77 := venusLookup "Lookup_gsum_[77]" 0 2097152 2 1
def venusDmaMemCpyLookupGsum8001 := venusLookup "Lookup_gsum_[8001]" 0 2097152 7 1
def venusDmaMemCpyPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 1
def venusDmaMemCpyPermutationGsum8000 := venusLookup "Permutation_gsum_[8000]" 0 2097152 11 2
def venusDmaMemCpyRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 1
def venusDmaMemCpyRangeCheckGsum104 := venusLookup "Range Check_gsum_[104]" 0 2097152 1 2

def venusDmaMemCpyDeepAli : DeepAliCfg where
  name           := "DmaMemCpy"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaMemCpyFRI
  numConstraints := 22
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaMemCpyLookupGsum5000,
                     venusDmaMemCpyLookupGsum77,
                     venusDmaMemCpyLookupGsum8001,
                     venusDmaMemCpyPermutationGsum10,
                     venusDmaMemCpyPermutationGsum8000,
                     venusDmaMemCpyRangeCheckGsum102,
                     venusDmaMemCpyRangeCheckGsum104]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaMemCpy: 679 KiB (expected) / 1072 KiB (worst case).
example : venusDmaMemCpyDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 187, 168, 166, 169, 168, 168,
                166, 170, 169])
    (totalBits := 111)
    (proofSizeExpKib := 679) (proofSizeWorstKib := 1072) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaMemCpyDeepAli.ExitCriteria venusDmaMemCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [166, 169, 168, 168, 166, 170, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 180, 161, 166, 169, 168, 168,
                166, 170, 169])
    (totalBits := 128)
    (proofSizeExpKib := 679) (proofSizeWorstKib := 1072) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaInputCpy -/

def venusDmaInputCpyFRI := venusFRI Rate.half 2097152 27 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaInputCpyLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1
def venusDmaInputCpyLookupGsum8001 := venusLookup "Lookup_gsum_[8001]" 0 2097152 7 1
def venusDmaInputCpyPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 1
def venusDmaInputCpyPermutationGsum8000 := venusLookup "Permutation_gsum_[8000]" 0 2097152 11 2
def venusDmaInputCpyRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 1
def venusDmaInputCpyRangeCheckGsum104 := venusLookup "Range Check_gsum_[104]" 0 2097152 1 1
def venusDmaInputCpyRangeCheckGsum105 := venusLookup "Range Check_gsum_[105]" 0 2097152 1 1

def venusDmaInputCpyDeepAli : DeepAliCfg where
  name           := "DmaInputCpy"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaInputCpyFRI
  numConstraints := 20
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaInputCpyLookupGsum5000,
                     venusDmaInputCpyLookupGsum8001,
                     venusDmaInputCpyPermutationGsum10,
                     venusDmaInputCpyPermutationGsum8000,
                     venusDmaInputCpyRangeCheckGsum102,
                     venusDmaInputCpyRangeCheckGsum104,
                     venusDmaInputCpyRangeCheckGsum105]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaInputCpy: 646 KiB (expected) / 1040 KiB (worst case).
example : venusDmaInputCpyDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [166, 168, 168, 166, 170, 170, 170])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 166, 168, 168, 166,
                170, 170, 170])
    (totalBits := 111)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaInputCpyDeepAli.ExitCriteria venusDmaInputCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [166, 168, 168, 166, 170, 170, 170])
    (rowBits := [133, 137, 140, 143, 146, 149, 153, 128, 180, 161, 166, 168, 168, 166,
                170, 170, 170])
    (totalBits := 128)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64Aligned -/

def venusDma64AlignedFRI := venusFRI Rate.half 2097152 62 230 32 16 [8, 8, 8, 8, 8, 4]

def venusDma64AlignedDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 2097152 11 1
def venusDma64AlignedDirectGsum8200 := venusLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def venusDma64AlignedLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def venusDma64AlignedLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 2097152 2 4
def venusDma64AlignedPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 9
def venusDma64AlignedRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 8
def venusDma64AlignedRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2

def venusDma64AlignedDeepAli : DeepAliCfg where
  name           := "Dma64Aligned"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDma64AlignedFRI
  numConstraints := 88
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDma64AlignedDirectGsum5000,
                     venusDma64AlignedDirectGsum8200,
                     venusDma64AlignedLookupGsum5000,
                     venusDma64AlignedLookupGsum88,
                     venusDma64AlignedPermutationGsum10,
                     venusDma64AlignedRangeCheckGsum102,
                     venusDma64AlignedRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64Aligned: 838 KiB (expected) / 1233 KiB (worst case).
example : venusDma64AlignedDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 167, 165, 167, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 167,
                165, 167, 169])
    (totalBits := 111)
    (proofSizeExpKib := 838) (proofSizeWorstKib := 1233) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDma64AlignedDeepAli.ExitCriteria venusDma64AlignedJBR
    (aliBits := 178) (deepBits := 162)
    (lookupBits := [167, 166, 167, 167, 165, 167, 169])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 178, 162, 167, 166, 167, 167,
                165, 167, 169])
    (totalBits := 128)
    (proofSizeExpKib := 838) (proofSizeWorstKib := 1233) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedInputCpy -/

def venusDma64AlignedInputCpyFRI := venusFRI Rate.half 2097152 44 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDma64AlignedInputCpyDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 2097152 11 1
def venusDma64AlignedInputCpyDirectGsum8200 := venusLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def venusDma64AlignedInputCpyLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def venusDma64AlignedInputCpyLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 2097152 2 4
def venusDma64AlignedInputCpyPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 4
def venusDma64AlignedInputCpyRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 8
def venusDma64AlignedInputCpyRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2

def venusDma64AlignedInputCpyDeepAli : DeepAliCfg where
  name           := "Dma64AlignedInputCpy"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDma64AlignedInputCpyFRI
  numConstraints := 52
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDma64AlignedInputCpyDirectGsum5000,
                     venusDma64AlignedInputCpyDirectGsum8200,
                     venusDma64AlignedInputCpyLookupGsum5000,
                     venusDma64AlignedInputCpyLookupGsum88,
                     venusDma64AlignedInputCpyPermutationGsum10,
                     venusDma64AlignedInputCpyRangeCheckGsum102,
                     venusDma64AlignedInputCpyRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedInputCpy: 738 KiB (expected) / 1131 KiB (worst case).
example : venusDma64AlignedInputCpyDeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [167, 166, 167, 167, 166, 167, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 167, 166, 167, 167,
                166, 167, 169])
    (totalBits := 111)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDma64AlignedInputCpyDeepAli.ExitCriteria venusDma64AlignedInputCpyJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [167, 166, 167, 167, 166, 167, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 179, 161, 167, 166, 167, 167,
                166, 167, 169])
    (totalBits := 128)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedMemSet -/

def venusDma64AlignedMemSetFRI := venusFRI Rate.half 2097152 30 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDma64AlignedMemSetDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 2097152 11 1
def venusDma64AlignedMemSetDirectGsum8200 := venusLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def venusDma64AlignedMemSetLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def venusDma64AlignedMemSetPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 8
def venusDma64AlignedMemSetRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2

def venusDma64AlignedMemSetDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMemSet"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDma64AlignedMemSetFRI
  numConstraints := 62
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDma64AlignedMemSetDirectGsum5000,
                     venusDma64AlignedMemSetDirectGsum8200,
                     venusDma64AlignedMemSetLookupGsum5000,
                     venusDma64AlignedMemSetPermutationGsum10,
                     venusDma64AlignedMemSetRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedMemSet: 662 KiB (expected) / 1056 KiB (worst case).
example : venusDma64AlignedMemSetDeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 186, 168, 167, 166, 167, 165,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 662) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDma64AlignedMemSetDeepAli.ExitCriteria venusDma64AlignedMemSetJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 178, 161, 167, 166, 167, 165,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 662) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedMem -/

def venusDma64AlignedMemFRI := venusFRI Rate.half 2097152 46 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDma64AlignedMemDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 2097152 11 1
def venusDma64AlignedMemDirectGsum8200 := venusLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def venusDma64AlignedMemLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def venusDma64AlignedMemPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 9
def venusDma64AlignedMemRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2

def venusDma64AlignedMemDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMem"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDma64AlignedMemFRI
  numConstraints := 81
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDma64AlignedMemDirectGsum5000,
                     venusDma64AlignedMemDirectGsum8200,
                     venusDma64AlignedMemLookupGsum5000,
                     venusDma64AlignedMemPermutationGsum10,
                     venusDma64AlignedMemRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedMem: 748 KiB (expected) / 1142 KiB (worst case).
example : venusDma64AlignedMemDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 165,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDma64AlignedMemDeepAli.ExitCriteria venusDma64AlignedMemJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 165, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 166, 167, 165,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 748) (proofSizeWorstKib := 1142) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Dma64AlignedMemCpy -/

def venusDma64AlignedMemCpyFRI := venusFRI Rate.half 2097152 52 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDma64AlignedMemCpyDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 2097152 11 1
def venusDma64AlignedMemCpyDirectGsum8200 := venusLookup "Direct_gsum_[8200]" 2097152 2097152 10 1
def venusDma64AlignedMemCpyLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def venusDma64AlignedMemCpyPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 17
def venusDma64AlignedMemCpyRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2

def venusDma64AlignedMemCpyDeepAli : DeepAliCfg where
  name           := "Dma64AlignedMemCpy"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDma64AlignedMemCpyFRI
  numConstraints := 69
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDma64AlignedMemCpyDirectGsum5000,
                     venusDma64AlignedMemCpyDirectGsum8200,
                     venusDma64AlignedMemCpyLookupGsum5000,
                     venusDma64AlignedMemCpyPermutationGsum10,
                     venusDma64AlignedMemCpyRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Dma64AlignedMemCpy: 781 KiB (expected) / 1174 KiB (worst case).
example : venusDma64AlignedMemCpyDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 166, 167, 164, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 166, 167, 164,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDma64AlignedMemCpyDeepAli.ExitCriteria venusDma64AlignedMemCpyJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 166, 167, 164, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 166, 167, 164,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaUnaligned -/

def venusDmaUnalignedFRI := venusFRI Rate.half 2097152 52 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaUnalignedDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 2097152 11 1
def venusDmaUnalignedDirectGsum8201 := venusLookup "Direct_gsum_[8201]" 2097152 2097152 18 1
def venusDmaUnalignedLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 11 1
def venusDmaUnalignedLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 2097152 2 4
def venusDmaUnalignedPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 2097152 2097152 6 2
def venusDmaUnalignedRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 2

def venusDmaUnalignedDeepAli : DeepAliCfg where
  name           := "DmaUnaligned"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaUnalignedFRI
  numConstraints := 75
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaUnalignedDirectGsum5000,
                     venusDmaUnalignedDirectGsum8201,
                     venusDmaUnalignedLookupGsum5000,
                     venusDmaUnalignedLookupGsum88,
                     venusDmaUnalignedPermutationGsum10,
                     venusDmaUnalignedRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaUnaligned: 781 KiB (expected) / 1174 KiB (worst case).
example : venusDmaUnalignedDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [167, 165, 167, 167, 166, 169])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 167, 165, 167, 167,
                166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaUnalignedDeepAli.ExitCriteria venusDmaUnalignedJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [167, 165, 167, 167, 166, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 178, 161, 167, 165, 167, 167,
                166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 781) (proofSizeWorstKib := 1174) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePost -/

def venusDmaPrePostFRI := venusFRI Rate.half 2097152 83 230 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaPrePostLookupGsum8002 := venusLookup "Lookup_gsum_[8002]" 0 2097152 6 1
def venusDmaPrePostLookupGsum8003 := venusLookup "Lookup_gsum_[8003]" 0 2097152 3 1
def venusDmaPrePostLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 2097152 2 12
def venusDmaPrePostPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 4
def venusDmaPrePostPermutationGsum8000 := venusLookup "Permutation_gsum_[8000]" 2097152 0 11 1

def venusDmaPrePostDeepAli : DeepAliCfg where
  name           := "DmaPrePost"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaPrePostFRI
  numConstraints := 69
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaPrePostLookupGsum8002,
                     venusDmaPrePostLookupGsum8003,
                     venusDmaPrePostLookupGsum88,
                     venusDmaPrePostPermutationGsum10,
                     venusDmaPrePostPermutationGsum8000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePost: 951 KiB (expected) / 1346 KiB (worst case).
example : venusDmaPrePostDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [168, 169, 166, 166, 167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 185, 168, 168, 169, 166, 166,
                167])
    (totalBits := 111)
    (proofSizeExpKib := 951) (proofSizeWorstKib := 1346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaPrePostDeepAli.ExitCriteria venusDmaPrePostJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 169, 166, 166, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 155, 128, 179, 162, 168, 169, 166, 166,
                167])
    (totalBits := 128)
    (proofSizeExpKib := 951) (proofSizeWorstKib := 1346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePostMemCpy -/

def venusDmaPrePostMemCpyFRI := venusFRI Rate.half 2097152 70 230 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaPrePostMemCpyLookupGsum8002 := venusLookup "Lookup_gsum_[8002]" 0 2097152 6 1
def venusDmaPrePostMemCpyLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 2097152 2 12
def venusDmaPrePostMemCpyPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 4
def venusDmaPrePostMemCpyPermutationGsum8000 := venusLookup "Permutation_gsum_[8000]" 2097152 0 11 1

def venusDmaPrePostMemCpyDeepAli : DeepAliCfg where
  name           := "DmaPrePostMemCpy"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaPrePostMemCpyFRI
  numConstraints := 38
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaPrePostMemCpyLookupGsum8002,
                     venusDmaPrePostMemCpyLookupGsum88,
                     venusDmaPrePostMemCpyPermutationGsum10,
                     venusDmaPrePostMemCpyPermutationGsum8000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePostMemCpy: 881 KiB (expected) / 1276 KiB (worst case).
example : venusDmaPrePostMemCpyDeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [168, 166, 166, 167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 186, 168, 168, 166, 166, 167])
    (totalBits := 111)
    (proofSizeExpKib := 881) (proofSizeWorstKib := 1276) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaPrePostMemCpyDeepAli.ExitCriteria venusDmaPrePostMemCpyJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 166, 166, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 168, 166, 166, 167])
    (totalBits := 128)
    (proofSizeExpKib := 881) (proofSizeWorstKib := 1276) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePostInputCpy -/

def venusDmaPrePostInputCpyFRI := venusFRI Rate.half 2097152 44 229 32 16 [8, 8, 8, 8, 8, 4]

def venusDmaPrePostInputCpyLookupGsum8002 := venusLookup "Lookup_gsum_[8002]" 0 2097152 6 1
def venusDmaPrePostInputCpyLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 2097152 2 8
def venusDmaPrePostInputCpyPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 2
def venusDmaPrePostInputCpyPermutationGsum8000 := venusLookup "Permutation_gsum_[8000]" 2097152 0 11 1

def venusDmaPrePostInputCpyDeepAli : DeepAliCfg where
  name           := "DmaPrePostInputCpy"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaPrePostInputCpyFRI
  numConstraints := 20
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusDmaPrePostInputCpyLookupGsum8002,
                     venusDmaPrePostInputCpyLookupGsum88,
                     venusDmaPrePostInputCpyPermutationGsum10,
                     venusDmaPrePostInputCpyPermutationGsum8000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePostInputCpy: 738 KiB (expected) / 1131 KiB (worst case).
example : venusDmaPrePostInputCpyDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [168, 166, 167, 167])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 187, 168, 168, 166, 167, 167])
    (totalBits := 111)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaPrePostInputCpyDeepAli.ExitCriteria venusDmaPrePostInputCpyJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [168, 166, 167, 167])
    (rowBits := [133, 138, 141, 144, 147, 150, 154, 128, 180, 161, 168, 166, 167, 167])
    (totalBits := 128)
    (proofSizeExpKib := 738) (proofSizeWorstKib := 1131) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Main -/

def venusMainFRI := venusFRI Rate.half 4194304 61 230 32 16 [8, 8, 8, 8, 8, 8]

def venusMainDirectGsum1000 := venusLookup "Direct_gsum_[1000]" 4194304 4194304 5 1
def venusMainLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 0 4194304 11 1
def venusMainLookupGsum7890 := venusLookup "Lookup_gsum_[7890]" 0 4194304 11 1
def venusMainPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 4194304 4194304 6 34
def venusMainRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 4194304 1 34
def venusMainRangeCheckGsum106 := venusLookup "Range Check_gsum_[106]" 0 4194304 1 1

def venusMainDeepAli : DeepAliCfg where
  name           := "Main"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusMainFRI
  numConstraints := 144
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusMainDirectGsum1000,
                     venusMainLookupGsum5000,
                     venusMainLookupGsum7890,
                     venusMainPermutationGsum10,
                     venusMainRangeCheckGsum102,
                     venusMainRangeCheckGsum106]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Main: 890 KiB (expected) / 1292 KiB (worst case).
example : venusMainDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 167)
    (lookupBits := [166, 166, 166, 161, 164, 169])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 184, 167, 166, 166, 166, 161,
                164, 169])
    (totalBits := 111)
    (proofSizeExpKib := 890) (proofSizeWorstKib := 1292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusMainDeepAli.ExitCriteria venusMainJBR
    (aliBits := 178) (deepBits := 161)
    (lookupBits := [166, 166, 166, 161, 164, 169])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 178, 161, 166, 166, 166, 161,
                164, 169])
    (totalBits := 128)
    (proofSizeExpKib := 890) (proofSizeWorstKib := 1292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Rom -/

def venusRomFRI := venusFRI Rate.half 4194304 18 221 32 20 [8, 8, 8, 8, 8, 8]

def venusRomLookupGsum7890 := venusLookup "Lookup_gsum_[7890]" 4194304 0 11 1

def venusRomDeepAli : DeepAliCfg where
  name           := "Rom"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusRomFRI
  numConstraints := 3
  airMaxDegree   := 2
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusRomLookupGsum7890]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Rom: 635 KiB (expected) / 1019 KiB (worst case).
example : venusRomDeepAli.ExitCriteria venusUDR
    (aliBits := 190) (deepBits := 168)
    (lookupBits := [166])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 190, 168, 166])
    (totalBits := 111)
    (proofSizeExpKib := 635) (proofSizeWorstKib := 1019) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusRomDeepAli.ExitCriteria venusRomJBR
    (aliBits := 183) (deepBits := 161)
    (lookupBits := [166])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 183, 161, 166])
    (totalBits := 128)
    (proofSizeExpKib := 635) (proofSizeWorstKib := 1019) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Mem -/

def venusMemFRI := venusFRI Rate.half 4194304 29 230 32 16 [8, 8, 8, 8, 8, 8]

def venusMemDirectGsum11 := venusLookup "Direct_gsum_[11]" 4194304 4194304 6 1
def venusMemPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 4194304 0 6 1
def venusMemRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 4194304 1 1
def venusMemRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 4194304 1 5
def venusMemRangeCheckGsum104 := venusLookup "Range Check_gsum_[104]" 0 4194304 1 1

def venusMemDeepAli : DeepAliCfg where
  name           := "Mem"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusMemFRI
  numConstraints := 34
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusMemDirectGsum11, venusMemPermutationGsum10, venusMemRangeCheckGsum102, venusMemRangeCheckGsum103, venusMemRangeCheckGsum104]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Mem: 718 KiB (expected) / 1120 KiB (worst case).
example : venusMemDeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 167)
    (lookupBits := [166, 167, 169, 167, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 186, 167, 166, 167, 169, 167,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 718) (proofSizeWorstKib := 1120) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusMemDeepAli.ExitCriteria venusMemJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [166, 167, 169, 167, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 179, 161, 166, 167, 169, 167,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 718) (proofSizeWorstKib := 1120) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## RomData -/

def venusRomDataFRI := venusFRI Rate.half 2097152 19 229 32 16 [8, 8, 8, 8, 8, 4]

def venusRomDataDirectGsum11 := venusLookup "Direct_gsum_[11]" 2097152 2097152 6 1
def venusRomDataPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 2097152 0 6 1
def venusRomDataRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 3

def venusRomDataDeepAli : DeepAliCfg where
  name           := "RomData"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusRomDataFRI
  numConstraints := 23
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusRomDataDirectGsum11, venusRomDataPermutationGsum10, venusRomDataRangeCheckGsum102]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- RomData: 603 KiB (expected) / 997 KiB (worst case).
example : venusRomDataDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [167, 168, 169])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 167, 168, 169])
    (totalBits := 111)
    (proofSizeExpKib := 603) (proofSizeWorstKib := 997) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusRomDataDeepAli.ExitCriteria venusRomDataJBR
    (aliBits := 180) (deepBits := 161)
    (lookupBits := [167, 168, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 180, 161, 167, 168, 169])
    (totalBits := 128)
    (proofSizeExpKib := 603) (proofSizeWorstKib := 997) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## InputData -/

def venusInputDataFRI := venusFRI Rate.half 2097152 27 229 32 16 [8, 8, 8, 8, 8, 4]

def venusInputDataDirectGsum11 := venusLookup "Direct_gsum_[11]" 2097152 2097152 6 1
def venusInputDataPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 2097152 0 6 1
def venusInputDataRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 2097152 1 1
def venusInputDataRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 2097152 1 8

def venusInputDataDeepAli : DeepAliCfg where
  name           := "InputData"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusInputDataFRI
  numConstraints := 30
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusInputDataDirectGsum11, venusInputDataPermutationGsum10, venusInputDataRangeCheckGsum102, venusInputDataRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- InputData: 646 KiB (expected) / 1040 KiB (worst case).
example : venusInputDataDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 168)
    (lookupBits := [167, 168, 170, 167])
    (rowBits := [167, 172, 175, 178, 181, 184, 187, 111, 187, 168, 167, 168, 170, 167])
    (totalBits := 111)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusInputDataDeepAli.ExitCriteria venusInputDataJBR
    (aliBits := 179) (deepBits := 161)
    (lookupBits := [167, 168, 170, 167])
    (rowBits := [133, 137, 140, 143, 146, 149, 153, 128, 179, 161, 167, 168, 170, 167])
    (totalBits := 128)
    (proofSizeExpKib := 646) (proofSizeWorstKib := 1040) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlign -/

def venusMemAlignFRI := venusFRI Rate.half 2097152 59 230 32 16 [8, 8, 8, 8, 8, 4]

def venusMemAlignLookupGsum133 := venusLookup "Lookup_gsum_[133]" 0 2097152 6 1
def venusMemAlignPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 2097152 6 1
def venusMemAlignRangeCheckGsum107 := venusLookup "Range Check_gsum_[107]" 0 2097152 1 8

def venusMemAlignDeepAli : DeepAliCfg where
  name           := "MemAlign"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusMemAlignFRI
  numConstraints := 40
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusMemAlignLookupGsum133, venusMemAlignPermutationGsum10, venusMemAlignRangeCheckGsum107]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlign: 821 KiB (expected) / 1217 KiB (worst case).
example : venusMemAlignDeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 168)
    (lookupBits := [168, 168, 167])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 186, 168, 168, 168, 167])
    (totalBits := 111)
    (proofSizeExpKib := 821) (proofSizeWorstKib := 1217) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusMemAlignDeepAli.ExitCriteria venusMemAlignJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 168, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 168, 168, 167])
    (totalBits := 128)
    (proofSizeExpKib := 821) (proofSizeWorstKib := 1217) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlignByte -/

def venusMemAlignByteFRI := venusFRI Rate.half 4194304 25 229 32 16 [8, 8, 8, 8, 8, 8]

def venusMemAlignByteDirectGsum10 := venusLookup "Direct_gsum_[10]" 4194304 4194304 6 1
def venusMemAlignByteLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 4194304 2 1
def venusMemAlignBytePermutationGsum10 := venusLookup "Permutation_gsum_[10]" 4194304 4194304 6 2
def venusMemAlignByteRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 4194304 1 1
def venusMemAlignByteRangeCheckGsum107 := venusLookup "Range Check_gsum_[107]" 0 4194304 1 1

def venusMemAlignByteDeepAli : DeepAliCfg where
  name           := "MemAlignByte"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusMemAlignByteFRI
  numConstraints := 16
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusMemAlignByteDirectGsum10,
                     venusMemAlignByteLookupGsum88,
                     venusMemAlignBytePermutationGsum10,
                     venusMemAlignByteRangeCheckGsum103,
                     venusMemAlignByteRangeCheckGsum107]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlignByte: 694 KiB (expected) / 1093 KiB (worst case).
example : venusMemAlignByteDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 167)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 187, 167, 166, 168, 165, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 694) (proofSizeWorstKib := 1093) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusMemAlignByteDeepAli.ExitCriteria venusMemAlignByteJBR
    (aliBits := 180) (deepBits := 160)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 180, 160, 166, 168, 165, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 694) (proofSizeWorstKib := 1093) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlignReadByte -/

def venusMemAlignReadByteFRI := venusFRI Rate.half 4194304 18 229 32 16 [8, 8, 8, 8, 8, 8]

def venusMemAlignReadByteDirectGsum10 := venusLookup "Direct_gsum_[10]" 4194304 4194304 6 1
def venusMemAlignReadByteLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 4194304 2 1
def venusMemAlignReadBytePermutationGsum10 := venusLookup "Permutation_gsum_[10]" 4194304 4194304 6 1
def venusMemAlignReadByteRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 4194304 1 1

def venusMemAlignReadByteDeepAli : DeepAliCfg where
  name           := "MemAlignReadByte"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusMemAlignReadByteFRI
  numConstraints := 10
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusMemAlignReadByteDirectGsum10,
                     venusMemAlignReadByteLookupGsum88,
                     venusMemAlignReadBytePermutationGsum10,
                     venusMemAlignReadByteRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlignReadByte: 656 KiB (expected) / 1056 KiB (worst case).
example : venusMemAlignReadByteDeepAli.ExitCriteria venusUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 168, 166, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 168, 166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusMemAlignReadByteDeepAli.ExitCriteria venusMemAlignReadByteJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 168, 166, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 168, 166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## MemAlignWriteByte -/

def venusMemAlignWriteByteFRI := venusFRI Rate.half 4194304 23 229 32 16 [8, 8, 8, 8, 8, 8]

def venusMemAlignWriteByteDirectGsum10 := venusLookup "Direct_gsum_[10]" 4194304 4194304 6 1
def venusMemAlignWriteByteLookupGsum88 := venusLookup "Lookup_gsum_[88]" 0 4194304 2 1
def venusMemAlignWriteBytePermutationGsum10 := venusLookup "Permutation_gsum_[10]" 4194304 4194304 6 2
def venusMemAlignWriteByteRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 4194304 1 1
def venusMemAlignWriteByteRangeCheckGsum107 := venusLookup "Range Check_gsum_[107]" 0 4194304 1 1

def venusMemAlignWriteByteDeepAli : DeepAliCfg where
  name           := "MemAlignWriteByte"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusMemAlignWriteByteFRI
  numConstraints := 15
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusMemAlignWriteByteDirectGsum10,
                     venusMemAlignWriteByteLookupGsum88,
                     venusMemAlignWriteBytePermutationGsum10,
                     venusMemAlignWriteByteRangeCheckGsum103,
                     venusMemAlignWriteByteRangeCheckGsum107]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- MemAlignWriteByte: 683 KiB (expected) / 1082 KiB (worst case).
example : venusMemAlignWriteByteDeepAli.ExitCriteria venusUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 168, 165, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 683) (proofSizeWorstKib := 1082) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusMemAlignWriteByteDeepAli.ExitCriteria venusMemAlignWriteByteJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 168, 165, 169, 169])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 168, 165, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 683) (proofSizeWorstKib := 1082) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Arith -/

def venusArithFRI := venusFRI Rate.half 2097152 64 230 32 16 [8, 8, 8, 8, 8, 4]

def venusArithLookupGsum330 := venusLookup "Lookup_gsum_[330]" 0 2097152 2 23
def venusArithLookupGsum331 := venusLookup "Lookup_gsum_[331]" 0 2097152 4 1
def venusArithLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 2097152 11 1

def venusArithDeepAli : DeepAliCfg where
  name           := "Arith"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusArithFRI
  numConstraints := 65
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusArithLookupGsum330, venusArithLookupGsum331, venusArithLookupGsum5000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Arith: 848 KiB (expected) / 1244 KiB (worst case).
example : venusArithDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 168)
    (lookupBits := [165, 168, 166])
    (rowBits := [166, 172, 175, 178, 181, 184, 187, 111, 185, 168, 165, 168, 166])
    (totalBits := 111)
    (proofSizeExpKib := 848) (proofSizeWorstKib := 1244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusArithDeepAli.ExitCriteria venusArithJBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [165, 168, 166])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 179, 162, 165, 168, 166])
    (totalBits := 128)
    (proofSizeExpKib := 848) (proofSizeWorstKib := 1244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Binary -/

def venusBinaryFRI := venusFRI Rate.half 4194304 49 230 32 16 [8, 8, 8, 8, 8, 8]

def venusBinaryDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 4194304 11 1
def venusBinaryLookupGsum125 := venusLookup "Lookup_gsum_[125]" 0 4194304 7 8
def venusBinaryLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 4194304 0 11 1

def venusBinaryDeepAli : DeepAliCfg where
  name           := "Binary"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusBinaryFRI
  numConstraints := 14
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusBinaryDirectGsum5000, venusBinaryLookupGsum125, venusBinaryLookupGsum5000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Binary: 826 KiB (expected) / 1227 KiB (worst case).
example : venusBinaryDeepAli.ExitCriteria venusUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 164, 166])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 164, 166])
    (totalBits := 111)
    (proofSizeExpKib := 826) (proofSizeWorstKib := 1227) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusBinaryDeepAli.ExitCriteria venusBinaryJBR
    (aliBits := 181) (deepBits := 161)
    (lookupBits := [166, 164, 166])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 181, 161, 166, 164, 166])
    (totalBits := 128)
    (proofSizeExpKib := 826) (proofSizeWorstKib := 1227) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## BinaryAdd -/

def venusBinaryAddFRI := venusFRI Rate.half 4194304 18 229 32 16 [8, 8, 8, 8, 8, 8]

def venusBinaryAddDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 4194304 11 1
def venusBinaryAddLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 4194304 0 11 1
def venusBinaryAddRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 4194304 1 4

def venusBinaryAddDeepAli : DeepAliCfg where
  name           := "BinaryAdd"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusBinaryAddFRI
  numConstraints := 9
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusBinaryAddDirectGsum5000, venusBinaryAddLookupGsum5000, venusBinaryAddRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- BinaryAdd: 656 KiB (expected) / 1056 KiB (worst case).
example : venusBinaryAddDeepAli.ExitCriteria venusUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 166, 167])
    (rowBits := [166, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 166, 167])
    (totalBits := 111)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusBinaryAddDeepAli.ExitCriteria venusBinaryAddJBR
    (aliBits := 181) (deepBits := 160)
    (lookupBits := [166, 166, 167])
    (rowBits := [133, 137, 140, 143, 146, 149, 152, 128, 181, 160, 166, 166, 167])
    (totalBits := 128)
    (proofSizeExpKib := 656) (proofSizeWorstKib := 1056) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## BinaryExtension -/

def venusBinaryExtensionFRI := venusFRI Rate.half 4194304 40 230 32 16 [8, 8, 8, 8, 8, 8]

def venusBinaryExtensionDirectGsum5000 := venusLookup "Direct_gsum_[5000]" 0 4194304 11 1
def venusBinaryExtensionLookupGsum124 := venusLookup "Lookup_gsum_[124]" 0 4194304 7 8
def venusBinaryExtensionLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 4194304 0 11 1
def venusBinaryExtensionRangeCheckGsum102 := venusLookup "Range Check_gsum_[102]" 0 4194304 1 1

def venusBinaryExtensionDeepAli : DeepAliCfg where
  name           := "BinaryExtension"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusBinaryExtensionFRI
  numConstraints := 8
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusBinaryExtensionDirectGsum5000,
                     venusBinaryExtensionLookupGsum124,
                     venusBinaryExtensionLookupGsum5000,
                     venusBinaryExtensionRangeCheckGsum102]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- BinaryExtension: 777 KiB (expected) / 1179 KiB (worst case).
example : venusBinaryExtensionDeepAli.ExitCriteria venusUDR
    (aliBits := 188) (deepBits := 167)
    (lookupBits := [166, 164, 166, 169])
    (rowBits := [165, 171, 174, 177, 180, 183, 186, 111, 188, 167, 166, 164, 166, 169])
    (totalBits := 111)
    (proofSizeExpKib := 777) (proofSizeWorstKib := 1179) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusBinaryExtensionDeepAli.ExitCriteria venusBinaryExtensionJBR
    (aliBits := 182) (deepBits := 161)
    (lookupBits := [166, 164, 166, 169])
    (rowBits := [133, 138, 141, 144, 147, 150, 153, 128, 182, 161, 166, 164, 166, 169])
    (totalBits := 128)
    (proofSizeExpKib := 777) (proofSizeWorstKib := 1179) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Add256 -/

def venusAdd256FRI := venusFRI Rate.half 1048576 69 229 64 16 [8, 8, 8, 8, 8]

def venusAdd256LookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 1048576 0 11 1
def venusAdd256PermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 1048576 6 16
def venusAdd256RangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 1048576 1 16

def venusAdd256DeepAli : DeepAliCfg where
  name           := "Add256"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusAdd256FRI
  numConstraints := 36
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusAdd256LookupGsum5000, venusAdd256PermutationGsum10, venusAdd256RangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Add256: 816 KiB (expected) / 1165 KiB (worst case).
example : venusAdd256DeepAli.ExitCriteria venusUDR
    (aliBits := 186) (deepBits := 169)
    (lookupBits := [168, 165, 167])
    (rowBits := [166, 173, 176, 179, 182, 185, 111, 186, 169, 168, 165, 167])
    (totalBits := 111)
    (proofSizeExpKib := 816) (proofSizeWorstKib := 1165) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusAdd256DeepAli.ExitCriteria venusAdd256JBR
    (aliBits := 179) (deepBits := 162)
    (lookupBits := [168, 165, 167])
    (rowBits := [133, 139, 142, 145, 148, 151, 128, 179, 162, 168, 165, 167])
    (totalBits := 128)
    (proofSizeExpKib := 816) (proofSizeWorstKib := 1165) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq -/

def venusArithEqFRI := venusFRI Rate.half 1048576 470 231 64 16 [8, 8, 8, 8, 8]

def venusArithEqLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 1048576 0 11 1
def venusArithEqLookupGsum5002 := venusLookup "Lookup_gsum_[5002]" 0 1048576 2 2
def venusArithEqPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 1048576 6 2
def venusArithEqRangeCheckGsum103_104 := venusLookup "Range Check_gsum_[103, 104]" 0 1048576 1 3
def venusArithEqRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 1048576 1 7
def venusArithEqRangeCheckGsum108 := venusLookup "Range Check_gsum_[108]" 0 1048576 1 6

def venusArithEqDeepAli : DeepAliCfg where
  name           := "ArithEq"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusArithEqFRI
  numConstraints := 103
  airMaxDegree   := 3
  maxCombo       := 36
  grindDeep      := 0
  lookups        := [venusArithEqLookupGsum5000,
                     venusArithEqLookupGsum5002,
                     venusArithEqPermutationGsum10,
                     venusArithEqRangeCheckGsum103_104,
                     venusArithEqRangeCheckGsum103,
                     venusArithEqRangeCheckGsum108]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq: 2994 KiB (expected) / 3346 KiB (worst case).
example : venusArithEqDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 169)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [164, 173, 176, 179, 182, 185, 111, 185, 169, 168, 169, 168, 170, 169,
                169])
    (totalBits := 111)
    (proofSizeExpKib := 2994) (proofSizeWorstKib := 3346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusArithEqDeepAli.ExitCriteria venusArithEqJBR
    (aliBits := 178) (deepBits := 163)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [133, 142, 145, 148, 151, 154, 128, 178, 163, 168, 169, 168, 170, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 2994) (proofSizeWorstKib := 3346) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq384 -/

def venusArithEq384FRI := venusFRI Rate.half 1048576 536 232 64 16 [8, 8, 8, 8, 8]

def venusArithEq384LookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 1048576 0 11 1
def venusArithEq384LookupGsum5002 := venusLookup "Lookup_gsum_[5002]" 0 1048576 2 2
def venusArithEq384PermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 1048576 6 2
def venusArithEq384RangeCheckGsum103_104 := venusLookup "Range Check_gsum_[103, 104]" 0 1048576 1 3
def venusArithEq384RangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 1048576 1 7
def venusArithEq384RangeCheckGsum108 := venusLookup "Range Check_gsum_[108]" 0 1048576 1 6

def venusArithEq384DeepAli : DeepAliCfg where
  name           := "ArithEq384"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusArithEq384FRI
  numConstraints := 76
  airMaxDegree   := 3
  maxCombo       := 54
  grindDeep      := 0
  lookups        := [venusArithEq384LookupGsum5000,
                     venusArithEq384LookupGsum5002,
                     venusArithEq384PermutationGsum10,
                     venusArithEq384RangeCheckGsum103_104,
                     venusArithEq384RangeCheckGsum103,
                     venusArithEq384RangeCheckGsum108]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq384: 3366 KiB (expected) / 3720 KiB (worst case).
example : venusArithEq384DeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 169)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [163, 173, 176, 179, 182, 185, 112, 185, 169, 168, 169, 168, 170, 169,
                169])
    (totalBits := 112)
    (proofSizeExpKib := 3366) (proofSizeWorstKib := 3720) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusArithEq384DeepAli.ExitCriteria venusArithEq384JBR
    (aliBits := 179) (deepBits := 163)
    (lookupBits := [168, 169, 168, 170, 169, 169])
    (rowBits := [133, 142, 145, 148, 151, 154, 128, 179, 163, 168, 169, 168, 170, 169,
                169])
    (totalBits := 128)
    (proofSizeExpKib := 3366) (proofSizeWorstKib := 3720) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Keccakf -/

def venusKeccakfFRI := venusFRI Rate.half 131072 4065 217 64 23 [8, 8, 8, 8]

def venusKeccakfLookupGsum126 := venusLookup "Lookup_gsum_[126]" 0 131072 4 534
def venusKeccakfLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 131072 0 11 1
def venusKeccakfPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 131072 6 25

def venusKeccakfDeepAli : DeepAliCfg where
  name           := "Keccakf"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusKeccakfFRI
  numConstraints := 2432
  airMaxDegree   := 3
  maxCombo       := 26
  grindDeep      := 0
  lookups        := [venusKeccakfLookupGsum126, venusKeccakfLookupGsum5000, venusKeccakfPermutationGsum10]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Keccakf: 20975 KiB (expected) / 21244 KiB (worst case).
example : venusKeccakfDeepAli.ExitCriteria venusUDR
    (aliBits := 180) (deepBits := 172)
    (lookupBits := [163, 171, 167])
    (rowBits := [164, 176, 179, 182, 185, 113, 180, 172, 163, 171, 167])
    (totalBits := 113)
    (proofSizeExpKib := 20975) (proofSizeWorstKib := 21244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusKeccakfDeepAli.ExitCriteria venusKeccakfJBR
    (aliBits := 174) (deepBits := 166)
    (lookupBits := [163, 171, 167])
    (rowBits := [132, 145, 148, 151, 154, 128, 174, 166, 163, 171, 167])
    (totalBits := 128)
    (proofSizeExpKib := 20975) (proofSizeWorstKib := 21244) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Sha256f -/

def venusSha256fFRI := venusFRI Rate.half 262144 1265 231 32 16 [8, 8, 8, 8, 4]

def venusSha256fLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 262144 0 11 1
def venusSha256fPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 262144 6 1
def venusSha256fRangeCheckGsum109 := venusLookup "Range Check_gsum_[109]" 0 262144 1 2

def venusSha256fDeepAli : DeepAliCfg where
  name           := "Sha256f"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusSha256fFRI
  numConstraints := 115
  airMaxDegree   := 3
  maxCombo       := 87
  grindDeep      := 0
  lookups        := [venusSha256fLookupGsum5000, venusSha256fPermutationGsum10, venusSha256fRangeCheckGsum109]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Sha256f: 7215 KiB (expected) / 7549 KiB (worst case).
example : venusSha256fDeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 171)
    (lookupBits := [170, 171, 172])
    (rowBits := [164, 175, 178, 181, 184, 187, 111, 185, 171, 170, 171, 172])
    (totalBits := 111)
    (proofSizeExpKib := 7215) (proofSizeWorstKib := 7549) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusSha256fDeepAli.ExitCriteria venusSha256fJBR
    (aliBits := 178) (deepBits := 165)
    (lookupBits := [170, 171, 172])
    (rowBits := [132, 143, 146, 149, 152, 155, 128, 178, 165, 170, 171, 172])
    (totalBits := 128)
    (proofSizeExpKib := 7215) (proofSizeWorstKib := 7549) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Poseidon2 -/

def venusPoseidon2FRI := venusFRI Rate.quarter 131072 182 114 32 16 [8, 8, 8, 8, 4]

def venusPoseidon2LookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 131072 0 11 1
def venusPoseidon2PermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 131072 6 4

def venusPoseidon2DeepAli : DeepAliCfg where
  name           := "Poseidon2"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusPoseidon2FRI
  numConstraints := 85
  airMaxDegree   := 4
  maxCombo       := 17
  grindDeep      := 0
  lookups        := [venusPoseidon2LookupGsum5000, venusPoseidon2PermutationGsum10]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Poseidon2: 682 KiB (expected) / 832 KiB (worst case).
example : venusPoseidon2DeepAli.ExitCriteria venusUDR
    (aliBits := 185) (deepBits := 172)
    (lookupBits := [171, 170])
    (rowBits := [166, 174, 177, 180, 183, 186, 93, 185, 172, 171, 170])
    (totalBits := 93)
    (proofSizeExpKib := 682) (proofSizeWorstKib := 832) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusPoseidon2DeepAli.ExitCriteria venusPoseidon2JBR
    (aliBits := 177) (deepBits := 164)
    (lookupBits := [171, 170])
    (rowBits := [133, 140, 143, 146, 149, 153, 128, 177, 164, 171, 170])
    (totalBits := 128)
    (proofSizeExpKib := 682) (proofSizeWorstKib := 832) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Blake2br -/

def venusBlake2brFRI := venusFRI Rate.half 262144 651 230 32 16 [8, 8, 8, 8, 4]

def venusBlake2brLookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 262144 0 11 1
def venusBlake2brPermutationGsum10 := venusLookup "Permutation_gsum_[10]" 0 262144 6 4
def venusBlake2brPermutationGsum127 := venusLookup "Permutation_gsum_[127]" 262144 262144 3 1
def venusBlake2brRangeCheckGsum103 := venusLookup "Range Check_gsum_[103]" 0 262144 1 12

def venusBlake2brDeepAli : DeepAliCfg where
  name           := "Blake2br"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusBlake2brFRI
  numConstraints := 189
  airMaxDegree   := 3
  maxCombo       := 29
  grindDeep      := 0
  lookups        := [venusBlake2brLookupGsum5000, venusBlake2brPermutationGsum10, venusBlake2brPermutationGsum127, venusBlake2brRangeCheckGsum103]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Blake2br: 3874 KiB (expected) / 4207 KiB (worst case).
example : venusBlake2brDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [170, 169, 171, 170])
    (rowBits := [165, 175, 178, 181, 184, 187, 111, 184, 171, 170, 169, 171, 170])
    (totalBits := 111)
    (proofSizeExpKib := 3874) (proofSizeWorstKib := 4207) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusBlake2brDeepAli.ExitCriteria venusBlake2brJBR
    (aliBits := 177) (deepBits := 165)
    (lookupBits := [170, 169, 171, 170])
    (rowBits := [133, 142, 145, 148, 151, 155, 128, 177, 165, 170, 169, 171, 170])
    (totalBits := 128)
    (proofSizeExpKib := 3874) (proofSizeWorstKib := 4207) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## SpecifiedRanges -/

def venusSpecifiedRangesFRI := venusFRI Rate.half 1048576 107 229 64 16 [8, 8, 8, 8, 8]

def venusSpecifiedRangesLookupGsum102 := venusLookup "Lookup_gsum_[102]" 1048576 0 1 1
def venusSpecifiedRangesLookupGsum103_104 := venusLookup "Lookup_gsum_[103, 104]" 1048576 0 1 1
def venusSpecifiedRangesLookupGsum104_105_106_107_108 := venusLookup "Lookup_gsum_[104, 105, 106, 107, 108]" 1048576 0 1 1
def venusSpecifiedRangesLookupGsum104 := venusLookup "Lookup_gsum_[104]" 1048576 0 1 1
def venusSpecifiedRangesLookupGsum108_109 := venusLookup "Lookup_gsum_[108, 109]" 1048576 0 1 1
def venusSpecifiedRangesLookupGsum108 := venusLookup "Lookup_gsum_[108]" 1048576 0 1 1

def venusSpecifiedRangesDeepAli : DeepAliCfg where
  name           := "SpecifiedRanges"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusSpecifiedRangesFRI
  numConstraints := 16
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusSpecifiedRangesLookupGsum102,
                     venusSpecifiedRangesLookupGsum103_104,
                     venusSpecifiedRangesLookupGsum104_105_106_107_108,
                     venusSpecifiedRangesLookupGsum104,
                     venusSpecifiedRangesLookupGsum108_109,
                     venusSpecifiedRangesLookupGsum108]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- SpecifiedRanges: 1020 KiB (expected) / 1369 KiB (worst case).
example : venusSpecifiedRangesDeepAli.ExitCriteria venusUDR
    (aliBits := 187) (deepBits := 169)
    (lookupBits := [171, 171, 171, 171, 171, 171])
    (rowBits := [166, 173, 176, 179, 182, 185, 111, 187, 169, 171, 171, 171, 171, 171,
                171])
    (totalBits := 111)
    (proofSizeExpKib := 1020) (proofSizeWorstKib := 1369) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusSpecifiedRangesDeepAli.ExitCriteria venusSpecifiedRangesJBR
    (aliBits := 180) (deepBits := 162)
    (lookupBits := [171, 171, 171, 171, 171, 171])
    (rowBits := [132, 139, 142, 145, 148, 151, 128, 180, 162, 171, 171, 171, 171, 171,
                171])
    (totalBits := 128)
    (proofSizeExpKib := 1020) (proofSizeWorstKib := 1369) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## VirtualTable0 -/

def venusVirtualTable0FRI := venusFRI Rate.half 2097152 69 230 32 16 [8, 8, 8, 8, 8, 4]

def venusVirtualTable0LookupGsum124_8001 := venusLookup "Lookup_gsum_[124, 8001]" 2097152 0 7 1
def venusVirtualTable0LookupGsum125_124 := venusLookup "Lookup_gsum_[125, 124]" 2097152 0 7 1
def venusVirtualTable0LookupGsum125 := venusLookup "Lookup_gsum_[125]" 2097152 0 7 1
def venusVirtualTable0LookupGsum126_331_8002_133_125 := venusLookup "Lookup_gsum_[126, 331, 8002, 133, 125]" 2097152 0 7 1
def venusVirtualTable0LookupGsum330 := venusLookup "Lookup_gsum_[330]" 2097152 0 2 1
def venusVirtualTable0LookupGsum5002_88_77_8003_126 := venusLookup "Lookup_gsum_[5002, 88, 77, 8003, 126]" 2097152 0 4 1

def venusVirtualTable0DeepAli : DeepAliCfg where
  name           := "VirtualTable0"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusVirtualTable0FRI
  numConstraints := 6
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusVirtualTable0LookupGsum124_8001,
                     venusVirtualTable0LookupGsum125_124,
                     venusVirtualTable0LookupGsum125,
                     venusVirtualTable0LookupGsum126_331_8002_133_125,
                     venusVirtualTable0LookupGsum330,
                     venusVirtualTable0LookupGsum5002_88_77_8003_126]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- VirtualTable0: 875 KiB (expected) / 1270 KiB (worst case).
example : venusVirtualTable0DeepAli.ExitCriteria venusUDR
    (aliBits := 189) (deepBits := 168)
    (lookupBits := [168, 168, 168, 168, 169, 168])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 189, 168, 168, 168, 168, 168,
                169, 168])
    (totalBits := 111)
    (proofSizeExpKib := 875) (proofSizeWorstKib := 1270) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusVirtualTable0DeepAli.ExitCriteria venusVirtualTable0JBR
    (aliBits := 182) (deepBits := 162)
    (lookupBits := [168, 168, 168, 168, 169, 168])
    (rowBits := [133, 139, 142, 145, 148, 151, 154, 128, 182, 162, 168, 168, 168, 168,
                169, 168])
    (totalBits := 128)
    (proofSizeExpKib := 875) (proofSizeWorstKib := 1270) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## VirtualTable1 -/

def venusVirtualTable1FRI := venusFRI Rate.half 2097152 90 230 32 16 [8, 8, 8, 8, 8, 4]

def venusVirtualTable1LookupGsum5000 := venusLookup "Lookup_gsum_[5000]" 2097152 0 8 1

def venusVirtualTable1DeepAli : DeepAliCfg where
  name           := "VirtualTable1"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusVirtualTable1FRI
  numConstraints := 6
  airMaxDegree   := 3
  maxCombo       := 3
  grindDeep      := 0
  lookups        := [venusVirtualTable1LookupGsum5000]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- VirtualTable1: 989 KiB (expected) / 1384 KiB (worst case).
example : venusVirtualTable1DeepAli.ExitCriteria venusUDR
    (aliBits := 189) (deepBits := 168)
    (lookupBits := [167])
    (rowBits := [165, 172, 175, 178, 181, 184, 187, 111, 189, 168, 167])
    (totalBits := 111)
    (proofSizeExpKib := 989) (proofSizeWorstKib := 1384) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusVirtualTable1DeepAli.ExitCriteria venusVirtualTable1JBR
    (aliBits := 182) (deepBits := 162)
    (lookupBits := [167])
    (rowBits := [133, 139, 142, 145, 148, 151, 155, 128, 182, 162, 167])
    (totalBits := 128)
    (proofSizeExpKib := 989) (proofSizeWorstKib := 1384) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## DmaPrePost-compressor -/

def venusDmaPrePostCompressorFRI := venusFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def venusDmaPrePostCompressorConnectionGprod1 := venusLookup "Connection_gprod_[1]" 262144 262144 2 36

def venusDmaPrePostCompressorDeepAli : DeepAliCfg where
  name           := "DmaPrePost-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusDmaPrePostCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [venusDmaPrePostCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- DmaPrePost-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : venusDmaPrePostCompressorDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusDmaPrePostCompressorDeepAli.ExitCriteria venusDmaPrePostCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq-compressor -/

def venusArithEqCompressorFRI := venusFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def venusArithEqCompressorConnectionGprod1 := venusLookup "Connection_gprod_[1]" 262144 262144 2 36

def venusArithEqCompressorDeepAli : DeepAliCfg where
  name           := "ArithEq-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusArithEqCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [venusArithEqCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : venusArithEqCompressorDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusArithEqCompressorDeepAli.ExitCriteria venusArithEqCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## ArithEq384-compressor -/

def venusArithEq384CompressorFRI := venusFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def venusArithEq384CompressorConnectionGprod1 := venusLookup "Connection_gprod_[1]" 262144 262144 2 36

def venusArithEq384CompressorDeepAli : DeepAliCfg where
  name           := "ArithEq384-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusArithEq384CompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [venusArithEq384CompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- ArithEq384-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : venusArithEq384CompressorDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusArithEq384CompressorDeepAli.ExitCriteria venusArithEq384CompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Keccakf-compressor -/

def venusKeccakfCompressorFRI := venusFRI Rate.quarter 1048576 198 110 32 20 [8, 8, 8, 8, 8, 4]

def venusKeccakfCompressorConnectionGprod1 := venusLookup "Connection_gprod_[1]" 1048576 1048576 2 36

def venusKeccakfCompressorDeepAli : DeepAliCfg where
  name           := "Keccakf-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusKeccakfCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [venusKeccakfCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Keccakf-compressor: 771 KiB (expected) / 940 KiB (worst case).
example : venusKeccakfCompressorDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 169)
    (lookupBits := [164])
    (rowBits := [163, 171, 174, 177, 180, 183, 186, 94, 184, 169, 164])
    (totalBits := 94)
    (proofSizeExpKib := 771) (proofSizeWorstKib := 940) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusKeccakfCompressorDeepAli.ExitCriteria venusKeccakfCompressorJBR
    (aliBits := 177) (deepBits := 162)
    (lookupBits := [164])
    (rowBits := [133, 141, 144, 147, 150, 153, 156, 128, 177, 162, 164])
    (totalBits := 128)
    (proofSizeExpKib := 771) (proofSizeWorstKib := 940) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Sha256f-compressor -/

def venusSha256fCompressorFRI := venusFRI Rate.quarter 524288 198 110 64 20 [8, 8, 8, 8, 8]

def venusSha256fCompressorConnectionGprod1 := venusLookup "Connection_gprod_[1]" 524288 524288 2 36

def venusSha256fCompressorDeepAli : DeepAliCfg where
  name           := "Sha256f-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusSha256fCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [venusSha256fCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Sha256f-compressor: 743 KiB (expected) / 892 KiB (worst case).
example : venusSha256fCompressorDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 170)
    (lookupBits := [165])
    (rowBits := [164, 172, 175, 178, 181, 184, 94, 184, 170, 165])
    (totalBits := 94)
    (proofSizeExpKib := 743) (proofSizeWorstKib := 892) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusSha256fCompressorDeepAli.ExitCriteria venusSha256fCompressorJBR
    (aliBits := 176) (deepBits := 162)
    (lookupBits := [165])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 162, 165])
    (totalBits := 128)
    (proofSizeExpKib := 743) (proofSizeWorstKib := 892) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Blake2br-compressor -/

def venusBlake2brCompressorFRI := venusFRI Rate.quarter 262144 198 110 32 20 [8, 8, 8, 8, 8]

def venusBlake2brCompressorConnectionGprod1 := venusLookup "Connection_gprod_[1]" 262144 262144 2 36

def venusBlake2brCompressorDeepAli : DeepAliCfg where
  name           := "Blake2br-compressor"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusBlake2brCompressorFRI
  numConstraints := 179
  airMaxDegree   := 5
  maxCombo       := 6
  grindDeep      := 0
  lookups        := [venusBlake2brCompressorConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Blake2br-compressor: 726 KiB (expected) / 871 KiB (worst case).
example : venusBlake2brCompressorDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [166])
    (rowBits := [165, 173, 176, 179, 182, 185, 94, 184, 171, 166])
    (totalBits := 94)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusBlake2brCompressorDeepAli.ExitCriteria venusBlake2brCompressorJBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [166])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 166])
    (totalBits := 128)
    (proofSizeExpKib := 726) (proofSizeWorstKib := 871) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Recursive2 -/

def venusRecursive2FRI := venusFRI Rate.eighth 131072 145 73 32 20 [8, 8, 8, 8, 8]

def venusRecursive2ConnectionGprod1 := venusLookup "Connection_gprod_[1]" 131072 131072 2 27

def venusRecursive2DeepAli : DeepAliCfg where
  name           := "Recursive2"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusRecursive2FRI
  numConstraints := 158
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [venusRecursive2ConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Recursive2: 398 KiB (expected) / 487 KiB (worst case).
example : venusRecursive2DeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 171)
    (lookupBits := [168])
    (rowBits := [166, 173, 176, 179, 182, 185, 80, 184, 171, 168])
    (totalBits := 80)
    (proofSizeExpKib := 398) (proofSizeWorstKib := 487) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusRecursive2DeepAli.ExitCriteria venusRecursive2JBR
    (aliBits := 176) (deepBits := 163)
    (lookupBits := [168])
    (rowBits := [133, 140, 143, 146, 149, 152, 128, 176, 163, 168])
    (totalBits := 128)
    (proofSizeExpKib := 398) (proofSizeWorstKib := 487) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Final -/

def venusFinalFRI := venusFRI Rate.thirtysecond 65536 139 43 32 22 [16, 16, 16, 16]

def venusFinalConnectionGprod1 := venusLookup "Connection_gprod_[1]" 65536 65536 2 24

def venusFinalDeepAli : DeepAliCfg where
  name           := "Final"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusFinalFRI
  numConstraints := 154
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [venusFinalConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Final: 253 KiB (expected) / 292 KiB (worst case).
example : venusFinalDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 172)
    (lookupBits := [169])
    (rowBits := [164, 172, 176, 180, 184, 63, 184, 172, 169])
    (totalBits := 63)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusFinalDeepAli.ExitCriteria venusFinalJBR
    (aliBits := 175) (deepBits := 163)
    (lookupBits := [169])
    (rowBits := [133, 140, 144, 148, 152, 128, 175, 163, 169])
    (totalBits := 128)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 292) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ## Final_Compressed -/

def venusFinalCompressedFRI := venusFRI Rate.sixteenth 32768 145 54 1024 22 [8, 8, 8]

def venusFinalCompressedConnectionGprod1 := venusLookup "Connection_gprod_[1]" 32768 32768 2 27

def venusFinalCompressedDeepAli : DeepAliCfg where
  name           := "Final_Compressed"
  proofSystName  := "DEEP-ALI"
  field          := goldilocks3
  densePCS       := .fri venusFinalCompressedFRI
  numConstraints := 158
  airMaxDegree   := 8
  maxCombo       := 4
  grindDeep      := 0
  lookups        := [venusFinalCompressedConnectionGprod1]
  h_lookups_field := by native_decide
  isUDR          := true
  isJBR          := true

-- Final_Compressed: 269 KiB (expected) / 313 KiB (worst case).
example : venusFinalCompressedDeepAli.ExitCriteria venusUDR
    (aliBits := 184) (deepBits := 173)
    (lookupBits := [170])
    (rowBits := [166, 174, 177, 180, 71, 184, 173, 170])
    (totalBits := 71)
    (proofSizeExpKib := 269) (proofSizeWorstKib := 313) := by
  unfold DeepAliCfg.ExitCriteria; native_decide
example : venusFinalCompressedDeepAli.ExitCriteria venusFinalCompressedJBR
    (aliBits := 175) (deepBits := 164)
    (lookupBits := [170])
    (rowBits := [134, 141, 144, 147, 128, 175, 164, 170])
    (totalBits := 128)
    (proofSizeExpKib := 269) (proofSizeWorstKib := 313) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

end Soundcalc
