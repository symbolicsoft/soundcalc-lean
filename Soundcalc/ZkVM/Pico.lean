import Soundcalc.Circuit.DeepAli
import Soundcalc.PCS.FRI
import Soundcalc.Lookup
import Soundcalc.Field.KoalaBear

/-!
# Pico soundness configuration

Pico is a DEEP-ALI zkVM, so it only needs `Soundcalc.Circuit.DeepAli`. Parameters
below are generated from `soundcalc/zkvms/pico/pico.toml` (mirrored at
<https://github.com/ethereum/soundcalc/blob/main/reports/pico.md>).

## Circuits

RISCV → CONVERT → COMBINE → COMPRESS → EMBED, a 5-stage recursion pipeline:

* **riscv**: `ρ = 1/2`, `H = 2^22`, 22 FRI rounds, 7 lookups (base STARK proof).
* **convert**: `ρ = 1/2`, `H = 2^20`, 20 FRI rounds, 1 lookup (1-to-1 recursion).
* **combine**: `ρ = 1/2`, `H = 2^18`, 18 FRI rounds, 1 lookup (2-to-1 recursion).
* **compress**: `ρ = 1/16`, `H = 2^17`, 17 FRI rounds, 1 lookup (tighter FRI, smaller proof).
* **embed**: `ρ = 1/16`, `H = 2^15`, 15 FRI rounds, 1 lookup (BN254-embedding layer).

## Two-regime strategy

* **UDR** (`picoUDR`): classical unique-decoding threshold, shared by all circuits.
* **JBR**: Johnson Bound Regime. The gap `η = max(ρ/20, √ρ/100)` (BCHKS25's default
  gap, `soundcalc/proxgaps/johnson_bound.py`) depends on `ρ`, so it differs per
  rate: `η = 1/40` for riscv/convert/combine (`ρ = 1/2`), `η = 1/320` for
  compress/embed (`ρ = 1/16`). `g = 2^40` is the same `√ρ`-enclosure granularity
  used by Airbender/OpenVM.
-/

namespace Soundcalc

/-! ## Configuration literals (generated from `pico.toml`) -/

def picoRiscvFRI : FRIConfig where
  hashBits       := 248
  field          := koalaBear4
  ρ              := Rate.half
  denseLen       := 2 ^ 22          -- trace length = FRI dimension
  batchSize      := 1435
  powerBatch     := true            -- Pico uses power batching
  multilinBatch  := false
  numQueries     := 84
  foldingFactors := List.replicate 22 2
  earlyStopDeg   := 2
  grindQuery     := 16
  grindBatch     := 0                -- pico.toml has no grinding_batching_phase
  grindCommit    := 0                -- pico.toml has no grinding_commit_phase

def picoConvertFRI : FRIConfig where
  hashBits       := 248
  field          := koalaBear4
  ρ              := Rate.half
  denseLen       := 2 ^ 20
  batchSize      := 485
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 84
  foldingFactors := List.replicate 20 2
  earlyStopDeg   := 2
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def picoCombineFRI : FRIConfig where
  hashBits       := 248
  field          := koalaBear4
  ρ              := Rate.half
  denseLen       := 2 ^ 18
  batchSize      := 485
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 84
  foldingFactors := List.replicate 18 2
  earlyStopDeg   := 2
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def picoCompressFRI : FRIConfig where
  hashBits       := 248
  field          := koalaBear4
  ρ              := Rate.sixteenth
  denseLen       := 2 ^ 17
  batchSize      := 485
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 21
  foldingFactors := List.replicate 17 2
  earlyStopDeg   := 16
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

def picoEmbedFRI : FRIConfig where
  hashBits       := 248
  field          := koalaBear4
  ρ              := Rate.sixteenth
  denseLen       := 2 ^ 15
  batchSize      := 485
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 21
  foldingFactors := List.replicate 15 2
  earlyStopDeg   := 16
  grindQuery     := 16
  grindBatch     := 0
  grindCommit    := 0

/-! ## Lookup configurations (univariate logup, regime-independent) -/

def picoRiscvAlu : LookupCfg where
  name := "alu"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 33554432; rowsL := 58720256; numColumnsS := 14; numLookupsM := 1
  grindBitsLookup := 0

def picoRiscvByte : LookupCfg where
  name := "byte"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 589824; rowsL := 352321536; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0

def picoRiscvGlobalType : LookupCfg where
  name := "global_type"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 8388608; rowsL := 9437184; numColumnsS := 11; numLookupsM := 1
  grindBitsLookup := 0

def picoRiscvMemory : LookupCfg where
  name := "memory"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 25165824; rowsL := 25165824; numColumnsS := 23; numLookupsM := 1
  grindBitsLookup := 0

def picoRiscvPoseidon2 : LookupCfg where
  name := "poseidon2"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 8388608; rowsL := 8388608; numColumnsS := 33; numLookupsM := 1
  grindBitsLookup := 0

def picoRiscvProgram : LookupCfg where
  name := "program"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 4194304; rowsL := 4194304; numColumnsS := 39; numLookupsM := 1
  grindBitsLookup := 0

def picoRiscvSyscall : LookupCfg where
  name := "syscall"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 1048576; rowsL := 4194304; numColumnsS := 5; numLookupsM := 1
  grindBitsLookup := 0

def picoConvertMemory : LookupCfg where
  name := "memory"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 11534336; rowsL := 17825808; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0

def picoCombineMemory : LookupCfg where
  name := "memory"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 3407872; rowsL := 7733264; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0

def picoCompressMemory : LookupCfg where
  name := "memory"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 1703936; rowsL := 4063248; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0

def picoEmbedMemory : LookupCfg where
  name := "memory"; field := koalaBear4; isLogUpMultivar := false
  rowsT := 491520; rowsL := 1048592; numColumnsS := 6; numLookupsM := 1
  grindBitsLookup := 0

/-- The two regimes for Pico. `η` is derived from `(koalaBear4, ρ, g)` by `JBR`
    itself (BCHKS25's default gap, `= 1/40` for `ρ = 1/2`, `= 1/320` for `ρ = 1/16`);
    `g = 2^40` is the A1 granularity. A single `JBR koalaBear4 (2^40)` value is
    correct for every circuit regardless of its `ρ` — kept as separate per-circuit
    abbrevs below purely for readability at call sites. -/
abbrev picoUDR : Regime := UDR koalaBear4
abbrev picoRiscvJBR : Regime := JBR koalaBear4 (2^40)
abbrev picoConvertJBR : Regime := JBR koalaBear4 (2^40)
abbrev picoCombineJBR : Regime := JBR koalaBear4 (2^40)
abbrev picoCompressJBR : Regime := JBR koalaBear4 (2^40)
abbrev picoEmbedJBR : Regime := JBR koalaBear4 (2^40)

/-! ## DEEP-ALI configurations (tied to FRI by construction) -/

def picoRiscvDeepAli : DeepAliCfg where
  name           := "riscv"
  proofSystName  := "DEEP-ALI"
  field          := picoRiscvFRI.field
  densePCS       := .fri picoRiscvFRI
  numConstraints := 4729
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 0
  lookups        := [picoRiscvAlu, picoRiscvByte, picoRiscvGlobalType, picoRiscvMemory,
                     picoRiscvPoseidon2, picoRiscvProgram, picoRiscvSyscall]
  isUDR          := true
  isJBR          := true

def picoConvertDeepAli : DeepAliCfg where
  name           := "convert"
  proofSystName  := "DEEP-ALI"
  field          := picoConvertFRI.field
  densePCS       := .fri picoConvertFRI
  numConstraints := 323
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 0
  lookups        := [picoConvertMemory]
  isUDR          := true
  isJBR          := true

def picoCombineDeepAli : DeepAliCfg where
  name           := "combine"
  proofSystName  := "DEEP-ALI"
  field          := picoCombineFRI.field
  densePCS       := .fri picoCombineFRI
  numConstraints := 323
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 0
  lookups        := [picoCombineMemory]
  isUDR          := true
  isJBR          := true

def picoCompressDeepAli : DeepAliCfg where
  name           := "compress"
  proofSystName  := "DEEP-ALI"
  field          := picoCompressFRI.field
  densePCS       := .fri picoCompressFRI
  numConstraints := 323
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 0
  lookups        := [picoCompressMemory]
  isUDR          := true
  isJBR          := true

def picoEmbedDeepAli : DeepAliCfg where
  name           := "embed"
  proofSystName  := "DEEP-ALI"
  field          := picoEmbedFRI.field
  densePCS       := .fri picoEmbedFRI
  numConstraints := 323
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 0
  lookups        := [picoEmbedMemory]
  isUDR          := true
  isJBR          := true

/-
# Exit criteria (bundled)

Row entries: batching | commit×rounds | query | ALI | DEEP | lookups.
Lookup cells and proof sizes are regime-independent, hence identical across the
UDR/JBR calls for a given circuit.
Cross-checked against <https://github.com/ethereum/soundcalc/blob/main/reports/pico.md>. -/

-- riscv: 2225 KiB (expected) / 2583 KiB (worst case).
example : picoRiscvDeepAli.ExitCriteria picoUDR
    (aliBits := 111) (deepBits := 99)
    (lookupBits := [93, 92, 96, 93, 94, 95, 99])
    (rowBits := [92, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
                  116, 117, 118, 119, 120, 121, 122, 122, 123, 50, 111, 99,
                  93, 92, 96, 93, 94, 95, 99])
    (totalBits := 50)
    (proofSizeExpKib := 2225) (proofSizeWorstKib := 2583) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

example : picoRiscvDeepAli.ExitCriteria picoRiscvJBR
    (aliBits := 106) (deepBits := 95)
    (lookupBits := [93, 92, 96, 93, 94, 95, 99])
    (rowBits := [69, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
                  94, 95, 96, 97, 98, 99, 100, 101, 102, 53, 106, 95,
                  93, 92, 96, 93, 94, 95, 99])
    (totalBits := 53)
    (proofSizeExpKib := 2225) (proofSizeWorstKib := 2583) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

-- convert: 934 KiB (expected) / 1255 KiB (worst case).
example : picoConvertDeepAli.ExitCriteria picoUDR
    (aliBits := 115) (deepBits := 101)
    (lookupBits := [96])
    (rowBits := [96, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
                  118, 119, 120, 121, 122, 122, 123, 50, 115, 101, 96])
    (totalBits := 50)
    (proofSizeExpKib := 934) (proofSizeWorstKib := 1255) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

example : picoConvertDeepAli.ExitCriteria picoConvertJBR
    (aliBits := 110) (deepBits := 97)
    (lookupBits := [96])
    (rowBits := [73, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
                  96, 97, 98, 99, 100, 101, 102, 53, 110, 97, 96])
    (totalBits := 53)
    (proofSizeExpKib := 934) (proofSizeWorstKib := 1255) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

-- combine: 861 KiB (expected) / 1146 KiB (worst case).
example : picoCombineDeepAli.ExitCriteria picoUDR
    (aliBits := 115) (deepBits := 103)
    (lookupBits := [97])
    (rowBits := [98, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
                  120, 121, 122, 122, 123, 50, 115, 103, 97])
    (totalBits := 50)
    (proofSizeExpKib := 861) (proofSizeWorstKib := 1146) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

example : picoCombineDeepAli.ExitCriteria picoCombineJBR
    (aliBits := 110) (deepBits := 99)
    (lookupBits := [97])
    (rowBits := [75, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
                  98, 99, 100, 101, 102, 53, 110, 99, 97])
    (totalBits := 53)
    (proofSizeExpKib := 861) (proofSizeWorstKib := 1146) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

-- compress: 253 KiB (expected) / 308 KiB (worst case).
example : picoCompressDeepAli.ExitCriteria picoUDR
    (aliBits := 115) (deepBits := 104)
    (lookupBits := [98])
    (rowBits := [95, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
                  118, 119, 119, 120, 35, 115, 104, 98])
    (totalBits := 35)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 308) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

example : picoCompressDeepAli.ExitCriteria picoCompressJBR
    (aliBits := 106) (deepBits := 95)
    (lookupBits := [98])
    (rowBits := [61, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83,
                  84, 85, 86, 87, 57, 106, 95, 98])
    (totalBits := 57)
    (proofSizeExpKib := 253) (proofSizeWorstKib := 308) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

-- embed: 232 KiB (expected) / 281 KiB (worst case).
example : picoEmbedDeepAli.ExitCriteria picoUDR
    (aliBits := 115) (deepBits := 106)
    (lookupBits := [100])
    (rowBits := [97, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
                  119, 120, 35, 115, 106, 100])
    (totalBits := 35)
    (proofSizeExpKib := 232) (proofSizeWorstKib := 281) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

example : picoEmbedDeepAli.ExitCriteria picoEmbedJBR
    (aliBits := 106) (deepBits := 97)
    (lookupBits := [100])
    (rowBits := [63, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
                  86, 87, 57, 106, 97, 100])
    (totalBits := 57)
    (proofSizeExpKib := 232) (proofSizeWorstKib := 281) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ### Enclosure-granularity guard (verified where it bites) -/

example : sqrtLB (1/2) (2^40) < sqrtUB (1/2) (2^40) := by native_decide
example : sqrtLB (1/16) (2^40) < sqrtUB (1/16) (2^40) := by native_decide
example : jbrM (1/2) (1/40) (2^40) = 15 := by native_decide
example : jbrM (1/16) (1/320) (2^40) = 41 := by native_decide

end Soundcalc
