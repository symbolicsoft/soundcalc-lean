import Soundcalc.Circuit.DeepAli
import Soundcalc.PCS.FRI
import Soundcalc.Lookup
import Soundcalc.Field

/-!
# OpenVM soundness configuration

OpenVM is a DEEP-ALI zkVM, so it only needs `Soundcalc.Circuit.DeepAli`
—  Parameters below are generated from `soundcalc/zkvms/openvm/openvm.toml` (mirrored at
<https://github.com/ethereum/soundcalc/blob/main/reports/openvm.md>).

## Circuits

* **app** / **leaf**: identical parameters (`ρ = 1/2`, `H = 2^23`, 23 FRI rounds).
* **internal**: `ρ = 1/4`, `H = 2^21`, 21 FRI rounds, and a single lookup.

## Two-regime strategy

* **UDR** (`openvmUDR`): classical unique-decoding threshold, shared by all circuits.
* **JBR**: Johnson Bound Regime. The gap `η = max(ρ/20, √ρ/100)` (BCHKS25's default
  gap, `soundcalc/proxgaps/johnson_bound.py`) depends on `ρ`, so it differs per
  circuit: `η = 1/40` for app/leaf (`ρ = 1/2`), `η = 1/80` for internal (`ρ = 1/4`).
  `g = 2^40` is the same `√ρ`-enclosure granularity used by Airbender.
-/

namespace Soundcalc

/-! ## Configuration literals (generated from `openvm.toml`) -/

def openvmAppFRI : FRIConfig where
  hashBits       := 256
  field          := babyBear4
  ρ              := ⟨1/2, by norm_num, by norm_num⟩
  traceLen       := 2 ^ 23
  denseLen       := 2 ^ 23          -- trace length = FRI dimension
  batchSize      := 80000
  powerBatch     := true            -- OpenVM uses power batching
  multilinBatch  := false
  numQueries     := 193
  foldingFactors := List.replicate 23 2
  earlyStopDeg   := 2
  grindQuery     := 20
  grindBatch     := 20
  grindCommit    := 0               -- openvm.toml has no grinding_commit_phase

def openvmLeafFRI : FRIConfig where
  hashBits       := 256
  field          := babyBear4
  ρ              := ⟨1/2, by norm_num, by norm_num⟩
  traceLen       := 2 ^ 23
  denseLen       := 2 ^ 23
  batchSize      := 80000
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 193
  foldingFactors := List.replicate 23 2
  earlyStopDeg   := 2
  grindQuery     := 20
  grindBatch     := 20
  grindCommit    := 0

def openvmInternalFRI : FRIConfig where
  hashBits       := 256
  field          := babyBear4
  ρ              := ⟨1/4, by norm_num, by norm_num⟩
  traceLen       := 2 ^ 21
  denseLen       := 2 ^ 21
  batchSize      := 4000
  powerBatch     := true
  multilinBatch  := false
  numQueries     := 118
  foldingFactors := List.replicate 21 2
  earlyStopDeg   := 4
  grindQuery     := 20
  grindBatch     := 16
  grindCommit    := 0

/-! ## Lookup configuration (`internal` only; univariate logup) -/
/-
    Below numLookupsM is not specified in the TOML file, but the parse specifies the defualt values
    https://github.com/ethereum/soundcalc/blob/main/soundcalc/zkvms/zkvm.py#L27
-/

def openvmInternalLookup : LookupCfg where
  name := "lookup"; field := babyBear4; isLogUpMultivar := false
  rowsT := 0; rowsL := 128; numColumnsS := 1; numLookupsM := 1
  grindBitsLookup := 18

/-- The regimes for OpenVM. `η` is derived from `(babyBear4, ρ, g)` by `JBR` itself
    (BCHKS25's default gap), so a single `JBR babyBear4 (2^40)` value is correct for
    every circuit regardless of its `ρ` — kept as separate per-circuit abbrevs below
    purely for readability at call sites. -/
abbrev openvmUDR : Regime := UDR babyBear4
abbrev openvmAppJBR : Regime := JBR babyBear4 (2^40)
abbrev openvmLeafJBR : Regime := JBR babyBear4 (2^40)
abbrev openvmInternalJBR : Regime := JBR babyBear4 (2^40)

/-! ## DEEP-ALI configurations (tied to FRI by construction) -/
/-
    maxCombo is specified to be opening_points, again this is not directly specified.
-/

def openvmAppDeepAli : DeepAliCfg where
  name           := "app"
  proofSystName  := "DEEP-ALI"
  field          := openvmAppFRI.field
  densePCS       := openvmAppFRI
  numConstraints := 15000
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 5

def openvmLeafDeepAli : DeepAliCfg where
  name           := "leaf"
  proofSystName  := "DEEP-ALI"
  field          := openvmLeafFRI.field
  densePCS       := openvmLeafFRI
  numConstraints := 15000
  airMaxDegree   := 3
  maxCombo       := 2
  grindDeep      := 5

def openvmInternalDeepAli : DeepAliCfg where
  name           := "internal"
  proofSystName  := "DEEP-ALI"
  field          := openvmInternalFRI.field
  densePCS       := openvmInternalFRI
  numConstraints := 15000
  airMaxDegree   := 4
  maxCombo       := 2
  grindDeep      := 5
  lookups        := [openvmInternalLookup]

/-! ## Exit criteria (bundled)

Row entries: batching | commit×rounds | query | ALI | DEEP | lookups (internal only).
Lookup cells and proof sizes are regime-independent, hence identical across the
UDR/JBR calls for a given circuit.
Cross-checked against <https://github.com/ethereum/soundcalc/blob/main/reports/openvm.md>. -/

-- app/leaf: 234635 KiB (expected) / 235651 KiB (worst case).
example : openvmAppDeepAli.ExitCriteria openvmUDR
    (aliBits := 109) (deepBits := 103)
    (lookupBits := [])
    (rowBits := [105, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
                  115, 116, 117, 118, 119, 120, 121, 122, 122, 123, 100, 109, 103])
    (totalBits := 100)
    (proofSizeExpKib := 234635) (proofSizeWorstKib := 235651) := by
  native_decide

example : openvmAppDeepAli.ExitCriteria openvmAppJBR
    (aliBits := 104) (deepBits := 98)
    (lookupBits := [])
    (rowBits := [82, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
                  94, 95, 96, 97, 98, 99, 100, 101, 106, 104, 98])
    (totalBits := 79)
    (proofSizeExpKib := 234635) (proofSizeWorstKib := 235651) := by
  native_decide

example : openvmLeafDeepAli.ExitCriteria openvmUDR
    (aliBits := 109) (deepBits := 103)
    (lookupBits := [])
    (rowBits := [105, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
                  115, 116, 117, 118, 119, 120, 121, 122, 122, 123, 100, 109, 103])
    (totalBits := 100)
    (proofSizeExpKib := 234635) (proofSizeWorstKib := 235651) := by
  native_decide

example : openvmLeafDeepAli.ExitCriteria openvmLeafJBR
    (aliBits := 104) (deepBits := 98)
    (lookupBits := [])
    (rowBits := [82, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
                  94, 95, 96, 97, 98, 99, 100, 101, 106, 104, 98])
    (totalBits := 79)
    (proofSizeExpKib := 234635) (proofSizeWorstKib := 235651) := by
  native_decide

-- internal: 7687 KiB (expected) / 8231 KiB (worst case).
example : openvmInternalDeepAli.ExitCriteria openvmUDR
    (aliBits := 109) (deepBits := 105)
    (lookupBits := [134])
    (rowBits := [106, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
                  116, 117, 118, 118, 119, 120, 121, 122, 100, 109, 105, 134])
    (totalBits := 100)
    (proofSizeExpKib := 7687) (proofSizeWorstKib := 8231) := by
  native_decide

example : openvmInternalDeepAli.ExitCriteria openvmInternalJBR
    (aliBits := 103) (deepBits := 98)
    (lookupBits := [134])
    (rowBits := [80, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91,
                  92, 93, 94, 95, 96, 97, 133, 103, 98, 134])
    (totalBits := 77)
    (proofSizeExpKib := 7687) (proofSizeWorstKib := 8231) := by
  native_decide

/-! ### Enclosure-granularity guard (verified where it bites) -/

example : sqrtLB (1/2) (2^40) < sqrtUB (1/2) (2^40) := by native_decide
example : sqrtLB (1/4) (2^40) < sqrtUB (1/4) (2^40) := by native_decide
example : jbrM (1/2) (1/40) (2^40) = 15 := by native_decide
example : jbrM (1/4) (1/80) (2^40) = 21 := by native_decide

end Soundcalc
