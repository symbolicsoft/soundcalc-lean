import Soundcalc.Circuit.Jagged
import Soundcalc.Circuit.SWIRL.ComputeError
import Soundcalc.SecBits
import Soundcalc.PCS.FRI
import Soundcalc.PCS.PCS
import Soundcalc.Lookup
import Soundcalc.Field.KoalaBear

namespace Soundcalc

/-!
# zkDTVM (v0.8.0) — mixed architecture over KoalaBear⁵

`core`/`compress`/`shrink` use the non-stacking Jagged/FRI path (unique decoding); `root_shrink`
uses the SWIRL/WHIR stacked path (list decoding, `m = 2`). Parameters from
`soundcalc/zkvms/zkdtvm_v080/zkdtvm_v080.toml`, validated against `reports/zkdtvm.md`.
-/

/-! ## core — Jagged/FRI, unique decoding -/
def zkdtvmCoreFRI : FRIConfig where
  hashBits := 248; field := koalaBear5; ρ := Rate.half
  denseLen := 2097152; batchSize := 62928
  powerBatch := true; multilinBatch := false
  numQueries := 261; foldingFactors := List.replicate 21 2; earlyStopDeg := 2
  grindQuery := 20; grindBatch := 10

def zkdtvmCoreLookup : LookupCfg where
  name := "lookup"; field := koalaBear5; isLogUpMultivar := false; multilinearFingerprint := true
  rowsT := 0; rowsL := 4194304; numColumnsS := 103; numLookupsM := 14
  grindBitsLookup := 10

def zkdtvmCoreJagged : JaggedCfg where
  name := "core"; field := koalaBear5
  densePCS := .fri zkdtvmCoreFRI
  traceWidth := 31209; traceLength := 4194304
  numConstraints := 29053; airMaxDegree := 3
  lookups := [zkdtvmCoreLookup]

/-! ## compress — Jagged/FRI, unique decoding -/
def zkdtvmCompressFRI : FRIConfig where
  hashBits := 248; field := koalaBear5; ρ := Rate.quarter
  denseLen := 1048576; batchSize := 128
  powerBatch := true; multilinBatch := false
  numQueries := 160; foldingFactors := List.replicate 20 2; earlyStopDeg := 4
  grindQuery := 20; grindBatch := 10

def zkdtvmCompressLookup : LookupCfg where
  name := "lookup"; field := koalaBear5; isLogUpMultivar := false; multilinearFingerprint := true
  rowsT := 0; rowsL := 2097152; numColumnsS := 6; numLookupsM := 50
  grindBitsLookup := 10

def zkdtvmCompressJagged : JaggedCfg where
  name := "compress"; field := koalaBear5
  densePCS := .fri zkdtvmCompressFRI
  traceWidth := 326; traceLength := 2097152
  numConstraints := 204; airMaxDegree := 3
  lookups := [zkdtvmCompressLookup]

/-! ## shrink — Jagged/FRI, unique decoding -/
def zkdtvmShrinkFRI : FRIConfig where
  hashBits := 248; field := koalaBear5; ρ := Rate.eighth
  denseLen := 524288; batchSize := 128
  powerBatch := true; multilinBatch := false
  numQueries := 131; foldingFactors := List.replicate 20 2; earlyStopDeg := 4
  grindQuery := 20; grindBatch := 10

def zkdtvmShrinkLookup : LookupCfg where
  name := "lookup"; field := koalaBear5; isLogUpMultivar := false; multilinearFingerprint := true
  rowsT := 0; rowsL := 1048576; numColumnsS := 6; numLookupsM := 50
  grindBitsLookup := 10

def zkdtvmShrinkJagged : JaggedCfg where
  name := "shrink"; field := koalaBear5
  densePCS := .fri zkdtvmShrinkFRI
  traceWidth := 326; traceLength := 1048576
  numConstraints := 204; airMaxDegree := 3
  lookups := [zkdtvmShrinkLookup]

def zkdtvmRootShrinkWHIR : WHIRConfig :=
  { hashBits := 256, field := koalaBear5, logInvRate := 4, numIterations := 3,
    foldingFactors := [4, 4, 4], logDegree := 18, batchSize := 1, powerBatch := true,
    grindBatch := 20, constraintDegree := 3,
    grindFolding := [[20, 20, 20, 20], [20, 20, 20, 20], [20, 20, 20, 20]],
    numQueries := [77, 38, 26], grindQueries := [20, 20, 20],
    numOodSamples := [1, 1], grindOod := [0, 0]
  }


/-! ## root_shrink — SWIRL/WHIR, list decoding (`m = 2`) -/
def zkdtvmRootShrink : SWIRLCfg where
  name := "root_shrink"
  field := koalaBear5
  whir := zkdtvmRootShrinkWHIR
  lSkip := 6
  airs := { actual := 50 };  logTraceHeight := { actual := 18 }
  traceColumns := { actual := 326 }
  interactions := { actual := 100 };  constraints := { actual := 204 }
  logup := { maxInteractionCount := 52428800, logMaxMessageLength := 6, powBits := 10 }
  explicitM := some 2

/-! ## Exit criteria — each circuit's full security row + total + proof size, vs `reports/zkdtvm.md` -/

-- core: 311725 KiB (expected) / 312976 KiB (worst case).
example : zkdtvmCoreJagged.ExitCriteria
    (reduceBits := 147) (zerocheckBits := 140) (lookupBits := [136])
    (rowBits := [147, 140, 129, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                  147, 148, 149, 150, 151, 152, 153, 153, 154, 128, 136])
    (totalBits := 128)
    (proofSizeExpKib := 311725) (proofSizeWorstKib := 312976) := by
  native_decide

-- compress: 1022 KiB (expected) / 1736 KiB (worst case).
example : zkdtvmCompressJagged.ExitCriteria
    (reduceBits := 147) (zerocheckBits := 146) (lookupBits := [136])
    (rowBits := [147, 146, 137, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                  147, 148, 149, 150, 151, 152, 152, 153, 128, 136])
    (totalBits := 128)
    (proofSizeExpKib := 1022) (proofSizeWorstKib := 1736) := by
  native_decide

-- shrink: 856 KiB (expected) / 1422 KiB (worst case).
example : zkdtvmShrinkJagged.ExitCriteria
    (reduceBits := 147) (zerocheckBits := 146) (lookupBits := [137])
    (rowBits := [147, 146, 137, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
                  147, 148, 149, 150, 151, 151, 152, 153, 128, 137])
    (totalBits := 128)
    (proofSizeExpKib := 856) (proofSizeWorstKib := 1422) := by
  native_decide

-- root_shrink: 200 KiB (expected = worst). `w_stack = 1` ⇒ no `whir_mu_batching` cell.
example : zkdtvmRootShrink.ExitCriteria
    (rowBits := [128, 153, 154, 143, 143, 142, 134, 134, 167, 140, 140, 142, 132, 132])
    (totalBits := 128) (proofSizeKib := 200) := by
  native_decide

end Soundcalc
