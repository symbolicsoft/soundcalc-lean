import Soundcalc.Circuit.SWIRL.ComputeError  -- SWIRLCfg + proofSizeBits + listErrs + ExitCriteria
import Soundcalc.Field.BabyBear               -- babyBear4 preset (OpenVM2 fields)

open Soundcalc

/-!
# OpenVM2 soundness configuration

OpenVM2 is a **SWIRL** zkVM (LogUp-GKR + ZeroCheck + stacked reduction, opened with a WHIR PCS),
so it uses `Soundcalc.Circuit.SWIRL`. Parameters are generated from
`soundcalc/zkvms/openvm2/openvm2.toml`, validated against `reports/openvm2.md`.

Six recursion circuits over BabyBear⁴:

* **app** / **leaf** — unique-decoding (UDR).
* **internal_for_leaf** / **internal_recursive** (identical) — list-decoding at `m = 2`.
* **hook** / **root** — list-decoding at `m = 1`.

Each circuit is byte-checked against the report by one `SWIRLCfg.ExitCriteria` — the full
security row `(listErrs).map secBits` (in `listErrs` column order `[logup, gkr_sumcheck,
gkr_batching, zerocheck, constraint_batching, stacked_reduction, whir_mu_batching, whir_fold_rbr,
whir_proximity_gaps, whir_sumcheck, whir_shift_rbr, whir_query, whir_gamma_batching,
whir_ood_rbr, whir]`), the total, and the proof size in KiB. The list-decoding circuits exercise
the `sqrtLB`/`sqrtUB` + BCHKS25 estimation (granularity `g = 2^40`); every cell reproduces the
report.

Each AIR/trace `Bounded` carries the actual (main) value and the soundness/proof-size envelope
(`soundness_*`, which the `zkvm.py` chain ties `proof_size_*` to). For `hook`/`root` the TOML sets
no `soundness_*`, so actual = envelope.
-/

namespace Soundcalc

/-! ## app — unique-decoding (UDR) -/
def openvm2App : SWIRLCfg where
  name := "app"
  whir :=
    { hashBits := 256, field := babyBear4, logInvRate := 1, numIterations := 4,
      foldingFactors := [4, 4, 4, 4], logDegree := 24, batchSize := 2048, powerBatch := true,
      grindBatch := 15, constraintDegree := 3,
      grindFolding := [[5, 5, 5, 5], [5, 5, 5, 5], [5, 5, 5, 5], [5, 5, 5, 5]],
      numQueries := [193, 88, 81, 81], grindQueries := [20, 20, 20, 20],
      numOodSamples := [1, 1, 1], grindOod := [0, 0, 0] }
  lSkip := 4
  airs := { actual := 72, envelope := 100 };  logTraceHeight := { actual := 24, envelope := 24 }
  traceColumns := { actual := 24381, envelope := 30000 }
  interactions := { actual := 976, envelope := 1000 };  constraints := { actual := 3183, envelope := 5000 }
  logup := { maxInteractionCount := 2013265921, logMaxMessageLength := 7, powBits := 18 }
  numPublicValues := 20

example : openvm2App.ExitCriteria
    (rowBits := [102, 122, 123, 117, 111, 107, 102, 104, 104, 127, 100, 100, 116, 104, 100])
    (totalBits := 100) (proofSizeKib := 26175) := by
  native_decide

/-! ## leaf — unique-decoding (UDR) -/
def openvm2Leaf : SWIRLCfg where
  name := "leaf"
  whir :=
    { hashBits := 256, field := babyBear4, logInvRate := 2, numIterations := 3,
      foldingFactors := [4, 4, 4], logDegree := 21, batchSize := 2048, powerBatch := true,
      grindBatch := 13, constraintDegree := 4,
      grindFolding := [[4, 4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4]],
      numQueries := [118, 84, 81], grindQueries := [20, 20, 20],
      numOodSamples := [1, 1], grindOod := [0, 0] }
  lSkip := 4
  airs := { actual := 42, envelope := 50 };  logTraceHeight := { actual := 21, envelope := 21 }
  traceColumns := { actual := 1679, envelope := 2000 }
  interactions := { actual := 78, envelope := 100 };  constraints := { actual := 282, envelope := 1000 }
  logup := { maxInteractionCount := 2013265921, logMaxMessageLength := 7, powBits := 18 }
  numPublicValues := 121

example : openvm2Leaf.ExitCriteria
    (rowBits := [102, 122, 123, 117, 113, 111, 102, 105, 105, 126, 100, 100, 116, 107, 100])
    (totalBits := 100) (proofSizeKib := 15509) := by
  native_decide

/-! ## internal_for_leaf — list-decoding, `m = 2` -/
def openvm2InternalForLeaf : SWIRLCfg where
  name := "internal_for_leaf"
  whir :=
    { hashBits := 256, field := babyBear4, logInvRate := 3, numIterations := 3,
      foldingFactors := [4, 4, 4], logDegree := 19, batchSize := 512, powerBatch := true,
      grindBatch := 20, constraintDegree := 4,
      grindFolding := [[18, 18, 18, 18], [18, 18, 18, 18], [18, 18, 18, 18]],
      numQueries := [68, 30, 20], grindQueries := [20, 20, 20],
      numOodSamples := [1, 1], grindOod := [0, 0] }
  lSkip := 2
  airs := { actual := 42, envelope := 50 };  logTraceHeight := { actual := 19, envelope := 19 }
  traceColumns := { actual := 1663, envelope := 2000 }
  interactions := { actual := 78, envelope := 100 };  constraints := { actual := 282, envelope := 1000 }
  logup := { maxInteractionCount := 2013265921, logMaxMessageLength := 7, powBits := 19 }
  numPublicValues := 121
  explicitM := some 2

example : openvm2InternalForLeaf.ExitCriteria
    (rowBits := [100, 122, 123, 116, 110, 108, 102, 103, 103, 134, 100, 100, 111, 100, 100])
    (totalBits := 100) (proofSizeKib := 2393) := by
  native_decide

/-! ## internal_recursive — identical parameters to `internal_for_leaf` -/
def openvm2InternalRecursive : SWIRLCfg :=
  { openvm2InternalForLeaf with name := "internal_recursive" }

example : openvm2InternalRecursive.ExitCriteria
    (rowBits := [100, 122, 123, 116, 110, 108, 102, 103, 103, 134, 100, 100, 111, 100, 100])
    (totalBits := 100) (proofSizeKib := 2393) := by
  native_decide

def openvm2Hook : SWIRLCfg where
  name := "hook"
  whir :=
    { hashBits := 256, field := babyBear4, logInvRate := 2, numIterations := 3,
      foldingFactors := [4, 4, 4], logDegree := 20, batchSize := 80, powerBatch := true,
      grindBatch := 11, constraintDegree := 4,
      grindFolding := [[12, 12, 12, 12], [12, 12, 12, 12], [12, 12, 12, 12]],
      numQueries := [193, 42, 24], grindQueries := [20, 20, 20],
      numOodSamples := [1, 1], grindOod := [0, 0] }
  lSkip := 2
  airs := { actual := 50, envelope := 50 };  logTraceHeight := { actual := 20, envelope := 20 }
  traceColumns := { actual := 2000, envelope := 2000 }
  interactions := { actual := 100, envelope := 100 };  constraints := { actual := 1000, envelope := 1000 }
  logup := { maxInteractionCount := 2013265921, logMaxMessageLength := 7, powBits := 18 }
  numPublicValues := 18
  explicitM := some 1

example : openvm2Hook.ExitCriteria
    (rowBits := [101, 122, 123, 118, 112, 110, 100, 102, 102, 129, 100, 100, 112, 102, 100])
    (totalBits := 100) (proofSizeKib := 1330) := by
  native_decide

def openvm2Root : SWIRLCfg where
  name := "root"
  whir :=
    { hashBits := 256, field := babyBear4, logInvRate := 4, numIterations := 3,
      foldingFactors := [4, 4, 4], logDegree := 20, batchSize := 18, powerBatch := true,
      grindBatch := 20, constraintDegree := 4,
      grindFolding := [[20, 20, 20, 20], [20, 20, 20, 20], [20, 20, 20, 20]],
      numQueries := [57, 28, 19], grindQueries := [20, 20, 20],
      numOodSamples := [1, 1], grindOod := [0, 0] }
  lSkip := 2
  airs := { actual := 50, envelope := 50 };  logTraceHeight := { actual := 21, envelope := 21 }
  traceColumns := { actual := 2000, envelope := 2000 }
  interactions := { actual := 100, envelope := 100 };  constraints := { actual := 1000, envelope := 1000 }
  logup := { maxInteractionCount := 2013265921, logMaxMessageLength := 7, powBits := 18 }
  numPublicValues := 16
  explicitM := some 1

example : openvm2Root.ExitCriteria
    (rowBits := [100, 122, 123, 117, 111, 109, 107, 105, 105, 136, 100, 100, 112, 100, 100])
    (totalBits := 100) (proofSizeKib := 270) := by
  native_decide

end Soundcalc
