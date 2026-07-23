/- Automatically generated from `LeanEmitter.lean` and `sp1.toml`. -/

import Mathlib
import Soundcalc

open Soundcalc

/- ZkVM `SP1` | Circuit `core` | Lookup `lookup` -/

def SP1_core_lookup_lookup : LookupCfg where
  name            := "lookup"
  field           := koalaBear4
  isLogUpMultivar := true
  rowsL           := 4194304
  rowsT           := 0
  numColumnsS     := 107
  numLookupsM     := 1911
  grindBitsLookup := 12

/- ZkVM `SP1` | Circuit `core` -/

def SP1_core_FRI : FRIConfig where
  hashBits        := 248
  ρ               := ⟨1/4, by norm_num⟩
  traceLen        := 4194304
  field           := koalaBear4
  denseLen        := 2097152
  batchSize       := 193
  powerBatch      := false
  multilinBatch   := true
  numQueries      := 124
  foldingFactors  := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  earlyStopDeg    := 4
  grindQuery      := 16
  grindBatch      := 5

def SP1_core_jagged : JaggedCfg where
  name            := "core"
  field           := koalaBear4
  proofSystName   := "Jagged"
  densePCS        := SP1_core_FRI
  traceLength     := 4194304
  traceWidth      := 3741
  numConstraints  := 3412
  airMaxDegree    := 3
  lookups         := [SP1_core_lookup_lookup]

/- Sanity check against `sp1.md`'s reported values.-/

/- **Security bits table** -/
example : secBits (SP1_core_jagged.totalErr) = 100 := by native_decide

example : secBits (SP1_core_lookup_lookup.errUB) = 100 := by native_decide

example : secBits (SP1_core_FRI.batchingErr (UDR koalaBear4)) = 104 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 0) = 103 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 9) = 112 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 10) = 113 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 11) = 114 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 12) = 115 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 13) = 116 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 14) = 117 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 15) = 118 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 16) = 119 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 17) = 120 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 18) = 121 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 1) = 104 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 19) = 121 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 20) = 122 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 2) = 105 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 3) = 106 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 4) = 107 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 5) = 108 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 6) = 109 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 7) = 110 := by native_decide
example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 8) = 111 := by native_decide
example : secBits (SP1_core_FRI.queryErr (UDR koalaBear4)) = 100 := by native_decide

example : secBits SP1_core_jagged.reduceErr = 116 := by native_decide
example : secBits SP1_core_jagged.zerocheckErr = 112 := by native_decide

/- **Proof sizes (FRI-only, Jagged circuit)** -/
example : sp1CoreFRI.proofSizeExp          / KIB = 913  := by native_decide
example : sp1CoreFRI.proofSizeWorst        / KIB = 1474 := by native_decide

example : sp1CoreJagged.proofSizeExp       / KIB = 918  := by native_decide
example : sp1CoreJagged.proofSizeWorst     / KIB = 1479 := by native_decide

/- ZkVM `SP1` | Circuit `compress` | Lookup `lookup` -/

def SP1_compress_lookup_lookup : LookupCfg where
  name            := "lookup"
  field           := koalaBear4
  isLogUpMultivar := true
  rowsL           := 2097152
  rowsT           := 0
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

/- ZkVM `SP1` | Circuit `compress` -/

def SP1_compress_FRI : FRIConfig where
  hashBits        := 248
  ρ               := ⟨1/4, by norm_num⟩
  traceLen        := 2097152
  field           := koalaBear4
  denseLen        := 1048576
  batchSize       := 128
  powerBatch      := false
  multilinBatch   := true
  numQueries      := 124
  foldingFactors  := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  earlyStopDeg    := 4
  grindQuery      := 16
  grindBatch      := 5

def SP1_compress_jagged : JaggedCfg where
  name            := "compress"
  field           := koalaBear4
  proofSystName   := "Jagged"
  densePCS        := SP1_compress_FRI
  traceLength     := 2097152
  traceWidth      := 326
  numConstraints  := 204
  airMaxDegree    := 3
  lookups         := [SP1_compress_lookup_lookup]

/- Sanity check against `sp1.md`'s reported values.-/

/- **Security bits table** -/
example : secBits (SP1_compress_jagged.totalErr) = 100 := by native_decide

example : secBits (SP1_compress_lookup_lookup.errUB) = 107 := by native_decide

example : secBits (SP1_compress_FRI.batchingErr (UDR koalaBear4)) = 105 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 0) = 104 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 9) = 113 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 10) = 114 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 11) = 115 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 12) = 116 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 13) = 117 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 14) = 118 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 15) = 119 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 16) = 120 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 17) = 121 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 18) = 121 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 1) = 105 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 19) = 122 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 2) = 106 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 3) = 107 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 4) = 108 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 5) = 109 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 6) = 110 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 7) = 111 := by native_decide
example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 8) = 112 := by native_decide
example : secBits (SP1_compress_FRI.queryErr (UDR koalaBear4)) = 100 := by native_decide

example : secBits SP1_compress_jagged.reduceErr = 116 := by native_decide
example : secBits SP1_compress_jagged.zerocheckErr = 115 := by native_decide

/- **Proof sizes (FRI-only, Jagged circuit)** -/
example : sp1CompressFRI.proofSizeExp      / KIB = 730  := by native_decide
example : sp1CompressFRI.proofSizeWorst    / KIB = 1261 := by native_decide

example : sp1CompressJagged.proofSizeExp   / KIB = 735  := by native_decide
example : sp1CompressJagged.proofSizeWorst / KIB = 1267 := by native_decide

/- ZkVM `SP1` | Circuit `shrink` | Lookup `lookup` -/

def SP1_shrink_lookup_lookup : LookupCfg where
  name            := "lookup"
  field           := koalaBear4
  isLogUpMultivar := true
  rowsL           := 524288
  rowsT           := 0
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

/- ZkVM `SP1` | Circuit `shrink` -/

def SP1_shrink_FRI : FRIConfig where
  hashBits        := 248
  ρ               := ⟨1/8, by norm_num⟩
  traceLen        := 524288
  field           := koalaBear4
  denseLen        := 262144
  batchSize       := 128
  powerBatch      := false
  multilinBatch   := true
  numQueries      := 94
  foldingFactors  := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  earlyStopDeg    := 8
  grindQuery      := 22
  grindBatch      := 5

def SP1_shrink_jagged : JaggedCfg where
  name            := "shrink"
  field           := koalaBear4
  proofSystName   := "Jagged"
  densePCS        := SP1_shrink_FRI
  traceLength     := 524288
  traceWidth      := 326
  numConstraints  := 204
  airMaxDegree    := 3
  lookups         := [SP1_shrink_lookup_lookup]

/- Sanity check against `sp1.md`'s reported values.-/

/- **Security bits table** -/
example : secBits (SP1_shrink_jagged.totalErr) = 100 := by native_decide

example : secBits (SP1_shrink_lookup_lookup.errUB) = 109 := by native_decide

example : secBits (SP1_shrink_FRI.batchingErr (UDR koalaBear4)) = 106 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 0) = 105 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 9) = 114 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 10) = 115 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 11) = 116 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 12) = 117 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 13) = 118 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 14) = 119 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 15) = 120 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 16) = 120 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 17) = 121 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 1) = 106 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 2) = 107 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 3) = 108 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 4) = 109 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 5) = 110 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 6) = 111 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 7) = 112 := by native_decide
example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 8) = 113 := by native_decide
example : secBits (SP1_shrink_FRI.queryErr (UDR koalaBear4)) = 100 := by native_decide

example : secBits SP1_shrink_jagged.reduceErr = 116 := by native_decide
example : secBits SP1_shrink_jagged.zerocheckErr = 115 := by native_decide

/- **Proof sizes (FRI-only, Jagged circuit)** -/
example : sp1ShrinkFRI.proofSizeExp        / KIB = 524  := by native_decide
example : sp1ShrinkFRI.proofSizeWorst      / KIB = 882  := by native_decide

example : sp1ShrinkJagged.proofSizeExp     / KIB = 529  := by native_decide
example : sp1ShrinkJagged.proofSizeWorst   / KIB = 887  := by native_decide

/- Theorems tying together the hand-written configs in
   `Soundcalc/ZkVM/SP1.lean` with the ones parsed from `sp1.toml`.-/
example : SP1_core_jagged = sp1CoreJagged := by rfl
example : SP1_compress_jagged = sp1CompressJagged := by rfl
example : SP1_shrink_jagged = sp1ShrinkJagged := by rfl