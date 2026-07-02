/- Automatically generated from `TomlParser.lean` and `SP1.toml`. -/

import Mathlib
import Soundcalc
import Soundcalc.Field
import Soundcalc.Lookup

open Soundcalc

/- SP1: core -/

def SP1_core_jagged : JaggedCfg where
  field           := koalaBear4
  denseLen        := 2097152
  batchSize       := 193
  traceWidth      := 3741
  traceLength     := 4194304
  numConstraints  := 3412
  airMaxDegree    := 3

def SP1_core_FRI : FRIConfig where
  field           := koalaBear4
  ρ               := ⟨1/4, by norm_num⟩
  denseLen        := 2097152
  batchSize       := 193
  numQueries      := 124
  foldingFactors  := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  earlyStopDeg    := 4
  grindQuery      := 16
  grindBatch      := 5

def SP1_core_lookup_lookup : LookupCfg where
  field           := koalaBear4
  rowsT           := 0
  rowsL           := 4194304
  numColumnsS     := 107
  numLookupsM     := 1911
  grindBitsLookup := 12

/- Sanity check against `sp1.md`'s reported values.-/
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

/- SP1: compress -/

def SP1_compress_jagged : JaggedCfg where
  field           := koalaBear4
  denseLen        := 1048576
  batchSize       := 128
  traceWidth      := 326
  traceLength     := 2097152
  numConstraints  := 204
  airMaxDegree    := 3

def SP1_compress_FRI : FRIConfig where
  field           := koalaBear4
  ρ               := ⟨1/4, by norm_num⟩
  denseLen        := 1048576
  batchSize       := 128
  numQueries      := 124
  foldingFactors  := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  earlyStopDeg    := 4
  grindQuery      := 16
  grindBatch      := 5

def SP1_compress_lookup_lookup : LookupCfg where
  field           := koalaBear4
  rowsT           := 0
  rowsL           := 2097152
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

/- Sanity check against `sp1.md`'s reported values.-/
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

/- SP1: shrink -/

def SP1_shrink_jagged : JaggedCfg where
  field           := koalaBear4
  denseLen        := 262144
  batchSize       := 128
  traceWidth      := 326
  traceLength     := 524288
  numConstraints  := 204
  airMaxDegree    := 3

def SP1_shrink_FRI : FRIConfig where
  field           := koalaBear4
  ρ               := ⟨1/8, by norm_num⟩
  denseLen        := 262144
  batchSize       := 128
  numQueries      := 94
  foldingFactors  := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  earlyStopDeg    := 8
  grindQuery      := 22
  grindBatch      := 5

def SP1_shrink_lookup_lookup : LookupCfg where
  field           := koalaBear4
  rowsT           := 0
  rowsL           := 524288
  numColumnsS     := 6
  numLookupsM     := 53
  grindBitsLookup := 12

/- Sanity check against `sp1.md`'s reported values.-/
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

