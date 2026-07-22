import Soundcalc.Circuit.DeepAli
import Soundcalc.PCS.FRI
import Soundcalc.Lookup
import Soundcalc.Field

/-!
# Airbender soundness configuration (A6)

Join point for A0–A5: all cell theorems and both regime totals.

`airbenderFRI` and `airbenderDeepAli` are plain Lean literals generated from
`airbender.toml` — not parsed at proof time (same S7 discipline as SP1). Keeping
them as literals makes every cell theorem transparent to `native_decide`.

## Two-regime strategy

* **UDR** (`airbenderUDR`): classical unique-decoding threshold `θ = (1-ρ)/2`.
  All cells are exact rationals; proofs are the same flavour as every SP1 theorem.
* **JBR** (`airbenderJBR`): Johnson Bound Regime with `η = 1/40`, `g = 2^40`.
  `√ρ` is enclosed by `sqrtLB`/`sqrtUB`; cells are certified upper bounds proved
  via `native_decide` over rational arithmetic.

## TCB note

All cell and total theorems use `native_decide`, which compiles the decision
procedure to native code via the `ofReduceBool` kernel reduction. This extends
the TCB by the Lean compiler for those goals. The stress cases are the
`(m + 1/2)^5 = (31/2)^5`-scale numerators over `|F| ≈ 2^124` multiplied by the
`g = 2^40` enclosure denominators; `decide` (kernel reduction) would time out on
these. The regime-independent lookup cells (A5) are the only ones provable by
plain `decide`.
-/

namespace Soundcalc

/-! ## Configuration literals (generated from `airbender.toml`) -/
/- domainSize D = 2^24 / (1/2) = 2^25 -/

def airbenderFRI : FRIConfig where
  hashBits       := 256
  field          := mersenne31_4
  ρ              := ⟨1/2, by norm_num, by norm_num⟩
  traceLen       := 2^24
  denseLen       := 2^24          -- trace length = FRI dimension
  batchSize      := 1225
  powerBatch     := true          -- Airbender uses power batching
  multilinBatch  := false
  numQueries     := 87
  foldingFactors := [16, 16, 16, 8, 8]
  earlyStopDeg   := 128
  grindQuery     := 28
  grindBatch     := 0             -- Airbender does not grind the batching phase
  grindCommit    := 5             -- 5 bits per folding round (grinding_commit_phase)

/-! ## Lookup configurations (univariate logup, regime-independent) -/
def airbenderGenericLookup : LookupCfg where
  name := "genericLookup"; field := mersenne31_4; isLogUpMultivar := false
  rowsT := 16777215; rowsL := 16777215; numColumnsS := 4; numLookupsM := 208
  grindBitsLookup := 5

def airbenderRangeCheck16 : LookupCfg where
  name := "rangeCheck16"; field := mersenne31_4; isLogUpMultivar := false
  rowsT := 65536; rowsL := 16777215; numColumnsS := 1; numLookupsM := 34
  grindBitsLookup := 5

def airbenderRangeCheck19 : LookupCfg where
  name := "rangeCheck19"; field := mersenne31_4; isLogUpMultivar := false
  rowsT := 524288; rowsL := 16777215; numColumnsS := 1; numLookupsM := 86
  grindBitsLookup := 5

def airbenderDecoder : LookupCfg where
  name := "decoder"; field := mersenne31_4; isLogUpMultivar := false
  rowsT := 16777215; rowsL := 16777215; numColumnsS := 10; numLookupsM := 1
  grindBitsLookup := 5


/-- The two regimes for Airbender. `η = 1/40`, `g = 2^40` are the pinned gap and
    A1 granularity. -/
abbrev airbenderUDR : Regime := UDR mersenne31_4
abbrev airbenderJBR : Regime := JBR mersenne31_4 (1/40) (2^40)

/-! ## DEEP-ALI configuration (tied to FRI by construction) -/

/-- Airbender DEEP-ALI configuration. -/
def airbenderDeepAli : DeepAliCfg where
  name           := "Airbender"
  proofSystName  := "DEEP-ALI"
  field          := airbenderFRI.field
  densePCS       := airbenderFRI
  numConstraints := 928
  airMaxDegree   := 2
  maxCombo       := 2
  grindDeep      := 12
  lookups        := [airbenderGenericLookup,
                     airbenderRangeCheck16,
                     airbenderRangeCheck19,
                     airbenderDecoder]

/-- Airbender satisfies the DEEP-ALI multi-point side condition (`DeepAliCfg.multiPointOk`)
    in both regimes. -/
theorem airbenderDeepAli_multiPoint_ok (R : Regime)
    (hR : R = airbenderUDR ∨ R = airbenderJBR) :
    airbenderDeepAli.multiPointOk R := by
  unfold DeepAliCfg.multiPointOk
  rcases hR with rfl | rfl <;> native_decide

/-! ## A4 exit criteria -/

example : secBits (airbenderDeepAli.aliErr airbenderUDR) = 114 := by native_decide
example : secBits (airbenderDeepAli.deepErr airbenderUDR) = 110 := by native_decide
example : secBits (airbenderDeepAli.aliErr airbenderJBR) = 109 := by native_decide
example : secBits (airbenderDeepAli.deepErr airbenderJBR) = 105 := by native_decide

/-! ### Per-cell security bits — one theorem per regime row

Entries: batching | commit×5 | query | ALI | DEEP | 4 lookups.
Covers all 13 cells including JBR commit rounds 1–3 (previously unchecked). -/

theorem ab_udr_row : (airbenderDeepAli.listErrs airbenderUDR).map secBits =
    [90, 106, 110, 114, 118, 121, 64, 114, 110, 94, 99, 98, 100] := by native_decide

theorem ab_jbr_row : (airbenderDeepAli.listErrs airbenderJBR).map secBits =
    [68, 83, 87, 91, 95, 98, 67, 109, 105, 94, 99, 98, 100] := by native_decide

/-! ### Totals — min over the row, via `secBits_min'` (pure order theory, no cryptography)

The JBR total (67) exceeds the UDR total (64) because the query cell dominates and
JBR's query bound is tighter: Johnson's larger decode window cuts the query error. -/

theorem ab_udr_total : secBits (airbenderDeepAli.totalErr airbenderUDR) = 64 := by native_decide
theorem ab_jbr_total : secBits (airbenderDeepAli.totalErr airbenderJBR) = 67 := by native_decide

/-! ### Enclosure-granularity guard (A1/A2 knob, verified where it bites) -/

example : sqrtLB (1/2) (2^40) < sqrtUB (1/2) (2^40) := by native_decide
example : jbrM (1/2) (1/40) (2^40) = 15 := by native_decide


/-! ### Airbender proof sizes -/

-- Airbender: 1836 KiB (expected) / 1951 KiB (worst case).
example : airbenderDeepAli.proofSizeExp  / KIB = 1836 := by native_decide
example : airbenderDeepAli.proofSizeWorst / KIB = 1951 := by native_decide

end Soundcalc
