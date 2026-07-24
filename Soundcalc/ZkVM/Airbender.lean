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


/-- The two regimes for Airbender. `η` is derived from `(mersenne31_4, ρ, g)` by
    `JBR` itself (BCHKS25's default gap, `= 1/40` for `ρ = 1/2`); `g = 2^40` is the
    A1 granularity. -/
abbrev airbenderUDR : Regime := UDR mersenne31_4
abbrev airbenderJBR : Regime := JBR mersenne31_4 (2^40)

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

/-! ## A4–A6 exit criteria (bundled)

Row entries: batching | commit×5 | query | ALI | DEEP | 4 lookups.
Covers all 13 cells including JBR commit rounds 1–3 (previously unchecked). Lookup
cells and proof sizes are regime-independent, hence identical across both calls below.

The JBR total (67) exceeds the UDR total (64) because the query cell dominates and
JBR's query bound is tighter: Johnson's larger decode window cuts the query error. -/

example : airbenderDeepAli.ExitCriteria airbenderUDR
    (aliBits := 114) (deepBits := 110)
    (lookupBits := [94, 99, 98, 100])
    (rowBits := [90, 106, 110, 114, 118, 121, 64, 114, 110, 94, 99, 98, 100])
    (totalBits := 64)
    (proofSizeExpKib := 1836) (proofSizeWorstKib := 1951) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

example : airbenderDeepAli.ExitCriteria airbenderJBR
    (aliBits := 109) (deepBits := 105)
    (lookupBits := [94, 99, 98, 100])
    (rowBits := [68, 83, 87, 91, 95, 98, 67, 109, 105, 94, 99, 98, 100])
    (totalBits := 67)
    (proofSizeExpKib := 1836) (proofSizeWorstKib := 1951) := by
  unfold DeepAliCfg.ExitCriteria; native_decide

/-! ### Enclosure-granularity guard (A1/A2 knob, verified where it bites) -/

example : sqrtLB (1/2) (2^40) < sqrtUB (1/2) (2^40) := by native_decide
example : jbrM (1/2) (1/40) (2^40) = 15 := by native_decide

end Soundcalc
