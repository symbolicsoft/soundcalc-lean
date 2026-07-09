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

/-- The two regimes for Airbender. `η = 1/40`, `g = 2^40` are the pinned gap and
    A1 granularity. -/
abbrev airbenderUDR : Regime := UDR mersenne31_4
abbrev airbenderJBR : Regime := JBR mersenne31_4 (1/40) (2^40)

/-! ## DEEP-ALI configuration (tied to FRI by construction) -/

/-- Airbender DEEP-ALI configuration.  `field`, `ρ`, and `traceLength` are taken
    directly from `airbenderFRI` so they cannot diverge from the FRI config. -/
def airbenderDeepAli : DeepAliCfg where
  field          := airbenderFRI.field
  ρ              := airbenderFRI.ρ
  traceLength    := airbenderFRI.denseLen
  numConstraints := 928
  airMaxDegree   := 2
  maxCombo       := 2
  grindDeep      := 12

-- Consistency: provable by rfl since the fields are defined as equal.
example : airbenderDeepAli.field       = airbenderFRI.field    := rfl
example : airbenderDeepAli.ρ           = airbenderFRI.ρ        := rfl
example : airbenderDeepAli.traceLength = airbenderFRI.denseLen := rfl

/-- Multi-point side condition: the decode window `(1 − θUB) · D` exceeds `H + m_max`.
    Uses `θUB` (upper bound on true θ) so the checked window is a lower bound on the
    true window — if the guard passes here it passes with the exact θ. -/
theorem DeepAliCfg.multiPoint_ok (c : DeepAliCfg) (R : Regime)
    (hc : c = airbenderDeepAli)
    (hR : R = UDR c.field ∨ R = JBR c.field (1/40) (2^40)) :
    ((c.traceLength : Q) + (c.maxCombo : Q)) <
      (1 - R.θUB c.ρ c.traceLength) * ((c.traceLength : Q) / (c.ρ : Q)) := by
  subst hc
  rcases hR with rfl | rfl <;> native_decide

/-! ## A4 exit criteria -/

example : secBits (airbenderDeepAli.aliErr airbenderUDR) = 114 := by native_decide
example : secBits (airbenderDeepAli.deepErr airbenderUDR) = 110 := by native_decide
example : secBits (airbenderDeepAli.aliErr airbenderJBR) = 109 := by native_decide
example : secBits (airbenderDeepAli.deepErr airbenderJBR) = 105 := by native_decide

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

/-! ## Cell error collection -/

/-- All per-cell errors for regime `R`:
    batching, one commit cell per fold, query, ALI, DEEP, 4 lookups (regime-independent). -/
def airbenderRounds (R : Regime) : List ℚ :=
  [airbenderFRI.batchingErrPowers R] ++
  (List.range airbenderFRI.foldingFactors.length).map (airbenderFRI.commitErr R) ++
  [airbenderFRI.queryErr R,
   airbenderDeepAli.aliErr R,
   airbenderDeepAli.deepErr R,
   airbenderGenericLookup.errUB,
   airbenderRangeCheck16.errUB,
   airbenderRangeCheck19.errUB,
   airbenderDecoder.errUB]

/-- Worst-case (maximum) error across all Airbender cells.
    `secBits (airbenderTotalErr R) = ((airbenderRounds R).map secBits).minimum` by `secBits_min'`. -/
def airbenderTotalErr (R : Regime) : ℚ := (airbenderRounds R).foldr max 0

/-! ### Per-cell security bits — one theorem per regime row

Entries: batching | commit×5 | query | ALI | DEEP | 4 lookups.
Covers all 13 cells including JBR commit rounds 1–3 (previously unchecked). -/

theorem ab_udr_row : (airbenderRounds airbenderUDR).map secBits =
    [90, 106, 110, 114, 118, 121, 64, 114, 110, 94, 99, 98, 100] := by native_decide

theorem ab_jbr_row : (airbenderRounds airbenderJBR).map secBits =
    [68, 83, 87, 91, 95, 98, 67, 109, 105, 94, 99, 98, 100] := by native_decide

/-! ### Totals — min over the row, via `secBits_min'` (pure order theory, no cryptography)

The JBR total (67) exceeds the UDR total (64) because the query cell dominates and
JBR's query bound is tighter: Johnson's larger decode window cuts the query error. -/

theorem ab_udr_total : secBits (airbenderTotalErr airbenderUDR) = 64 := by native_decide
theorem ab_jbr_total : secBits (airbenderTotalErr airbenderJBR) = 67 := by native_decide

/-! ### Enclosure-granularity guard (A1/A2 knob, verified where it bites) -/

example : sqrtLB (1/2) (2^40) < sqrtUB (1/2) (2^40) := by native_decide
example : jbrM (1/2) (1/40) (2^40) = 15 := by native_decide

end Soundcalc
