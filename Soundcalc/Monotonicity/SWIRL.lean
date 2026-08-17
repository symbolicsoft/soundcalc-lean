import Soundcalc.Monotonicity.Basic
import Soundcalc.Circuit.SWIRL.ComputeError

/-!
# Monotonicity — SWIRL circuit cells

SWIRL's decoding regime is chosen by the single field `explicitM`: `none` is unique decoding
(list size `1`), `some m` is list decoding at multiplicity `m` (list size `(m+½)/√ρ`). No
`SWIRLCfg` invariant mentions `explicitM`, so it is a genuine **record-update knob** — unlike
`DeepAliCfg`'s regime, which is a separate `Regime` argument.

Exactly four of SWIRL's six non-WHIR cells are *linear in the list size* `ℓ = listSize logBlowup`:

  `logupErr`, `zerocheckErr`, `constraintBatchingErr`, `stackedReductionErr`

each of the shape `coef · ℓ / |F|` with a regime-independent `coef ≥ 0`. (`gkrSumcheckErr = 3/|F|`
and `gkrBatchingErr = 1/|F|` contain no `ℓ`, so they are regime-independent outright.) This file
proves those four monotone in `ℓ`, then lifts them to the `m` knob and to the unique-vs-list
comparison.

The headline is `SWIRLCfg.listErrs_unique_le_list`: on every one of the four, unique decoding is at
least as sound as list decoding. This is the SWIRL counterpart of `whir_listSize_ge_one` — list
decoding buys query security and pays for it on the algebraic cells.

The cell lemmas are stated in **two-config** form (two `SWIRLCfg`s agreeing on everything the
coefficient reads) rather than as record updates, so that both sides are syntactically identical
apart from `ℓ`; the record-update corollaries then discharge the agreement hypotheses by `rfl`.
-/

namespace Soundcalc

/-! ## Positivity facts the cells need -/

/-- The SWIRL error denominator `|F_ext| = p^e` is positive. -/
theorem SWIRLCfg.card_pos (c : SWIRLCfg) : 0 < c.card := by
  unfold SWIRLCfg.card
  have h : 0 < c.whir.field.card := c.whir.field.card_pos
  exact_mod_cast h

/-- The grinding factor `2^(−effpow)` is nonnegative (it is `1`, or a ratio of naturals). -/
theorem swEffpowFactor_nonneg (F : FieldParams) (powBits : ℕ) : 0 ≤ swEffpowFactor F powBits := by
  unfold swEffpowFactor
  split_ifs with h
  · norm_num
  · positivity

/-! ## The list size

`listSize lir = 1` (unique) or `((max m 1) + ½) / sqrtLB (2^(−lir)) g` (list). The side condition
`0 < sqrtLB (swRho lir) swSqrtG` is the same one `jbrErrLinear_conservative` carries; it holds
whenever `2^lir ≤ swSqrtG^2 = 2^80`, i.e. for every real config. -/

/-- **The list size is monotone in the multiplicity `m`.** The numerator `(max m 1) + ½` grows and
the `√ρ` denominator does not depend on `m`. -/
theorem SWIRLCfg.listSize_mono_multiplicity (c : SWIRLCfg) (lir : ℕ)
    (hsr : 0 < sqrtLB (swRho lir) swSqrtG) {m m' : ℕ} (h : m ≤ m') :
    ({c with explicitM := some m}).listSize lir
      ≤ ({c with explicitM := some m'}).listSize lir := by
  simp only [SWIRLCfg.listSize]
  have hmm : ((max m 1 : ℕ) : ℚ) ≤ ((max m' 1 : ℕ) : ℚ) := by
    have hn : max m 1 ≤ max m' 1 := max_le_max h le_rfl
    exact_mod_cast hn
  exact div_le_div_same (by linarith) hsr

/-- **List decoding never shrinks the list size.** `1` is the unique-regime list size, and the
list-regime one is `((max m 1) + ½)/√ρ ≥ 1` because `√ρ ≤ 1` while the numerator is `≥ 3/2`.
The SWIRL counterpart of `whir_listSize_ge_one`. -/
theorem SWIRLCfg.listSize_unique_le_list (c : SWIRLCfg) (lir : ℕ) (m : ℕ)
    (hsr : 0 < sqrtLB (swRho lir) swSqrtG) (hsr1 : sqrtLB (swRho lir) swSqrtG ≤ 1) :
    ({c with explicitM := none}).listSize lir
      ≤ ({c with explicitM := some m}).listSize lir := by
  simp only [SWIRLCfg.listSize]
  rw [le_div_iff₀ hsr, one_mul]
  have h1 : (1 : ℚ) ≤ ((max m 1 : ℕ) : ℚ) := by
    have hn : (1 : ℕ) ≤ max m 1 := le_max_right _ _
    exact_mod_cast hn
  linarith

/-! ## The four `ℓ`-linear cells

Each has the shape `coef · ℓ / |F|`, with `coef` built from `lSkip`, the AIR/trace bounds, the
LogUp parameters and `maxConstraintDegree` — none of which `explicitM` touches. -/

/-- **LogUp cell, monotone in the list size.** -/
theorem SWIRLCfg.logupErr_mono_listSize (c c' : SWIRLCfg)
    (hw : c'.whir = c.whir) (hlogup : c'.logup = c.logup)
    (h : c.initListSize ≤ c'.initListSize) :
    c.logupErr ≤ c'.logupErr := by
  simp only [SWIRLCfg.logupErr, SWIRLCfg.card, hw, hlogup]
  refine div_le_div_same ?_ c.card_pos
  refine mul_le_mul_of_nonneg_right ?_ (swEffpowFactor_nonneg c.whir.field c.logup.powBits)
  refine mul_le_mul_of_nonneg_left h ?_
  positivity

/-- **Zerocheck cell, monotone in the list size.** -/
theorem SWIRLCfg.zerocheckErr_mono_listSize (c c' : SWIRLCfg)
    (hw : c'.whir = c.whir) (hskip : c'.lSkip = c.lSkip)
    (h : c.initListSize ≤ c'.initListSize) :
    c.zerocheckErr ≤ c'.zerocheckErr := by
  simp only [SWIRLCfg.zerocheckErr, SWIRLCfg.card, SWIRLCfg.maxConstraintDegree, hw, hskip]
  refine div_le_div_same ?_ c.card_pos
  refine mul_le_mul_of_nonneg_left h ?_
  positivity

/-- **Constraint-batching cell, monotone in the list size.** -/
theorem SWIRLCfg.constraintBatchingErr_mono_listSize (c c' : SWIRLCfg)
    (hw : c'.whir = c.whir) (hskip : c'.lSkip = c.lSkip)
    (hairs : c'.airs = c.airs) (hint : c'.interactions = c.interactions)
    (hlth : c'.logTraceHeight = c.logTraceHeight) (hcon : c'.constraints = c.constraints)
    (hlogup : c'.logup = c.logup)
    (h : c.initListSize ≤ c'.initListSize) :
    c.constraintBatchingErr ≤ c'.constraintBatchingErr := by
  simp only [SWIRLCfg.constraintBatchingErr, SWIRLCfg.card, hw, hskip, hairs, hint, hlth, hcon,
    hlogup]
  refine div_le_div_same ?_ c.card_pos
  refine mul_le_mul_of_nonneg_left h ?_
  positivity

/-- **Stacked-reduction cell, monotone in the list size.** -/
theorem SWIRLCfg.stackedReductionErr_mono_listSize (c c' : SWIRLCfg)
    (hw : c'.whir = c.whir) (hskip : c'.lSkip = c.lSkip)
    (htc : c'.traceColumns = c.traceColumns)
    (h : c.initListSize ≤ c'.initListSize) :
    c.stackedReductionErr ≤ c'.stackedReductionErr := by
  simp only [SWIRLCfg.stackedReductionErr, SWIRLCfg.card, hw, hskip, htc]
  refine div_le_div_same ?_ c.card_pos
  refine mul_le_mul_of_nonneg_left h ?_
  positivity

/-! ## Lifting to the knobs

`initListSize = listSize logBlowup`, and `logBlowup = whir.logInvRate` is untouched by the
`explicitM` update, so every agreement hypothesis above is `rfl` and the list-size hypothesis
comes from the two `listSize` lemmas. -/

/-- **The multiplicity knob costs soundness on all four cells.** Raising `m` raises the list size,
which raises every `ℓ`-linear cell. -/
theorem SWIRLCfg.cells_mono_multiplicity (c : SWIRLCfg)
    (hsr : 0 < sqrtLB (swRho c.logBlowup) swSqrtG) {m m' : ℕ} (h : m ≤ m') :
    ({c with explicitM := some m}).logupErr ≤ ({c with explicitM := some m'}).logupErr ∧
    ({c with explicitM := some m}).zerocheckErr ≤ ({c with explicitM := some m'}).zerocheckErr ∧
    ({c with explicitM := some m}).constraintBatchingErr
      ≤ ({c with explicitM := some m'}).constraintBatchingErr ∧
    ({c with explicitM := some m}).stackedReductionErr
      ≤ ({c with explicitM := some m'}).stackedReductionErr := by
  have hl : ({c with explicitM := some m}).initListSize
      ≤ ({c with explicitM := some m'}).initListSize :=
    c.listSize_mono_multiplicity c.logBlowup hsr h
  exact ⟨logupErr_mono_listSize _ _ rfl rfl hl,
         zerocheckErr_mono_listSize _ _ rfl rfl hl,
         constraintBatchingErr_mono_listSize _ _ rfl rfl rfl rfl rfl rfl rfl hl,
         stackedReductionErr_mono_listSize _ _ rfl rfl rfl hl⟩

/-- **Unique decoding is at least as sound as list decoding on every `ℓ`-linear cell.** The
algebraic price of the list regime: `ℓ` jumps from `1` to `(m+½)/√ρ ≥ 1`, and all four cells scale
with it. (The query cell moves the other way — that is the tradeoff, and why the reported total
stays config-dependent.) -/
theorem SWIRLCfg.cells_unique_le_list (c : SWIRLCfg) (m : ℕ)
    (hsr : 0 < sqrtLB (swRho c.logBlowup) swSqrtG)
    (hsr1 : sqrtLB (swRho c.logBlowup) swSqrtG ≤ 1) :
    ({c with explicitM := none}).logupErr ≤ ({c with explicitM := some m}).logupErr ∧
    ({c with explicitM := none}).zerocheckErr ≤ ({c with explicitM := some m}).zerocheckErr ∧
    ({c with explicitM := none}).constraintBatchingErr
      ≤ ({c with explicitM := some m}).constraintBatchingErr ∧
    ({c with explicitM := none}).stackedReductionErr
      ≤ ({c with explicitM := some m}).stackedReductionErr := by
  have hl : ({c with explicitM := none}).initListSize
      ≤ ({c with explicitM := some m}).initListSize :=
    c.listSize_unique_le_list c.logBlowup m hsr hsr1
  exact ⟨logupErr_mono_listSize _ _ rfl rfl hl,
         zerocheckErr_mono_listSize _ _ rfl rfl hl,
         constraintBatchingErr_mono_listSize _ _ rfl rfl rfl rfl rfl rfl rfl hl,
         stackedReductionErr_mono_listSize _ _ rfl rfl rfl hl⟩

end Soundcalc
