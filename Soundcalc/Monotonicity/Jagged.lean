import Soundcalc.Monotonicity.Basic
import Soundcalc.Circuit.Jagged

/-!
# Monotonicity — Jagged circuit cells

`zerocheckErr = (C + (deg+2)·⌈log₂ H⌉) / |F|` and
`reduceErr = (⌈log₂ w⌉ + 2ℓ + 2(2ℓ+2)) / |F|` (`ℓ` from the dense PCS's trace/batch sizes).

`JaggedCfg` pins `field`/`densePCS`/`lookups` (its coherence invariants), but `traceLength`,
`traceWidth`, `numConstraints`, `airMaxDegree` are free record-update knobs.

* **Catalogue** — `zerocheckErr` in `numConstraints`/`airMaxDegree`/`traceLength ↑`, `reduceErr` in
  `traceWidth ↑`, and both cells' `|F|` column via two configs (field pinned by coherence).
* **Proof size** is intentionally omitted: `getJaggedProofSizeBits` is private and reads *only* the
  (pinned) dense PCS — `densePCS.proofSize{Exp,Worst}` plus a reduction term over
  `densePCS.traceLen`/`batchSize`. None of Jagged's own fields enter it, so it has no Jagged-level
  knob; it inherits the dense PCS's proof-size monotonicity (`FRIConfig`/`WHIRConfig`).
-/

namespace Soundcalc

/-! # Catalogue — configuration knobs -/

/-- **Zerocheck, constraint-count knob (↑).** More constraints ⇒ larger zerocheck error. -/
theorem JaggedCfg.zerocheckErr_mono_numConstraints (c : JaggedCfg) {C : ℕ}
    (h : c.numConstraints ≤ C) :
    c.zerocheckErr ≤ ({c with numConstraints := C}).zerocheckErr := by
  dsimp only [JaggedCfg.zerocheckErr]
  have hcard : (0 : ℚ) < (c.field.card : ℚ) := by exact_mod_cast c.field.card_pos
  have hC : (c.numConstraints : ℚ) ≤ (C : ℚ) := by exact_mod_cast h
  refine div_le_div_same ?_ hcard
  gcongr

/-- **Zerocheck, degree knob (↑).** A larger AIR degree ⇒ larger zerocheck error. -/
theorem JaggedCfg.zerocheckErr_mono_airMaxDegree (c : JaggedCfg) {d : ℕ}
    (h : c.airMaxDegree ≤ d) :
    c.zerocheckErr ≤ ({c with airMaxDegree := d}).zerocheckErr := by
  dsimp only [JaggedCfg.zerocheckErr]
  have hcard : (0 : ℚ) < (c.field.card : ℚ) := by exact_mod_cast c.field.card_pos
  have hd : (c.airMaxDegree : ℚ) ≤ (d : ℚ) := by exact_mod_cast h
  refine div_le_div_same ?_ hcard
  gcongr

/-- **Zerocheck, trace-length knob (↑).** A longer trace ⇒ larger zerocheck error (via `⌈log₂ H⌉`). -/
theorem JaggedCfg.zerocheckErr_mono_traceLength (c : JaggedCfg) {t : ℕ}
    (h : c.traceLength ≤ t) :
    c.zerocheckErr ≤ ({c with traceLength := t}).zerocheckErr := by
  dsimp only [JaggedCfg.zerocheckErr]
  have hcard : (0 : ℚ) < (c.field.card : ℚ) := by exact_mod_cast c.field.card_pos
  have hlog : (Nat.clog 2 c.traceLength : ℚ) ≤ (Nat.clog 2 t : ℚ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  refine div_le_div_same ?_ hcard
  gcongr

/-- **Reduce, trace-width knob (↑).** A wider trace ⇒ larger reduction error (via `⌈log₂ w⌉`). -/
theorem JaggedCfg.reduceErr_mono_traceWidth (c : JaggedCfg) {w : ℕ}
    (h : c.traceWidth ≤ w) :
    c.reduceErr ≤ ({c with traceWidth := w}).reduceErr := by
  dsimp only [JaggedCfg.reduceErr]
  have hcard : (0 : ℚ) < (c.field.card : ℚ) := by exact_mod_cast c.field.card_pos
  have hlog : (Nat.clog 2 c.traceWidth : ℚ) ≤ (Nat.clog 2 w : ℚ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  refine div_le_div_same ?_ hcard
  push_cast
  gcongr

/-! # The `|F|` column (field pinned by coherence, so compared over two configs)

`zerocheckErr`/`reduceErr` read only `field.card` (not `densePCS.field`), so the two configs must
agree on the cell's other inputs and may differ freely elsewhere to satisfy `h_densePCS_field`. -/

/-- **Zerocheck, `|F|` column (↓).** A larger field ⇒ smaller zerocheck error. -/
theorem JaggedCfg.zerocheckErr_antitone_card (c c' : JaggedCfg)
    (hnc : c'.numConstraints = c.numConstraints) (hdeg : c'.airMaxDegree = c.airMaxDegree)
    (htl : c'.traceLength = c.traceLength) (hcard : c.field.card ≤ c'.field.card) :
    c'.zerocheckErr ≤ c.zerocheckErr := by
  simp only [JaggedCfg.zerocheckErr, hnc, hdeg, htl]
  exact div_le_div_denom (by positivity) (by exact_mod_cast c.field.card_pos)
    (by exact_mod_cast hcard)

/-- **Reduce, `|F|` column (↓).** A larger field ⇒ smaller reduction error. -/
theorem JaggedCfg.reduceErr_antitone_card (c c' : JaggedCfg)
    (htl : c'.densePCS.traceLen = c.densePCS.traceLen)
    (hbs : c'.densePCS.batchSize = c.densePCS.batchSize)
    (htw : c'.traceWidth = c.traceWidth) (hcard : c.field.card ≤ c'.field.card) :
    c'.reduceErr ≤ c.reduceErr := by
  simp only [JaggedCfg.reduceErr, htl, hbs, htw]
  exact div_le_div_denom (by positivity) (by exact_mod_cast c.field.card_pos)
    (by exact_mod_cast hcard)

end Soundcalc
