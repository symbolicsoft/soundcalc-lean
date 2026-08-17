import Soundcalc.Monotonicity.Basic
import Soundcalc.Lookup

/-!
# Monotonicity — LogUp / GKR lookups

`LookupCfg.errUB = (baseError + gkrError) / 2^grindBitsLookup`, with
`baseError = numLookupsM · H · R / |F|` (`H = rowsL + rowsT`, `R = columnAggregFactor`) and
`gkrError` the multivariate GKR term. `LookupCfg` carries no coherence invariant, so every field is
a record-update knob.

* **Catalogue** — configuration-knob sensitivities backing the LogUp / GKR row of the sensitivity
  catalog: `grindBitsLookup ↓`, `field ↓` (`|F|`), the `H` knob `rowsT ↑`, and the batch knobs
  `numLookupsM` / `numColumnsS ↑`.
* **Foundations** — `log2UB_mono`, `columnAggregFactor_mono`, `gkrErrorUB` monotonicity, and the
  same-denominator / nonnegativity plumbing.
-/

namespace Soundcalc

/-! # Foundations (proof toolkit)

The division-monotonicity finishing steps (`div_le_div_same`, `div_le_div_denom`) are shared from
`Monotonicity.Basic`. -/

/-- `log2UB` is monotone in its argument (`clog₂` and `·^m` are). -/
theorem log2UB_mono {x x' : ℕ} (h : x ≤ x') (m : ℕ) : log2UB x m ≤ log2UB x' m := by
  unfold log2UB
  have hcl : (Nat.clog 2 (x ^ m) : ℚ) ≤ (Nat.clog 2 (x' ^ m) : ℚ) := by
    exact_mod_cast Nat.clog_mono_right 2 (Nat.pow_le_pow_left h m)
  gcongr

/-- The quadratic `t ↦ t·(3t+1)` (the GKR error numerator shape) is monotone for `t ≥ 0`. -/
private theorem quad_mono {x y : ℚ} (hx : 0 ≤ x) (h : x ≤ y) :
    x * (3 * x + 1) ≤ y * (3 * y + 1) := by
  nlinarith [h, hx, mul_nonneg (sub_nonneg.2 h) hx]

/-- `columnAggregFactor` is monotone in the column count `S`. -/
theorem columnAggregFactor_mono {S S' : ℕ} (h : S ≤ S') (ml : Bool) :
    columnAggregFactor S ml ≤ columnAggregFactor S' ml := by
  cases ml with
  | false => show (S : ℚ) ≤ (S' : ℚ); exact_mod_cast h
  | true =>
      show max (log2UB S 64) 1 ≤ max (log2UB S' 64) 1
      exact max_le_max (log2UB_mono h 64) le_rfl

/-- `columnAggregFactor` is nonnegative. -/
theorem columnAggregFactor_nonneg (S : ℕ) (ml : Bool) : 0 ≤ columnAggregFactor S ml := by
  cases ml with
  | false => show (0 : ℚ) ≤ (S : ℚ); positivity
  | true => show (0 : ℚ) ≤ max (log2UB S 64) 1; exact le_trans zero_le_one (le_max_right _ _)

/-- `gkrErrorUB` is monotone in the alphabet size. -/
theorem gkrErrorUB_mono_alphabet (F : FieldParams) {a a' : ℕ} (h : a ≤ a') (M : ℕ) :
    gkrErrorUB F a M ≤ gkrErrorUB F a' M := by
  simp only [gkrErrorUB]
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hnm : log2UB a 64 + log2UB M 64 ≤ log2UB a' 64 + log2UB M 64 := by
    have := log2UB_mono h 64; linarith
  have hnn : (0 : ℚ) ≤ log2UB a 64 + log2UB M 64 := by
    have := log2UB_nonneg a 64; have := log2UB_nonneg M 64; linarith
  apply div_le_div_same _ hc
  nlinarith [quad_mono hnn hnm]

/-- `gkrErrorUB` is monotone in the number of lookups. -/
theorem gkrErrorUB_mono_lookups (F : FieldParams) (a : ℕ) {M M' : ℕ} (h : M ≤ M') :
    gkrErrorUB F a M ≤ gkrErrorUB F a M' := by
  simp only [gkrErrorUB]
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hnm : log2UB a 64 + log2UB M 64 ≤ log2UB a 64 + log2UB M' 64 := by
    have := log2UB_mono h 64; linarith
  have hnn : (0 : ℚ) ≤ log2UB a 64 + log2UB M 64 := by
    have := log2UB_nonneg a 64; have := log2UB_nonneg M 64; linarith
  apply div_le_div_same _ hc
  nlinarith [quad_mono hnn hnm]

/-- `gkrErrorUB` is antitone in the field size. -/
theorem gkrErrorUB_antitone_card {F F' : FieldParams} (hcard : F.card ≤ F'.card) (a M : ℕ) :
    gkrErrorUB F' a M ≤ gkrErrorUB F a M := by
  simp only [gkrErrorUB]
  have hF : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have hcQ : (F.card : ℚ) ≤ (F'.card : ℚ) := by exact_mod_cast hcard
  have hnn : (0 : ℚ) ≤
      1 / 2 * (log2UB a 64 + log2UB M 64) * (3 * (log2UB a 64 + log2UB M 64) + 1) := by
    have := log2UB_nonneg a 64; have := log2UB_nonneg M 64; positivity
  exact div_le_div_denom hnn hF hcQ

/-- `gkrErrorUB` is nonnegative. -/
theorem gkrErrorUB_nonneg (F : FieldParams) (a M : ℕ) : 0 ≤ gkrErrorUB F a M := by
  simp only [gkrErrorUB]
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  have := log2UB_nonneg a 64; have := log2UB_nonneg M 64
  positivity

/-! # Catalogue — configuration knobs

`LookupCfg` has no coherence invariant, so each field is a record-update knob. The `field` knob
compares two configs differing only in the field (the `|F|` column). -/

/-- **Grind knob → soundness (↓).** More lookup-phase PoW bits never raise the lookup error
(needs a nonnegative auxiliary `reductionErr`). -/
theorem LookupCfg.errUB_antitone_grindBitsLookup (c : LookupCfg) (hre : 0 ≤ c.reductionErr)
    {g : ℕ} (h : c.grindBitsLookup ≤ g) :
    ({c with grindBitsLookup := g}).errUB ≤ c.errUB := by
  dsimp only [LookupCfg.errUB]
  refine div_pow_two_antitone (add_nonneg ?_ ?_) h
  · exact div_nonneg (mul_nonneg (by positivity) (columnAggregFactor_nonneg _ _))
      (by positivity)
  · split_ifs with hm
    · exact add_nonneg (gkrErrorUB_nonneg _ _ _) hre
    · exact le_rfl

/-- **Field knob → soundness (↓).** A larger field never raises the lookup error (`|F|` column). -/
theorem LookupCfg.errUB_antitone_card (c : LookupCfg) {F' : FieldParams}
    (hcard : c.field.card ≤ F'.card) :
    ({c with field := F'}).errUB ≤ c.errUB := by
  dsimp only [LookupCfg.errUB]
  have hc : (0 : ℚ) < (c.field.card : ℚ) := by exact_mod_cast c.field.card_pos
  have hcQ : (c.field.card : ℚ) ≤ (F'.card : ℚ) := by exact_mod_cast hcard
  refine div_le_div_same (add_le_add ?_ ?_) (by positivity)
  · exact div_le_div_denom (mul_nonneg (by positivity) (columnAggregFactor_nonneg _ _)) hc hcQ
  · split_ifs with hm
    · exact add_le_add (gkrErrorUB_antitone_card hcard (c.rowsL + c.rowsT) c.numLookupsM) le_rfl
    · exact le_rfl

/-- **Table-size knob → soundness (↑).** More table rows never lower the lookup error (`H` column;
`H = rowsL + rowsT`). -/
theorem LookupCfg.errUB_mono_rowsT (c : LookupCfg) {t : ℕ} (h : c.rowsT ≤ t) :
    c.errUB ≤ ({c with rowsT := t}).errUB := by
  dsimp only [LookupCfg.errUB]
  have hH : c.rowsL + c.rowsT ≤ c.rowsL + t := by omega
  refine div_le_div_same (add_le_add ?_ ?_) (by positivity)
  · exact div_le_div_same
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hH) (by positivity))
        (columnAggregFactor_nonneg _ _))
      (by exact_mod_cast c.field.card_pos)
  · split_ifs with hm
    · exact add_le_add (gkrErrorUB_mono_alphabet c.field hH c.numLookupsM) le_rfl
    · exact le_rfl

/-- **Small-table knob → soundness (↑).** The other half of `H`: more `rowsL` rows never lower the
lookup error (mirror of `errUB_mono_rowsT`). -/
theorem LookupCfg.errUB_mono_rowsL (c : LookupCfg) {l : ℕ} (h : c.rowsL ≤ l) :
    c.errUB ≤ ({c with rowsL := l}).errUB := by
  dsimp only [LookupCfg.errUB]
  have hH : c.rowsL + c.rowsT ≤ l + c.rowsT := by omega
  refine div_le_div_same (add_le_add ?_ ?_) (by positivity)
  · exact div_le_div_same
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hH) (by positivity))
        (columnAggregFactor_nonneg _ _))
      (by exact_mod_cast c.field.card_pos)
  · split_ifs with hm
    · exact add_le_add (gkrErrorUB_mono_alphabet c.field hH c.numLookupsM) le_rfl
    · exact le_rfl

/-- **Lookup-count knob → soundness (↑).** More lookups never lower the lookup error (batch). -/
theorem LookupCfg.errUB_mono_numLookupsM (c : LookupCfg) {M : ℕ} (h : c.numLookupsM ≤ M) :
    c.errUB ≤ ({c with numLookupsM := M}).errUB := by
  dsimp only [LookupCfg.errUB]
  refine div_le_div_same (add_le_add ?_ ?_) (by positivity)
  · exact div_le_div_same
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity))
        (columnAggregFactor_nonneg _ _))
      (by exact_mod_cast c.field.card_pos)
  · split_ifs with hm
    · exact add_le_add (gkrErrorUB_mono_lookups c.field (c.rowsL + c.rowsT) h) le_rfl
    · exact le_rfl

/-- **Column-count knob → soundness (↑).** More columns never lower the lookup error (batch, via the
column-aggregation factor `R`; the GKR term is `S`-independent). -/
theorem LookupCfg.errUB_mono_numColumnsS (c : LookupCfg) {S : ℕ} (h : c.numColumnsS ≤ S) :
    c.errUB ≤ ({c with numColumnsS := S}).errUB := by
  dsimp only [LookupCfg.errUB]
  refine div_le_div_same (add_le_add ?_ le_rfl) (by positivity)
  exact div_le_div_same
    (mul_le_mul_of_nonneg_left (columnAggregFactor_mono h _) (by positivity))
    (by exact_mod_cast c.field.card_pos)

/-- **Auxiliary-error knob → soundness (↑).** A larger `reductionErr` never lowers the lookup error
(it is added on top in the multivariate GKR branch; the univariate branch ignores it). -/
theorem LookupCfg.errUB_mono_reductionErr (c : LookupCfg) {r : ℚ} (h : c.reductionErr ≤ r) :
    c.errUB ≤ ({c with reductionErr := r}).errUB := by
  dsimp only [LookupCfg.errUB]
  refine div_le_div_same (add_le_add le_rfl ?_) (by positivity)
  split_ifs with hm
  · linarith
  · exact le_rfl

end Soundcalc
