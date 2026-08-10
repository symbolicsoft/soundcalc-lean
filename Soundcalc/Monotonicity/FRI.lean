import Soundcalc.Monotonicity.Basic
import Soundcalc.Monotonicity.Regime
import Soundcalc.PCS.FRI

/-!
# Monotonicity — FRI

Organised in two tiers:

* **Catalogue** (bottom of file) — the user-facing theorems, each in *configuration-knob* shape:
  fix a `FRIConfig`, move **one** field via a record update, and compare a single soundness cell.
  These are the rows of the sensitivity catalog. The record-update-safe knobs are `numQueries` and
  `batchSize`; `denseLen`, `ρ` and `foldingFactors` are pinned together by the config's
  `h_earlyStop` invariant, so they cannot be moved by `{c with …}` (their sensitivity is studied at
  the regime / `errPowers` level instead — see the foundations, and the follow-up rows). Every
  catalogue cell is **regime-independent**: it is stated for a bare `R : Regime`, with the algebraic
  ones carrying `Regime.Standard` (discharged by `UDR_standard` / `JBR_standard`).
* **Foundations** — the bare-parameter mechanisms the catalogue is built from: the query-cell shape
  and the folding-product / dimension lemmas. Not part of the catalogue; they are the proof toolkit.

This module covers soundness only. Proof *size* carries no monotonicity results: the expected-case
size counts Merkle nodes with an inclusion–exclusion sum that is **not** monotone in the number of
openings (it peaks and then falls, since opening more leaves makes more of the tree derivable), so
the natural statements are false as written rather than merely unproven.
-/

namespace Soundcalc

/-! # Foundations (proof toolkit)

Bare-parameter mechanisms — not part of the user catalogue. The configuration-knob theorems at the
bottom of the file are thin lifts of these. The query-count shape lemmas themselves live in
`Monotonicity.Basic` (`queryShape_antitone_numQueries` / `secBits_queryShape_mono_numQueries`),
applied here with `θ = θLB c.ρ c.denseLen`, `g = c.grindQuery`. -/

/-! ## Later rounds process smaller instances (the FRI analog of `WHIRConfig.logDegree_anti`)

`commitErr i` runs over the dimension `denseLen / ∏_{j≤i} kⱼ`, which shrinks each round. Composed with
`Regime.Standard.errLinear_mono_dim` (smaller instance ⇒ more sound, at any regime), this is why the
report's commit-round bits climb — see `commitDimErr_antitone_round` in the catalogue. -/

/-- The accumulated folding factor `∏_{j≤i} kⱼ` is non-decreasing in the round `i` (each `kⱼ ≥ 1`). -/
theorem friAcc_mono {folds : List ℕ} (hpos : ∀ k ∈ folds, 1 ≤ k) (i : ℕ) :
    (folds.take (i + 1)).foldl (· * ·) 1 ≤ (folds.take (i + 2)).foldl (· * ·) 1 := by
  simp only [← List.prod_eq_foldl]
  rcases lt_or_ge (i + 1) folds.length with hlt | hge
  · rw [List.prod_take_succ folds (i + 1) hlt]
    have hk : 1 ≤ folds[i + 1] := hpos _ (List.getElem_mem hlt)
    exact Nat.le_mul_of_pos_right _ (by omega)
  · rw [List.take_of_length_le hge, List.take_of_length_le (by omega)]

/-- **The folded dimension shrinks each round**: `denseLen / ∏_{j≤i+1} ≤ denseLen / ∏_{j≤i}`.
The FRI counterpart of WHIR's `logDegree_anti`; with `Regime.Standard.errLinear_mono_dim` it gives
that the commit-round soundness error decreases (security climbs) round over round, at any regime. -/
theorem friDimension_antitone (denseLen : ℕ) {folds : List ℕ} (hpos : ∀ k ∈ folds, 1 ≤ k) (i : ℕ) :
    denseLen / (folds.take (i + 2)).foldl (· * ·) 1
      ≤ denseLen / (folds.take (i + 1)).foldl (· * ·) 1 := by
  apply Nat.div_le_div_left (friAcc_mono hpos i)
  simp only [← List.prod_eq_foldl]
  exact List.prod_pos fun x hx => by have := hpos x (List.mem_of_mem_take hx); omega

/-! # Catalogue — configuration sensitivity

Config-level theorems a user reads directly. Two groups: **cross-regime** (how the query cell moves
when the *decoding regime* changes — the JBR-vs-UDR question) and **configuration knobs** (how a cell
moves when one *config field* changes). -/

/-! ## Cross-regime: a larger decoding radius buys query bits (mirrors `WHIRConfig.epsilonQuery_*`) -/

/-- The FRI query error `(1 - θLB)^t / 2^g` is **antitone in the decoding radius** `θLB`: a regime
`R'` whose lower-bound radius is at least `R`'s (on this config) has query error no larger. -/
theorem FRIConfig.queryErr_antitone_radius (c : FRIConfig) (R R' : Regime)
    (hle : R.θLB c.ρ c.denseLen ≤ R'.θLB c.ρ c.denseLen)
    (h1 : R'.θLB c.ρ c.denseLen ≤ 1) :
    c.queryErr R' ≤ c.queryErr R := by
  unfold FRIConfig.queryErr
  exact queryShape_antitone_radius hle h1 _ _

/-- On the **query cell**, a larger decoding radius never gives fewer security bits: if `R'` has
`θLB ≥ R`'s (and `< 1`, so the error is positive), then `secBits (queryErr R) ≤ secBits
(queryErr R')`. With `R = UDR`, `R' = JBR` this is "JBR ≥ UDR on the query cell" — and
`johnson_beats_unique` is why JBR's radius clears UDR's (for a small-enough gap). -/
theorem FRIConfig.queryBits_mono (c : FRIConfig) (R R' : Regime)
    (hle : R.θLB c.ρ c.denseLen ≤ R'.θLB c.ρ c.denseLen)
    (h1 : R'.θLB c.ρ c.denseLen < 1) :
    secBits (c.queryErr R) ≤ secBits (c.queryErr R') := by
  unfold FRIConfig.queryErr
  exact secBits_queryShape_mono_radius hle h1 _ _

/-! ## Configuration knobs

Each theorem fixes a `FRIConfig`, moves exactly one field (via `{c with … }`), and compares one
cell. The two record-update-safe knobs are `numQueries` and `batchSize`: more queries buy query-cell
security (error ↓, bits ↑), more batching costs batching-cell soundness (error ↑).

**Every cell here is regime-independent.** The query cells hold for a bare `R : Regime` (their shape
`(1−θ)^t/2^g` involves no regime formula beyond the radius); the algebraic cells hold for any `R`
satisfying `Regime.Standard c.field c.ρ`, discharged by `UDR_standard` or `JBR_standard`. There are
no `_udr`/`_jbr` variants to keep in sync — Airbender/OpenVM/Pico/ZisK report at JBR and read the
same theorems SP1 does. -/

/-- **Query knob → soundness (↓).** More queries never *raise* the query-cell error. -/
theorem FRIConfig.queryErr_antitone_numQueries (c : FRIConfig) (R : Regime) {q : ℕ}
    (h : c.numQueries ≤ q)
    (h0 : 0 ≤ R.θLB c.ρ c.denseLen) (h1 : R.θLB c.ρ c.denseLen ≤ 1) :
    ({c with numQueries := q}).queryErr R ≤ c.queryErr R := by
  unfold FRIConfig.queryErr
  exact queryShape_antitone_numQueries h0 h1 h c.grindQuery

/-- **Query knob → security (↑).** More queries never *lower* the query-cell security bits. -/
theorem FRIConfig.queryBits_mono_numQueries (c : FRIConfig) (R : Regime) {q : ℕ}
    (h : c.numQueries ≤ q)
    (h0 : 0 ≤ R.θLB c.ρ c.denseLen) (h1 : R.θLB c.ρ c.denseLen < 1) :
    secBits (c.queryErr R) ≤ secBits (({c with numQueries := q}).queryErr R) := by
  unfold FRIConfig.queryErr
  exact secBits_queryShape_mono_numQueries h0 h1 h c.grindQuery

/-- **Batch knob → soundness (↑).** Batching more polynomials never *lowers* the batching-cell error —
at **any** regime, on **either** batching path (`powerBatch` ⇒ `errPowers`, or the multilinear path
⇒ `errMultilinear`). -/
theorem FRIConfig.batchingErr_mono_batchSize (c : FRIConfig) (R : Regime)
    (hR : R.Standard c.field c.ρ) {b : ℕ} (h : c.batchSize ≤ b) :
    c.batchingErr R ≤ ({c with batchSize := b}).batchingErr R := by
  dsimp only [FRIConfig.batchingErr]
  split_ifs with hp
  · gcongr; exact hR.errPowers_mono_batch (by positivity) h
  · gcongr; exact hR.errMultilinear_mono_batch (by positivity) h

/-- **Query-grind knob → soundness (↓).** More query-phase PoW bits never raise the query-cell
error (`div_pow_two_antitone` on `(1 − θ)^numQueries`). -/
theorem FRIConfig.queryErr_antitone_grindQuery (c : FRIConfig) (R : Regime) {g : ℕ}
    (h : c.grindQuery ≤ g) (hb : 0 ≤ 1 - R.θLB c.ρ c.denseLen) :
    ({c with grindQuery := g}).queryErr R ≤ c.queryErr R := by
  unfold FRIConfig.queryErr
  exact div_pow_two_antitone (pow_nonneg hb _) h

/-- **Batch-grind knob → soundness (↓).** More batching-phase PoW bits never raise the batching-cell
error — at any regime, on **either** batching path (`errPowers` or `errMultilinear`). -/
theorem FRIConfig.batchingErr_antitone_grindBatch (c : FRIConfig) (R : Regime)
    (hR : R.Standard c.field c.ρ) (hbs : 1 ≤ c.batchSize) {g : ℕ} (h : c.grindBatch ≤ g) :
    ({c with grindBatch := g}).batchingErr R ≤ c.batchingErr R := by
  dsimp only [FRIConfig.batchingErr]
  split_ifs with hp
  · exact div_pow_two_antitone (hR.errPowers_nonneg (by positivity) hbs) h
  · exact div_pow_two_antitone (hR.errMultilinear_nonneg (by positivity) c.batchSize) h

/-- **Commit-grind knob → soundness (↓).** More commit-phase PoW bits never raise the per-round
commit-cell error `commitErr i = errPowers(ρ, denseLen/∏kⱼ, kᵢ) / 2^grindCommit`, at any regime. The
companion of `batchingErr_antitone_grindBatch` for the commit cell. -/
theorem FRIConfig.commitErr_antitone_grindCommit (c : FRIConfig) (R : Regime)
    (hR : R.Standard c.field c.ρ) (i : ℕ)
    (hf : 1 ≤ c.foldingFactors.getD i 1) {g : ℕ} (h : c.grindCommit ≤ g) :
    ({c with grindCommit := g}).commitErr R i ≤ c.commitErr R i := by
  dsimp only [FRIConfig.commitErr]
  exact div_pow_two_antitone (hR.errPowers_nonneg (by positivity) hf) h

/-! ### The `H` and `|F|` cells (regime-level, since `denseLen`/`field` are pinned)

`denseLen` and `field` cannot be moved by a single-field record update (`h_earlyStop` couples
`denseLen`/`ρ`/`foldingFactors`), so their directions are recorded on the cell's *shape*: both
batching paths are monotone in the dimension at any regime (`errPowers_mono_dim` /
`errMultilinear_mono_dim`) and antitone in `|F|` (`UDR_`/`JBR_err{Powers,Multilinear}_antitone_card`
— the `|F|` knob is the one cell that must name its regime, since changing `|F|` *is* changing
`UDR F` into `UDR F'`).

The commit cell's own `H` movement, round over round, is `friDimension_antitone` above composed with
`errPowers_mono_dim`: the folded dimension shrinks each round, so the commit-round error falls. -/

/-- **Later commit rounds are more sound, at any regime.** Composing `friDimension_antitone` (the
folded dimension shrinks) with `errPowers_mono_dim` (smaller instance ⇒ smaller error): the
commit-cell error at round `i+1`'s dimension is at most the one at round `i`'s. Stated on the
dimensions rather than on `commitErr i` itself because the cell's batch argument is the *round's*
folding factor `kᵢ`, which is not monotone in `i`. -/
theorem FRIConfig.commitDimErr_antitone_round (c : FRIConfig) (R : Regime)
    (hR : R.Standard c.field c.ρ) (hpos : ∀ k ∈ c.foldingFactors, 1 ≤ k) (i : ℕ)
    {b : ℕ} (hb : 1 ≤ b) :
    R.errPowers c.ρ ((c.denseLen / (c.foldingFactors.take (i + 2)).foldl (· * ·) 1 : ℕ) : ℚ) b
      ≤ R.errPowers c.ρ ((c.denseLen / (c.foldingFactors.take (i + 1)).foldl (· * ·) 1 : ℕ) : ℚ) b :=
  errPowers_mono_dim hR (by exact_mod_cast friDimension_antitone c.denseLen hpos i) hb

end Soundcalc
