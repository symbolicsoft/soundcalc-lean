import Soundcalc.Monotonicity.Basic
import Soundcalc.Monotonicity.Regime
import Soundcalc.PCS.FRI

/-!
# Monotonicity — FRI

Organised in two tiers:

* **Catalogue** (bottom of file) — the user-facing theorems, each in *configuration-knob* shape:
  fix a `FRIConfig`, move **one** field via a record update, and compare a single cell (soundness
  error, security bits, or proof size). These are the rows of the sensitivity catalog. The
  record-update-safe knobs are `numQueries` and `batchSize`; `denseLen`, `ρ` and `foldingFactors`
  are pinned together by the config's `h_earlyStop` invariant, so they cannot be moved by `{c with …}`
  (their sensitivity is studied at the regime / `errPowers` level instead — see the foundations, and
  the follow-up rows). Every catalogue cell is **regime-independent**: it is stated for a bare
  `R : Regime`, with the algebraic ones carrying `Regime.Standard` (discharged by `UDR_standard` /
  `JBR_standard`).
* **Foundations** — the bare-parameter mechanisms the catalogue is built from: the query-cell shape,
  the Merkle proof-size atoms, the proof-size `foldl` monotonicity, and the folding-product /
  dimension lemmas. Not part of the catalogue; they are the proof toolkit.

Proof-size results are worst case (`expected = false`) except the `batchSize` knob, which is proven
for **both** `expected` values (`proofSizeExp_mono_batchSize`) since `batchSize` only scales the
initial multi-proof's leaves. The `numQueries` knob for `expected = true` is still open — it needs
monotonicity of the `numHashes` inclusion–exclusion sum in the number of openings.
-/

namespace Soundcalc

/-! # Foundations (proof toolkit)

Bare-parameter mechanisms — not part of the user catalogue. The configuration-knob theorems at the
bottom of the file are thin lifts of these. The query-count shape lemmas themselves live in
`Monotonicity.Basic` (`queryShape_antitone_numQueries` / `secBits_queryShape_mono_numQueries`),
applied here with `θ = θLB c.ρ c.denseLen`, `g = c.grindQuery`. -/

/-! ## Proof size: folding leaves and queries both cost more (worst case) -/

/-- A single Merkle path is monotone in the folding-block (leaf) size `tupleSize`: a bigger
folding factor makes each opening larger — the *cost* side of the folding-factor tradeoff (the
*benefit* is fewer rounds). -/
theorem getSizeOfMerkleProofBits_mono_tupleSize (numLeafs elemBits hashBits : ℕ) {t t' : ℕ}
    (h : t ≤ t') :
    getSizeOfMerkleProofBits numLeafs t elemBits hashBits
      ≤ getSizeOfMerkleProofBits numLeafs t' elemBits hashBits := by
  unfold getSizeOfMerkleProofBits
  have h1 : t * elemBits ≤ t' * elemBits := by gcongr
  exact Nat.add_le_add (Nat.add_le_add h1 (min_le_min h1 le_rfl)) le_rfl

/-- The worst-case Merkle multi-proof (`expected = false`) is monotone in the number of
openings/queries: `numOpenings · perProof`. This is the atom behind "more queries ⇒ bigger FRI
proof." -/
theorem getSizeOfMerkleMultiProofBits_worst_mono_numOpenings
    (numLeafs tupleSize elemBits hashBits : ℕ) {q q' : ℕ} (h : q ≤ q') :
    getSizeOfMerkleMultiProofBits numLeafs q tupleSize elemBits hashBits false
      ≤ getSizeOfMerkleMultiProofBits numLeafs q' tupleSize elemBits hashBits false := by
  unfold getSizeOfMerkleMultiProofBits
  simp only [Bool.false_eq_true, if_false]
  gcongr

/-- The FRI proof-size `foldl` (worst case), threading `(bits, domain)`: raising `numQueries`
never lowers the accumulated bits, and the domain thread is query-independent (so it is shared).
The joint statement is what makes the induction go through. -/
theorem friFold_mono (hashBits fieldBits : ℕ) {q q' : ℕ} (hq : q ≤ q') (l : List ℕ) :
    ∀ (b b' n : ℕ), b ≤ b' →
      (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) q factor fieldBits hashBits false,
           acc.2 / factor)) (b, n)).1
        ≤ (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) q' factor fieldBits hashBits false,
           acc.2 / factor)) (b', n)).1
      ∧ (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) q factor fieldBits hashBits false,
           acc.2 / factor)) (b, n)).2
        = (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) q' factor fieldBits hashBits false,
           acc.2 / factor)) (b', n)).2 := by
  induction l with
  | nil => intro b b' n hb; exact ⟨hb, rfl⟩
  | cons factor l' ih =>
    intro b b' n hb
    simp only [List.foldl_cons]
    apply ih
    have hm := getSizeOfMerkleMultiProofBits_worst_mono_numOpenings (n / factor) factor fieldBits hashBits hq
    omega

/-- The proof-size `foldl` is monotone in the **starting bits** for a *fixed* `numQueries` and any
`expected`: every round adds the same amount to both threads (it depends only on the shared domain
`acc.2`), so a larger initial value stays larger and the domain thread is identical. This is the
`batchSize`-knob analogue of `friFold_mono` — it needs no per-round monotonicity, so it holds for the
`expected = true` amortized count too. -/
theorem friFold_mono_init (hashBits fieldBits numQueries : ℕ) (expected : Bool) (l : List ℕ) :
    ∀ (b b' n : ℕ), b ≤ b' →
      (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) numQueries factor fieldBits hashBits expected,
           acc.2 / factor)) (b, n)).1
        ≤ (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) numQueries factor fieldBits hashBits expected,
           acc.2 / factor)) (b', n)).1
      ∧ (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) numQueries factor fieldBits hashBits expected,
           acc.2 / factor)) (b, n)).2
        = (l.foldl (fun (acc : ℕ × ℕ) factor =>
          (acc.1 + hashBits + getSizeOfMerkleMultiProofBits (acc.2 / factor) numQueries factor fieldBits hashBits expected,
           acc.2 / factor)) (b', n)).2 := by
  induction l with
  | nil => intro b b' n hb; exact ⟨hb, rfl⟩
  | cons factor l' ih =>
    intro b b' n hb
    simp only [List.foldl_cons]
    apply ih
    omega

/-- The Merkle multi-proof is monotone in the folding-block (leaf) size `tupleSize` for **either**
`expected` value: worst case scales the per-opening path, and the expected case scales `leafsSize`
(`numOpenings·tupleSize·elemBits`) while the hash-count term is `tupleSize`-independent. -/
theorem getSizeOfMerkleMultiProofBits_mono_tupleSize
    (numLeafs numOpenings elemBits hashBits : ℕ) (expected : Bool) {t t' : ℕ} (h : t ≤ t') :
    getSizeOfMerkleMultiProofBits numLeafs numOpenings t elemBits hashBits expected
      ≤ getSizeOfMerkleMultiProofBits numLeafs numOpenings t' elemBits hashBits expected := by
  unfold getSizeOfMerkleMultiProofBits
  cases expected with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    gcongr
    exact getSizeOfMerkleProofBits_mono_tupleSize numLeafs elemBits hashBits h
  | true =>
    simp only [if_true, getSizeOfMerkleMultiProofBitsExpected]
    gcongr

/-- **No free lunch (worst case).** The FRI proof size is monotone in `numQueries`: every extra
query enlarges the proof. Paired with `secBits_query_mono_numQueries` (more queries ⇒ more
security), this is the formal statement that query-security is *bought* with proof size. -/
theorem getFRIProofSizeBits_mono_numQueries (hashBits fieldBits batchSize domainSize : ℕ)
    (folds : List ℕ) (rate : ℚ) {q q' : ℕ} (hq : q ≤ q') :
    getFRIProofSizeBits hashBits fieldBits batchSize q domainSize folds rate false
      ≤ getFRIProofSizeBits hashBits fieldBits batchSize q' domainSize folds rate false := by
  unfold getFRIProofSizeBits
  have hinit : hashBits + getSizeOfMerkleMultiProofBits domainSize q batchSize fieldBits hashBits false
      ≤ hashBits + getSizeOfMerkleMultiProofBits domainSize q' batchSize fieldBits hashBits false := by
    have := getSizeOfMerkleMultiProofBits_worst_mono_numOpenings domainSize batchSize fieldBits hashBits hq
    omega
  obtain ⟨hbits, hfin⟩ := friFold_mono hashBits fieldBits hq folds _ _ domainSize hinit
  exact Nat.add_le_add hbits (Nat.le_of_eq (by rw [hfin]))

/-! ## Batching tradeoff: more batched polynomials cost soundness *and* proof size

The soundness side (`Regime.Standard.errPowers_mono_batch`, regime-independent) lives with the other
`errPowers` monotonicities in `Monotonicity.Regime`; the proof-size side is below. -/

/-- The worst-case Merkle multi-proof is monotone in the folding-block (leaf) size `tupleSize`. -/
theorem getSizeOfMerkleMultiProofBits_worst_mono_tupleSize
    (numLeafs numOpenings elemBits hashBits : ℕ) {t t' : ℕ} (h : t ≤ t') :
    getSizeOfMerkleMultiProofBits numLeafs numOpenings t elemBits hashBits false
      ≤ getSizeOfMerkleMultiProofBits numLeafs numOpenings t' elemBits hashBits false := by
  unfold getSizeOfMerkleMultiProofBits
  simp only [Bool.false_eq_true, if_false]
  gcongr
  exact getSizeOfMerkleProofBits_mono_tupleSize numLeafs elemBits hashBits h

/-- **Batching proof-size cost — worst *and* expected.** The FRI proof size is monotone in
`batchSize` for **either** `expected` value: the batched polynomials all ride in the *initial* Merkle
multi-proof (`tupleSize = batchSize`), and the fold rounds don't see `batchSize`, so `friFold_mono_init`
(no per-round monotonicity needed) carries the initial difference through — even for the harder
`expected = true` amortized count. -/
theorem getFRIProofSizeBits_mono_batchSize (hashBits fieldBits numQueries domainSize : ℕ)
    (folds : List ℕ) (rate : ℚ) (expected : Bool) {b b' : ℕ} (hb : b ≤ b') :
    getFRIProofSizeBits hashBits fieldBits b numQueries domainSize folds rate expected
      ≤ getFRIProofSizeBits hashBits fieldBits b' numQueries domainSize folds rate expected := by
  unfold getFRIProofSizeBits
  have hinit : hashBits + getSizeOfMerkleMultiProofBits domainSize numQueries b fieldBits hashBits expected
      ≤ hashBits + getSizeOfMerkleMultiProofBits domainSize numQueries b' fieldBits hashBits expected := by
    have := getSizeOfMerkleMultiProofBits_mono_tupleSize domainSize numQueries fieldBits hashBits expected hb
    omega
  obtain ⟨hbits, hfin⟩ := friFold_mono_init hashBits fieldBits numQueries expected folds _ _ domainSize hinit
  exact Nat.add_le_add hbits (Nat.le_of_eq (by rw [hfin]))

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
cell. The two record-update-safe knobs are `numQueries` and `batchSize`. Together the `numQueries`
trio (error ↓, security ↑, size ↑) and the `batchSize` pair (error ↑, size ↑) are the "no free
lunch" story at the config level.

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

/-- **Query knob → security (↑).** More queries never *lower* the query-cell security bits — the
benefit side of the no-free-lunch pair with `proofSizeWorst_mono_numQueries`. -/
theorem FRIConfig.queryBits_mono_numQueries (c : FRIConfig) (R : Regime) {q : ℕ}
    (h : c.numQueries ≤ q)
    (h0 : 0 ≤ R.θLB c.ρ c.denseLen) (h1 : R.θLB c.ρ c.denseLen < 1) :
    secBits (c.queryErr R) ≤ secBits (({c with numQueries := q}).queryErr R) := by
  unfold FRIConfig.queryErr
  exact secBits_queryShape_mono_numQueries h0 h1 h c.grindQuery

/-- **Query knob → proof size (↑).** More queries never *shrink* the (worst-case) proof — the cost
side of the no-free-lunch pair. -/
theorem FRIConfig.proofSizeWorst_mono_numQueries (c : FRIConfig) {q : ℕ}
    (h : c.numQueries ≤ q) :
    c.proofSizeWorst ≤ ({c with numQueries := q}).proofSizeWorst := by
  simp only [FRIConfig.proofSizeWorst]
  exact getFRIProofSizeBits_mono_numQueries _ _ _ _ _ _ h

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

/-- **Batch knob → proof size (↑).** The batched polynomials all ride the initial Merkle
multi-proof, so batching more of them never *shrinks* the proof. -/
theorem FRIConfig.proofSizeWorst_mono_batchSize (c : FRIConfig) {b : ℕ}
    (h : c.batchSize ≤ b) :
    c.proofSizeWorst ≤ ({c with batchSize := b}).proofSizeWorst := by
  simp only [FRIConfig.proofSizeWorst]
  exact getFRIProofSizeBits_mono_batchSize _ _ _ _ _ _ _ h

/-- **Batch knob → expected proof size (↑).** The amortized (`expected = true`) FRI proof size is
also monotone in `batchSize`: `batchSize` only scales the initial multi-proof's leaves, which the
expected-size formula counts linearly. The `numQueries` direction for `expected = true` is *not*
covered here — it needs monotonicity of the `numHashes` inclusion–exclusion sum in the number of
openings. -/
theorem FRIConfig.proofSizeExp_mono_batchSize (c : FRIConfig) {b : ℕ}
    (h : c.batchSize ≤ b) :
    c.proofSizeExp ≤ ({c with batchSize := b}).proofSizeExp := by
  simp only [FRIConfig.proofSizeExp]
  exact getFRIProofSizeBits_mono_batchSize _ _ _ _ _ _ _ h

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
