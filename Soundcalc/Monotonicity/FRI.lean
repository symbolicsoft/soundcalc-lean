import Soundcalc.Monotonicity.Basic
import Soundcalc.PCS.FRI

/-!
# Monotonicity — FRI

* **Radius → query bits.** `queryErr` is antitone in the decoding radius `θLB`, so (via
  `secBits_anti`) a larger radius never gives fewer query bits (`queryBits_mono`). With `johnson_beats_unique`
  this is "JBR ≥ UDR on the query cell."
* **Queries → security and proof size (no free lunch).** More queries never reduce query-cell
  security (`secBits_query_mono_numQueries`) but also always enlarge the (worst-case) proof
  (`getFRIProofSizeBits_mono_numQueries`).
* **Folding-leaf cost.** A bigger folding factor makes each Merkle opening larger
  (`getSizeOfMerkleProofBits_mono_tupleSize`).

Proof-size results are for the worst case (`expected = false`); the `expected = true` amortized
hash count has a much harder monotonicity and is left.
-/

namespace Soundcalc

/-! ## Decoding radius buys query bits (mirrors `WHIRConfig.epsilonQuery_*`)

The query-count monotonicity is proof-system-agnostic and lives in `Monotonicity.Basic`
(`queryShape_antitone_numQueries` / `secBits_queryShape_mono_numQueries`); apply it with
`θ = θLB c.ρ c.denseLen`, `g = c.grindQuery`. -/

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

/-! ## Batching tradeoff: more batched polynomials cost soundness *and* proof size -/

/-- **Batching soundness cost.** The powers-batching error `errPowers = errLinear·(batch − 1)` is
monotone in `batchSize`: batching more polynomials weakens the batching cell. -/
theorem UDR_errPowers_mono_batch (F : FieldParams) (ρ : Rate) (d : ℕ) {b b' : ℕ} (h : b ≤ b') :
    (UDR F).errPowers ρ d b ≤ (UDR F).errPowers ρ d b' := by
  obtain ⟨r, hr0, hr1⟩ := ρ
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast F.card_pos
  simp only [UDR]
  have hnum : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) + 1 := by
    have : (0 : ℚ) ≤ (1 - r) / 2 * ((d : ℚ) / r) := mul_nonneg (by linarith) (by positivity)
    linarith
  have hbase : (0 : ℚ) ≤ ((1 - r) / 2 * ((d : ℚ) / r) + 1) / (F.card : ℚ) := div_nonneg hnum hc.le
  have hbb : ((b : ℚ) - 1) ≤ ((b' : ℚ) - 1) := by
    have : (b : ℚ) ≤ (b' : ℚ) := by exact_mod_cast h
    linarith
  gcongr

/-- The worst-case Merkle multi-proof is monotone in the folding-block (leaf) size `tupleSize`. -/
theorem getSizeOfMerkleMultiProofBits_worst_mono_tupleSize
    (numLeafs numOpenings elemBits hashBits : ℕ) {t t' : ℕ} (h : t ≤ t') :
    getSizeOfMerkleMultiProofBits numLeafs numOpenings t elemBits hashBits false
      ≤ getSizeOfMerkleMultiProofBits numLeafs numOpenings t' elemBits hashBits false := by
  unfold getSizeOfMerkleMultiProofBits
  simp only [Bool.false_eq_true, if_false]
  gcongr
  exact getSizeOfMerkleProofBits_mono_tupleSize numLeafs elemBits hashBits h

/-- **Batching proof-size cost.** The FRI proof size is monotone in `batchSize`: the batched
polynomials all ride in the *initial* Merkle multi-proof (`tupleSize = batchSize`), so batching
more of them enlarges the proof. (The fold rounds don't see `batchSize`, so `friFold_mono` with the
same `numQueries` on both sides carries it through.) -/
theorem getFRIProofSizeBits_mono_batchSize (hashBits fieldBits numQueries domainSize : ℕ)
    (folds : List ℕ) (rate : ℚ) {b b' : ℕ} (hb : b ≤ b') :
    getFRIProofSizeBits hashBits fieldBits b numQueries domainSize folds rate false
      ≤ getFRIProofSizeBits hashBits fieldBits b' numQueries domainSize folds rate false := by
  unfold getFRIProofSizeBits
  have hinit : hashBits + getSizeOfMerkleMultiProofBits domainSize numQueries b fieldBits hashBits false
      ≤ hashBits + getSizeOfMerkleMultiProofBits domainSize numQueries b' fieldBits hashBits false := by
    have := getSizeOfMerkleMultiProofBits_worst_mono_tupleSize domainSize numQueries fieldBits hashBits hb
    omega
  obtain ⟨hbits, hfin⟩ := friFold_mono hashBits fieldBits (le_refl numQueries) folds _ _ domainSize hinit
  exact Nat.add_le_add hbits (Nat.le_of_eq (by rw [hfin]))

/-! ## Later rounds process smaller instances (the FRI analog of `WHIRConfig.logDegree_anti`)

`commitErr i` runs over the dimension `denseLen / ∏_{j≤i} kⱼ`, which shrinks each round. Composed with
`UDR_errLinear_mono_dim` (smaller instance ⇒ more sound), this is why the report's commit-round bits
climb. -/

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
The FRI counterpart of WHIR's `logDegree_anti`; with `UDR_errLinear_mono_dim` it gives that the
commit-round soundness error decreases (security climbs) round over round. -/
theorem friDimension_antitone (denseLen : ℕ) {folds : List ℕ} (hpos : ∀ k ∈ folds, 1 ≤ k) (i : ℕ) :
    denseLen / (folds.take (i + 2)).foldl (· * ·) 1
      ≤ denseLen / (folds.take (i + 1)).foldl (· * ·) 1 := by
  apply Nat.div_le_div_left (friAcc_mono hpos i)
  simp only [← List.prod_eq_foldl]
  exact List.prod_pos fun x hx => by have := hpos x (List.mem_of_mem_take hx); omega

end Soundcalc
