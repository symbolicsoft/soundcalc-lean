import Soundcalc.ZkVM.SP1
import Soundcalc.Monotonicity.FRI

/-!
# `Soundcalc.Monotonicity.SP1` — what the catalogue buys on a deployed circuit

Point theorems fix values; the catalogue fixes directions. Composing the two
gives statements that quantify over a parameter, which no number of
calculator runs can establish. Two examples on SP1 core:

* **Minimality.** `numQueries = 124` is the least query count at which the
  FRI query cell reaches 100 bits (`sp1Core_queries_minimal`): the cell is
  100 bits at 124, 99 bits at 123, and `queryBits_mono_numQueries` carries
  the 123 evaluation down to every smaller count.
* **Ceiling.** No query count takes SP1 core's total above 100 bits
  (`sp1Core_total_le_100`): the lookup cell is 100 bits and does not
  mention the query count, and the total is the `min` over cells.

Both are kernel-checked except for the point evaluations they rest on (the
query cell at 123 and 124 queries, and the lookup cell), each discharged by
`native_decide`.
-/

namespace Soundcalc

/-! ## Order facts about the Jagged total -/

/-- Every element of a list is at most its `foldr max 0`. -/
theorem le_foldr_max {l : List ℚ} {x : ℚ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- `foldl (· ++ [g ·])` is `append` of the `map`. -/
theorem foldl_append_singleton {α β : Type*} (g : α → β) :
    ∀ (l : List α) (init : List β),
      l.foldl (fun acc x => acc ++ [g x]) init = init ++ l.map g
  | [], init => by simp
  | a :: l, init => by
    rw [List.foldl_cons, foldl_append_singleton g l, List.map_cons, List.append_assoc,
      List.singleton_append]

/-- The error list of a Jagged circuit, as an explicit append rather than a `do` block. -/
theorem JaggedCfg.listErrs_eq (c : JaggedCfg) :
    c.listErrs = [c.reduceErr, c.zerocheckErr] ++ c.densePCS.listErrs (UDR c.field)
      ++ c.lookups.map (·.errUB) := by
  unfold JaggedCfg.listErrs
  simp only [map_pure, List.forIn_pure_yield_eq_foldl, bind_pure_comp]
  rw [foldl_append_singleton]
  simp

/-- Every listed error is at most the Jagged total. -/
theorem JaggedCfg.le_totalErr (c : JaggedCfg) {x : ℚ} (hx : x ∈ c.listErrs) :
    x ≤ c.totalErr :=
  le_foldr_max hx

/-- A lookup's error is at most the total of the circuit it belongs to. -/
theorem JaggedCfg.lookup_le_totalErr (c : JaggedCfg) {l : LookupCfg} (hl : l ∈ c.lookups) :
    l.errUB ≤ c.totalErr := by
  apply c.le_totalErr
  rw [JaggedCfg.listErrs_eq]
  exact List.mem_append_right _ (List.mem_map_of_mem hl)

/-! ## SP1 core with the query count as a free parameter -/

/-- SP1 core's FRI configuration with the query count replaced by `q`. -/
def sp1CoreFRIq (q : ℕ) : FRIConfig := { sp1CoreFRI with numQueries := q }

/-- SP1 core with the query count replaced by `q`; every other parameter pinned. -/
def sp1CoreJaggedq (q : ℕ) : JaggedCfg :=
  { sp1CoreJagged with densePCS := .fri (sp1CoreFRIq q), h_densePCS_field := rfl }

theorem sp1CoreFRIq_124 : sp1CoreFRIq 124 = sp1CoreFRI := rfl
theorem sp1CoreJaggedq_124 : sp1CoreJaggedq 124 = sp1CoreJagged := rfl
theorem sp1CoreJaggedq_lookups (q : ℕ) : (sp1CoreJaggedq q).lookups = [sp1CoreLookup] := rfl

/-! ## The three point evaluations -/

/-- The query cell at the deployed count: 100 bits. -/
theorem sp1Core_queryBits_124 :
    secBits ((sp1CoreFRIq 124).queryErr (UDR koalaBear4)) = 100 := by native_decide

/-- One query fewer: 99 bits. -/
theorem sp1Core_queryBits_123 :
    secBits ((sp1CoreFRIq 123).queryErr (UDR koalaBear4)) = 99 := by native_decide

/-- The lookup cell is `sp1_core_lookup_bits` (`Soundcalc/ZkVM/SP1.lean`): 100 bits,
independent of the query count. Its error is positive: -/
theorem sp1Core_lookupErr_pos : 0 < sp1CoreLookup.errUB := by native_decide

/-! ## Minimality -/

/-- The UDR radius for SP1 core is `3/8`, so the catalogue's side conditions hold. -/
theorem sp1Core_θLB_bounds :
    0 ≤ (UDR koalaBear4).θLB sp1CoreFRI.ρ sp1CoreFRI.denseLen ∧
    (UDR koalaBear4).θLB sp1CoreFRI.ρ sp1CoreFRI.denseLen < 1 := by
  simp only [UDR, sp1CoreFRI, Rate.quarter]
  norm_num

/-- **Minimality.** 124 is the least query count at which SP1 core's query cell
reaches 100 bits. -/
theorem sp1Core_queries_minimal :
    secBits ((sp1CoreFRIq 124).queryErr (UDR koalaBear4)) = 100 ∧
    ∀ q < 124, secBits ((sp1CoreFRIq q).queryErr (UDR koalaBear4)) < 100 := by
  refine ⟨sp1Core_queryBits_124, ?_⟩
  intro q hq
  have hmono := FRIConfig.queryBits_mono_numQueries (sp1CoreFRIq q) (UDR koalaBear4)
    (q := 123) (by show q ≤ 123; omega) sp1Core_θLB_bounds.1 sp1Core_θLB_bounds.2
  have h123 : ({ sp1CoreFRIq q with numQueries := 123 } : FRIConfig) = sp1CoreFRIq 123 := rfl
  rw [h123, sp1Core_queryBits_123] at hmono
  omega

/-! ## Ceiling -/

/-- **Ceiling.** No query count takes SP1 core's total above 100 bits. -/
theorem sp1Core_total_le_100 (q : ℕ) : secBits (sp1CoreJaggedq q).totalErr ≤ 100 := by
  have hle : sp1CoreLookup.errUB ≤ (sp1CoreJaggedq q).totalErr :=
    (sp1CoreJaggedq q).lookup_le_totalErr (by rw [sp1CoreJaggedq_lookups]; simp)
  calc secBits (sp1CoreJaggedq q).totalErr
      ≤ secBits sp1CoreLookup.errUB := secBits_anti sp1Core_lookupErr_pos hle
    _ = 100 := sp1_core_lookup_bits

end Soundcalc
