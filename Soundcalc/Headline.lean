import Soundcalc.ZkVM

/-!
# `Soundcalc.Headline` — the report hierarchy, with its theorem

A zkVM report ends in one number: the headline security level. soundcalc
derives it from the per-circuit, per-regime totals in three ways, depending
on which regimes every circuit supports (see `report_md.py`):

* every circuit supports UDR only (or JBR only): the headline is the minimum
  over circuits of that regime's total;
* every circuit supports both regimes: the headline is the better of the two
  per-regime minima;
* otherwise ("mixed"): each circuit contributes the best of the regimes that
  apply to it, and the headline is the minimum of those.

The OpenVM 2.0 incident was an aggregation in the wrong order for the mixed
case (`max` over regimes of `min` over circuits, instead of `min` over
circuits of `max` over regimes), which let the headline exceed the best
analysis of one of the circuits. `bestSecurityAcrossCircuits_le` rules that
class out: whatever branch is taken, the headline is at most every circuit's
best applicable security.

The renderer (`SoundcalcIO/MdRenderer/ZkVM.lean`) prints exactly
`ZkVM.bestSecurityAcrossCircuits`, so the theorem is about the number that
appears in the report.
-/

namespace Soundcalc

/-! ## Per-circuit totals as plain naturals -/

/-- UDR total of a circuit, or `0` when UDR does not apply. -/
def Circuit.secBitsUDR (c : Circuit) : ℕ := c.totalSecBitsUDR.getD 0

/-- JBR total of a circuit, or `0` when JBR does not apply. -/
def Circuit.secBitsJBR (c : Circuit) : ℕ := c.totalSecBitsJBR.getD 0

/-- The best security a circuit reaches under a regime that applies to it.
A regime that does not apply contributes `0`, so it never wins the `max`. -/
def Circuit.bestSecBits (c : Circuit) : ℕ := max c.secBitsUDR c.secBitsJBR

theorem Circuit.secBitsUDR_le_best (c : Circuit) : c.secBitsUDR ≤ c.bestSecBits :=
  le_max_left _ _

theorem Circuit.secBitsJBR_le_best (c : Circuit) : c.secBitsJBR ≤ c.bestSecBits :=
  le_max_right _ _

/-! ## A generic argmin over a list -/

/-- The element of `init :: l` minimising `f`, keeping the earlier one on ties.
This is the fold soundcalc uses to find the weakest circuit. -/
def argminBy {α : Type*} (f : α → ℕ) (init : α) (l : List α) : α :=
  l.foldl (fun w c => if f c < f w then c else w) init

@[simp] theorem argminBy_nil {α : Type*} (f : α → ℕ) (init : α) :
    argminBy f init [] = init := rfl

theorem argminBy_cons {α : Type*} (f : α → ℕ) (init a : α) (l : List α) :
    argminBy f init (a :: l) = argminBy f (if f a < f init then a else init) l := rfl

/-- `argminBy` is a lower bound for `f` on `init` and on every element of `l`. -/
theorem argminBy_le {α : Type*} (f : α → ℕ) (l : List α) (init : α) :
    f (argminBy f init l) ≤ f init ∧ ∀ c ∈ l, f (argminBy f init l) ≤ f c := by
  induction l generalizing init with
  | nil => exact ⟨le_rfl, fun c h => absurd h (List.not_mem_nil)⟩
  | cons a l ih =>
    rw [argminBy_cons]
    obtain ⟨h1, h2⟩ := ih (if f a < f init then a else init)
    have hstep : f (if f a < f init then a else init) ≤ f init ∧
        f (if f a < f init then a else init) ≤ f a := by
      split_ifs with h <;> omega
    refine ⟨le_trans h1 hstep.1, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact le_trans h1 hstep.2
    · exact h2 c hc

/-- `argminBy` returns `init` or an element of `l`. -/
theorem argminBy_mem {α : Type*} (f : α → ℕ) (l : List α) (init : α) :
    argminBy f init l = init ∨ argminBy f init l ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [argminBy_cons]
    by_cases hlt : f a < f init
    · rw [if_pos hlt]
      rcases ih a with h | h
      · exact Or.inr (by rw [h]; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [if_neg hlt]
      rcases ih init with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-! ## The headline -/

/-- Does every circuit of `vm` support the unique-decoding regime? -/
def ZkVM.globalUDR (vm : ZkVM) (h : vm.circuits ≠ []) : Bool :=
  vm.circuits.foldl (fun acc c => c.isUDR && acc) (vm.circuits.head h).isUDR

/-- Does every circuit of `vm` support the Johnson-bound regime? -/
def ZkVM.globalJBR (vm : ZkVM) (h : vm.circuits ≠ []) : Bool :=
  vm.circuits.foldl (fun acc c => c.isJBR && acc) (vm.circuits.head h).isJBR

/-- The weakest circuit under UDR. -/
def ZkVM.worstCircuitUDR (vm : ZkVM) (h : vm.circuits ≠ []) : Circuit :=
  argminBy Circuit.secBitsUDR (vm.circuits.head h) vm.circuits

/-- The weakest circuit under JBR. -/
def ZkVM.worstCircuitJBR (vm : ZkVM) (h : vm.circuits ≠ []) : Circuit :=
  argminBy Circuit.secBitsJBR (vm.circuits.head h) vm.circuits

/-- The weakest circuit when each circuit is judged by its best applicable regime. -/
def ZkVM.worstCircuitMixed (vm : ZkVM) (h : vm.circuits ≠ []) : Circuit :=
  argminBy Circuit.bestSecBits (vm.circuits.head h) vm.circuits

/-- The headline: the binding circuit, its security, and the regime label printed
next to it. Mirrors soundcalc's `report_md.py` (post-fix). -/
def ZkVM.bestSecurityAcrossCircuits (vm : ZkVM) (h : vm.circuits ≠ []) :
    Circuit × ℕ × String :=
  if !vm.globalUDR h && !vm.globalJBR h then
    (vm.worstCircuitMixed h, (vm.worstCircuitMixed h).bestSecBits, "mixed")
  else if vm.globalUDR h && vm.globalJBR h then
    if (vm.worstCircuitUDR h).secBitsUDR > (vm.worstCircuitJBR h).secBitsJBR then
      (vm.worstCircuitUDR h, (vm.worstCircuitUDR h).secBitsUDR, "UDR")
    else (vm.worstCircuitJBR h, (vm.worstCircuitJBR h).secBitsJBR, "JBR")
  else if vm.globalUDR h then (vm.worstCircuitUDR h, (vm.worstCircuitUDR h).secBitsUDR, "UDR")
  else (vm.worstCircuitJBR h, (vm.worstCircuitJBR h).secBitsJBR, "JBR")

/-- The headline security level alone. -/
def ZkVM.headline (vm : ZkVM) (h : vm.circuits ≠ []) : ℕ :=
  (vm.bestSecurityAcrossCircuits h).2.1

/-- **The headline never exceeds any circuit's best applicable analysis.**
This is the invariant the OpenVM 2.0 aggregation violated: a 99-bit circuit
under a 100-bit headline. It holds on every branch of the report hierarchy. -/
theorem ZkVM.headline_le_bestSecBits (vm : ZkVM) (h : vm.circuits ≠ []) :
    ∀ c ∈ vm.circuits, vm.headline h ≤ c.bestSecBits := by
  intro c hc
  have hU : (vm.worstCircuitUDR h).secBitsUDR ≤ c.secBitsUDR :=
    (argminBy_le Circuit.secBitsUDR vm.circuits (vm.circuits.head h)).2 c hc
  have hJ : (vm.worstCircuitJBR h).secBitsJBR ≤ c.secBitsJBR :=
    (argminBy_le Circuit.secBitsJBR vm.circuits (vm.circuits.head h)).2 c hc
  have hM : (vm.worstCircuitMixed h).bestSecBits ≤ c.bestSecBits :=
    (argminBy_le Circuit.bestSecBits vm.circuits (vm.circuits.head h)).2 c hc
  have hU' := le_trans hU c.secBitsUDR_le_best
  have hJ' := le_trans hJ c.secBitsJBR_le_best
  unfold ZkVM.headline ZkVM.bestSecurityAcrossCircuits
  split_ifs <;> assumption

/-- The binding circuit is one of the zkVM's circuits. -/
theorem ZkVM.bestSecurityAcrossCircuits_mem (vm : ZkVM) (h : vm.circuits ≠ []) :
    (vm.bestSecurityAcrossCircuits h).1 ∈ vm.circuits := by
  have hhead : vm.circuits.head h ∈ vm.circuits := List.head_mem h
  have key : ∀ f : Circuit → ℕ, argminBy f (vm.circuits.head h) vm.circuits ∈ vm.circuits := by
    intro f
    rcases argminBy_mem f vm.circuits (vm.circuits.head h) with heq | hmem
    · rw [heq]; exact hhead
    · exact hmem
  unfold ZkVM.bestSecurityAcrossCircuits
  split_ifs <;> first
    | exact key Circuit.bestSecBits
    | exact key Circuit.secBitsUDR
    | exact key Circuit.secBitsJBR

/-- The headline is attained: some circuit's best applicable security, or one of its
per-regime totals, equals it. Together with `headline_le_bestSecBits` this pins the
headline to `min` over circuits of `max` over applicable regimes in the mixed case. -/
theorem ZkVM.headline_mixed_attained (vm : ZkVM) (h : vm.circuits ≠ [])
    (hmix : !vm.globalUDR h && !vm.globalJBR h) :
    ∃ c ∈ vm.circuits, vm.headline h = c.bestSecBits := by
  refine ⟨vm.worstCircuitMixed h, ?_, ?_⟩
  · rcases argminBy_mem Circuit.bestSecBits vm.circuits (vm.circuits.head h) with heq | hmem
    · unfold ZkVM.worstCircuitMixed; rw [heq]; exact List.head_mem h
    · exact hmem
  · unfold ZkVM.headline ZkVM.bestSecurityAcrossCircuits
    simp [hmix]

end Soundcalc
