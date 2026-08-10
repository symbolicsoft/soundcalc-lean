import Soundcalc

/-!
# Axiom-hygiene guard (run by CI: `lake env lean scripts/AxiomsGuard.lean`)

Pins the trusted computing base claimed in the README as machine-checked facts:

* The structural theory — the `secBits` characterization, the `√·`/`log₂`
  enclosures, JBR conservativity, and every field preset (including the
  Goldilocks Pratt certificate) — depends only on Lean's three standard axioms:
  `propext`, `Classical.choice`, `Quot.sound`. In particular **no `sorryAx`**
  and **no `Lean.ofReduceBool`** (`native_decide`) anywhere in that cone.
* The monotonicity catalog (`Soundcalc.Monotonicity.*`) — every *shape* theorem
  about how a cell moves when a knob turns — is likewise kernel-only. This is
  the sharper half of the two-tier claim: the point-wise cells lean on the
  compiler, but the structural results *about the formulas* do not.
* The numeric report-cell theorems extend the TCB by exactly one generated
  `native_decide` axiom each (validated through the Lean compiler) — pinned
  on a representative below so any change to the TCB shape shows up in CI.

If a refactor makes one of these acquire a new axiom (or `sorry`), the
`#guard_msgs` mismatch fails this file, and CI with it.
-/

/-! ## Kernel-clean core (standard axioms only) -/

/-- info: 'Soundcalc.le_secBits_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.le_secBits_iff

/-- info: 'Soundcalc.secBits_min'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.secBits_min'

/-- info: 'Soundcalc.sqrtLB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.sqrtLB_le

/-- info: 'Soundcalc.le_sqrtUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.le_sqrtUB

/-- info: 'Soundcalc.log2UB_approx_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.log2UB_approx_bound

/-- info: 'Soundcalc.jbrErrLinear_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.jbrErrLinear_conservative

/-! ## Field presets: primality/2-adicity certificates are kernel-clean -/

/-- info: 'Soundcalc.koalaBear4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.koalaBear4

/-- info: 'Soundcalc.mersenne31_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.mersenne31_4

/-- info: 'Soundcalc.babyBear4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.babyBear4

/-- info: 'Soundcalc.goldilocks_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.goldilocks_prime

/-- info: 'Soundcalc.goldilocks3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.goldilocks3

/-- info: 'Soundcalc.koalaBear4_baseBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.koalaBear4_baseBits

/-! ## Monotonicity catalog: kernel-clean, no `native_decide` anywhere

The catalog states how a cell moves when a configuration knob or the decoding
regime changes. Unlike the numeric cells, *none* of it is discharged by
evaluation — the proofs are ordinary Mathlib arguments over `ℚ` and `ℝ`, so the
whole layer must stay on the three standard axioms. The proof-size results are
the ones worth watching: they reason about `Nat.clog`, `foldl` accumulators and
the Merkle inclusion–exclusion sum, all of which are tempting to close by
`decide`/`native_decide` under maintenance pressure. One representative per
module, so a regression anywhere in `Soundcalc/Monotonicity/` trips CI. -/

/-- info: 'Soundcalc.two_sqrt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.two_sqrt_le

/-- info: 'Soundcalc.secBits_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.secBits_grind

/-- info: 'Soundcalc.johnson_beats_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.johnson_beats_unique

/-- info: 'Soundcalc.FRIConfig.queryErr_antitone_numQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.FRIConfig.queryErr_antitone_numQueries

/-- info: 'Soundcalc.FRIConfig.proofSizeWorst_mono_numQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.FRIConfig.proofSizeWorst_mono_numQueries

/-- info: 'Soundcalc.whir_multiplicity_interior_optimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.whir_multiplicity_interior_optimum

/-- info: 'Soundcalc.JaggedCfg.zerocheckErr_antitone_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.JaggedCfg.zerocheckErr_antitone_card

/-- info: 'Soundcalc.DeepAliCfg.deepErr_mono_listSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.DeepAliCfg.deepErr_mono_listSize

/-- info: 'Soundcalc.LookupCfg.errUB_antitone_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.LookupCfg.errUB_antitone_card

/-! ## native_decide cells: TCB extension pinned

Each `native_decide` use introduces one generated axiom
(`<decl>._native.native_decide.ax_1_1`, validated through the compiler);
pinning a representative documents that shape — and that *nothing else*
(no `sorryAx`) enters these theorems' axiom sets. -/

/--
info: 'Soundcalc.sp1_core_lookup_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Soundcalc.sp1_core_lookup_bits._native.native_decide.ax_1_1]
-/
#guard_msgs in #print axioms Soundcalc.sp1_core_lookup_bits
