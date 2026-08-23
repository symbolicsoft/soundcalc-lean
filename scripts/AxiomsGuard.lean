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
* The numeric report-cell theorems are discharged by `decide +kernel` and so
  sit on the same three axioms; representatives are pinned below so that a
  regression to `native_decide` shows up in CI.

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
whole layer must stay on the three standard axioms. The `Nat.clog` and `foldl`
reasoning is what to watch: both are tempting to close by `decide`/`native_decide`
under maintenance pressure. One representative per module, so a regression
anywhere in `Soundcalc/Monotonicity/` trips CI. -/

/-- info: 'Soundcalc.two_sqrt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.two_sqrt_le

/-- info: 'Soundcalc.secBits_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.secBits_grind

/-- info: 'Soundcalc.johnson_beats_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.johnson_beats_unique

/-- info: 'Soundcalc.FRIConfig.queryErr_antitone_numQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.FRIConfig.queryErr_antitone_numQueries

/-- info: 'Soundcalc.FRIConfig.commitDimErr_antitone_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.FRIConfig.commitDimErr_antitone_round

/-- info: 'Soundcalc.whir_multiplicity_interior_optimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.whir_multiplicity_interior_optimum

/-- info: 'Soundcalc.JaggedCfg.zerocheckErr_antitone_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.JaggedCfg.zerocheckErr_antitone_card

/-- info: 'Soundcalc.DeepAliCfg.deepErr_mono_listSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.DeepAliCfg.deepErr_mono_listSize

/-- info: 'Soundcalc.LookupCfg.errUB_antitone_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.LookupCfg.errUB_antitone_card

/-! ## Report hierarchy: the headline theorem is kernel-clean -/

/-- info: 'Soundcalc.ZkVM.headline_le_bestSecBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.ZkVM.headline_le_bestSecBits

/-- info: 'Soundcalc.JaggedCfg.lookup_le_totalErr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.JaggedCfg.lookup_le_totalErr

/-! ## Numeric cells: kernel-checked, no `native_decide` anywhere

Every report cell and bundle is discharged by `decide +kernel`, so the numeric
layer sits on the same three axioms as the structural theory. Pinning a
representative cell, a full bundle-sized total, and the SP1 corollaries
documents that shape; a regression to `native_decide` (or a `sorry`) shows up
here as an extra axiom. -/

/-- info: 'Soundcalc.sp1_core_lookup_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.sp1_core_lookup_bits

/-- info: 'Soundcalc.sp1Core_queries_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.sp1Core_queries_minimal

/-- info: 'Soundcalc.sp1Core_total_le_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Soundcalc.sp1Core_total_le_100
