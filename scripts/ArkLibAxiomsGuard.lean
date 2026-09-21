import SoundcalcArkLib

/-!
# ArkLib bridge axiom guard

The ArkLib dependency contains tracked admissions outside this theorem's dependency cone. These
declaration-level checks ensure that both the upstream BCIKS20 result and Soundcalc's transported
result continue to avoid `sorryAx` and `Lean.ofReduceBool`.
-/

/-- info: 'ProximityGap.rs_mcaError_le_of_le_relUDR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProximityGap.rs_mcaError_le_of_le_relUDR

/--
info: 'Soundcalc.ArkLibBridge.rs_mcaError_le_uniqueDecodingEnvelope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Soundcalc.ArkLibBridge.rs_mcaError_le_uniqueDecodingEnvelope
