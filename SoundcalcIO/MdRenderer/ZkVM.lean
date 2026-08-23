import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Common

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `ZkVM` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/-
  The headline (binding circuit, its security, and the regime label) is
  `ZkVM.bestSecurityAcrossCircuits`, defined in `Soundcalc/Headline.lean`
  together with `ZkVM.headline_le_bestSecBits`: on every branch of the
  report hierarchy the headline is at most each circuit's best applicable
  security. The renderer prints that value unchanged.
  Ref: https://github.com/ethereum/soundcalc/blob/cee252916d6d9f8579c3d41b2eddb946c329d743/soundcalc/report_md.py#L86
-/

def ZkVM.finalProofSizeExpKiB (vm: ZkVM)(h_nonempty_circs: vm.circuits ≠ []) : Nat :=
  let vm_lastCirc := vm.circuits.getLast h_nonempty_circs
  vm_lastCirc.proofSizeExp / KIB

def ZkVM.finalProofSizeWorstKiB (vm: ZkVM)(h_nonempty_circs: vm.circuits ≠ []) : Nat :=
  let vm_lastCirc := vm.circuits.getLast h_nonempty_circs
  vm_lastCirc.proofSizeWorst / KIB

def ZkVM.proofSystemLabel (vm: ZkVM) : String := Id.run do
  let mut labels : List String := []
  for circ in vm.circuits do
    let label := s!"{circ.proofSysName} + {circ.PCS.label}"
    if not (labels.contains label) then
      labels := labels.append [label]
  if h : labels.length == 1 then
    have hne : labels ≠ [] := by
      intro hnil
      rw [hnil] at h
      simp at h
    return labels.head hne
  else
    /- Sample: Mixed(Jagged + FRI, SWIRL + WHIR)-/
    return "Mixed(" ++ ", ".intercalate labels ++ ")"

end Soundcalc
