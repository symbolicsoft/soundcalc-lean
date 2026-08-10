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

/--
  We identify the circuit that has the worst overall secBits, following `soundcalc`'s semantics:
  - If no global regime is found, each circuit contributes to the overall zkVM with its best regime.
    This yields a "mixed" regime.
  - If exactly one global regime is found, we output the circuit with the worst security bits for that regime.
  - If both global regimes are found, we output the circuit with the worst security bits for the best regime.
  Ref: https://github.com/ethereum/soundcalc/blob/cee252916d6d9f8579c3d41b2eddb946c329d743/soundcalc/report_md.py#L86

  Current support: UDR, JBR, mirroring `soundcalc`.
  **TODO** Revisit whenever regimes are generalized.
-/
def ZkVM.bestSecurityAcrossCircuits (vm: ZkVM)(h_nonempty_circs : vm.circuits ≠ []) : (Circuit × Nat × String) :=
  let vm_circuits := vm.circuits

  let vm_firstCirc := vm_circuits.head h_nonempty_circs

  let vm_globalUDR := vm_circuits.foldl (
    fun acc c => c.isUDR && acc
  ) (vm_firstCirc.isUDR)

  let vm_globalJBR := vm_circuits.foldl (
    fun acc c => c.isJBR && acc
  ) (vm_firstCirc.isJBR)

  let (worstRegimeCirc, bestRegimeSecBits, bestRegime) := match vm_globalUDR, vm_globalJBR with
    /- If no global regime is supported, each circuit contributes with its best regime.
        The final regime is denoted as "mixed".-/
    | false, false =>
      let worstCirc := vm_circuits.foldl
        (fun (worst c: Circuit) =>
          if max (c.totalSecBitsUDR.getD 0) (c.totalSecBitsJBR.getD 0) < max (worst.totalSecBitsUDR.getD 0) (worst.totalSecBitsJBR.getD 0) then c
          else worst)
        vm_firstCirc -- first circuit to accumulate over: always exists due to `hne`!

      /- Current behaviour: assign a missing regime a security of 0 within the evaluation of the max.
         **TODO** Replace defaults once regimes are appropriately generalized. -/
      let bestRegimeSecBits := max (worstCirc.totalSecBitsUDR.getD 0) (worstCirc.totalSecBitsJBR.getD 0)
      (worstCirc, bestRegimeSecBits, "mixed")
    /- In what's below, at least one global regime is defined. -/
    | globalUDR, globalJBR =>
      /- Evaluates the circuit with the worst overall secBits using UDR. -/
      let worstCircUDR := vm_circuits.foldl
        (fun (worst c: Circuit) =>
          if c.totalSecBitsUDR.getD 0 < worst.totalSecBitsUDR.getD 0 then c
          else worst)
        vm_firstCirc

      let minSecBitsUDR := worstCircUDR.totalSecBitsUDR.getD 0

      /- Evaluates the circuit with the worst overall secBits using JBR. -/
      let worstCircJBR := vm_circuits.foldl
        (fun (worst c: Circuit) =>
          if c.totalSecBitsJBR.getD 0 < worst.totalSecBitsJBR.getD 0 then c
          else worst)
        vm_firstCirc

      let minSecBitsJBR := worstCircJBR.totalSecBitsJBR.getD 0

      /- If all the circuits in the zkVM have exactly one shared regime, we pick that.
        Otherwise, we pick the best among the two. -/
      if globalUDR && globalJBR then
        if minSecBitsUDR > minSecBitsJBR then (worstCircUDR, minSecBitsUDR, "UDR")
        else (worstCircJBR, minSecBitsJBR, "JBR")
      else if globalUDR then (worstCircUDR, minSecBitsUDR, "UDR")
      else (worstCircJBR, minSecBitsJBR, "JBR")

  (worstRegimeCirc, bestRegimeSecBits, bestRegime)

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
