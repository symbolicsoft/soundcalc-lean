import Soundcalc.Field
import Soundcalc.Circuit.GenericCircuit
import Soundcalc.Circuit.Jagged
import Soundcalc.Circuit.DeepAli

open Soundcalc

namespace Soundcalc

/-!
  `CircuitVM` bundles all circuits supported by a zkVM, acting as a
  normalization layer among circuits of different types.

  Current support: Jagged, DeepAli.

  **TODO:** Revisit regimes methods (`is*`, `getSecBits*`) and defaults
  once an appropriate generalization is introduced at circuit-level.
-/

inductive CircuitVM where
  | jagged  (c : JaggedCfg)
  | deepali (c : DeepAliCfg)

/- Helper method normalizing specialized circuits to the same generic GenericCircuit structure. -/
def CircuitVM.toGenericCircuit : CircuitVM → GenericCircuit
  | .jagged c  => c.toGenericCircuit
  | .deepali c => c.toGenericCircuit

/- Further helper dot-methods bundling together methods
   from different families of circuits. -/
def CircuitVM.name (c: CircuitVM) : String :=
  c.toGenericCircuit.name

def CircuitVM.proofSizeWorst : CircuitVM → ℕ
  | .jagged c  => c.proofSizeWorst
  | .deepali c => c.proofSizeWorst

def CircuitVM.proofSizeExp : CircuitVM → ℕ
  | .jagged c  => c.proofSizeExp
  | .deepali c => c.proofSizeExp

def CircuitVM.isUDR (c: CircuitVM) : Bool :=
  c.toGenericCircuit.isUDR

def CircuitVM.isJBR (c: CircuitVM) : Bool :=
  c.toGenericCircuit.isJBR

def CircuitVM.totalSecBitsUDR : CircuitVM → ℕ
  | .jagged c  => secBits (c.totalErr)  -- current support: UDR only (we don't specify a regime)
  | .deepali c => secBits (c.totalErr (UDR c.field))

/- Following our Airbender characterization (`Soundcalc/ZkVM/Airbender.lean`),
   we keep `g = 2^40` as the sqrt granularity in JBR. -/
def CircuitVM.totalSecBitsJBR : CircuitVM → ℕ
  | .jagged _  => 0                     -- unsupported; *TODO* ìmprove representation.
  | .deepali c => secBits (c.totalErr (JBR c.field (2^40)))

end Soundcalc
