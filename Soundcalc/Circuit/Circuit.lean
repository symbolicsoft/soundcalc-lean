import Soundcalc.Field.Core
import Soundcalc.Circuit.GenericCircuit
import Soundcalc.Circuit.Jagged
import Soundcalc.Circuit.DeepAli

open Soundcalc

namespace Soundcalc

/-!
  `Circuit` bundles all circuits supported by a zkVM, acting as a
  normalization layer among circuits of different types.

  Current support: Jagged, DeepAli.

  **TODO:** Revisit regimes methods (`is*`, `getSecBits*`) and defaults
  once an appropriate generalization is introduced at circuit-level.
-/

inductive Circuit where
  | jagged  (c : JaggedCfg)
  | deepali (c : DeepAliCfg)

/- Helper method normalizing specialized circuits to the same generic GenericCircuit structure. -/
def Circuit.toGenericCircuit : Circuit → GenericCircuit
  | .jagged c  => c.toGenericCircuit
  | .deepali c => c.toGenericCircuit

/- Further helper dot-methods bundling together methods
   from different families of circuits. -/
def Circuit.name (c: Circuit) : String :=
  c.toGenericCircuit.name

def Circuit.proofSizeWorst : Circuit → ℕ
  | .jagged c  => c.proofSizeWorst
  | .deepali c => c.proofSizeWorst

def Circuit.proofSizeExp : Circuit → ℕ
  | .jagged c  => c.proofSizeExp
  | .deepali c => c.proofSizeExp

def Circuit.isUDR (c: Circuit) : Bool :=
  c.toGenericCircuit.isUDR

def Circuit.isJBR (c: Circuit) : Bool :=
  c.toGenericCircuit.isJBR

def Circuit.totalSecBitsUDR : Circuit → ℕ
  | .jagged c  => secBits (c.totalErr)  -- current support: UDR only (we don't specify a regime)
  | .deepali c => secBits (c.totalErr (UDR c.field))

/- Following our Airbender characterization (`Soundcalc/ZkVM/Airbender.lean`),
   we keep `g = 2^40` as the sqrt granularity in JBR. -/
def Circuit.totalSecBitsJBR : Circuit → ℕ
  | .jagged _  => 0                     -- unsupported; *TODO* ìmprove representation.
  | .deepali c => secBits (c.totalErr (JBR c.field (2^40)))

end Soundcalc
