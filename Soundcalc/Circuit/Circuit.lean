import Soundcalc.Field.Core
import Soundcalc.Circuit.Jagged
import Soundcalc.Circuit.DeepAli
import Soundcalc.Circuit.SWIRL.Circuit
import Soundcalc.Circuit.SWIRL.ComputeError
import Soundcalc.Circuit.SWIRL.ProofSize


open Soundcalc

namespace Soundcalc

/-!
  `Circuit` bundles all circuits supported by a zkVM, acting as a
  normalization layer among circuits of different types.

  Current support: Jagged, DeepAli, SWIRL.

  **FEAT TODO** Revisit regimes methods (`is*`, `getSecBits*`) and defaults
  once an appropriate generalization is introduced at circuit-level.
-/

inductive Circuit where
  | jagged  (c : JaggedCfg)
  | deepali (c : DeepAliCfg)
  | swirl   (c : SWIRLCfg)

/- Further helper dot-methods bundling together methods
   from different families of circuits. -/
def Circuit.name : Circuit → String
  | .jagged c  => c.name
  | .deepali c => c.name
  | .swirl c   => c.name

def Circuit.field : Circuit → FieldParams
  | .jagged c  => c.field
  | .deepali c => c.field
  | .swirl c   => c.field

def Circuit.proofSysName : Circuit → String
  | .jagged _  => "Jagged"
  | .deepali _ => "DEEP-ALI"
  | .swirl _   => "SWIRL"

def Circuit.proofSizeWorst : Circuit → ℕ
  | .jagged c  => c.proofSizeWorst
  | .deepali c => c.proofSizeWorst
  | .swirl c   => c.proofSizeBits

def Circuit.proofSizeExp : Circuit → ℕ
  | .jagged c  => c.proofSizeExp
  | .deepali c => c.proofSizeExp
  | .swirl c   => c.proofSizeBits

/-
  - Jagged circuits are always (and only) UDR.
  - DeepAli circuits support both UDR and JBR.
  - SWIRL circuits are either UDR or JBR, according to the
    contents of the `explicitM` field. -/
def Circuit.isUDR : Circuit → Bool
  | .jagged _  => true
  | .deepali _ => true
  | .swirl c   => match c.explicitM with
    | some _ => false
    | none   => true

def Circuit.isJBR : Circuit → Bool
  | .jagged _  => false
  | .deepali _ => true
  | .swirl c   => match c.explicitM with
    | some _ => true
    | none   => false

def Circuit.totalSecBitsUDR : Circuit → ℕ
  | .jagged c  => secBits (c.totalErr)  -- current support: UDR only (we don't specify a regime)
  | .deepali c => secBits (c.totalErr (UDR c.field))
  | .swirl c   => secBits (c.totalErr)

/- Following our Airbender characterization (`Soundcalc/ZkVM/Airbender.lean`),
   we keep `g = 2^40` as the sqrt granularity in JBR. -/
def Circuit.totalSecBitsJBR : Circuit → ℕ
  | .jagged _  => 0                     -- unsupported; *TODO* ìmprove representation.
  | .deepali c => secBits (c.totalErr (JBR c.field (2^40) c.gapToRadius))
  | .swirl c   => secBits (c.totalErr)

def Circuit.PCS : Circuit → PCS
  | .jagged c  => c.densePCS
  | .deepali c => c.densePCS
  | .swirl c   => .whir c.whir

end Soundcalc
