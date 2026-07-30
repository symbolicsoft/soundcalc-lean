import Soundcalc.Field.Core
import Soundcalc.PCS.FRI
import Soundcalc.PCS.WHIR

open Soundcalc

namespace Soundcalc

/-!
  `PCS` bundles all polynomial commitment schemes supported by zkVM circuits,
  acting as a normalization layer among PCS schemes of different types.

  Current support: FRI, WHIR (WIP).

  **TODO:** Complete integration with WHIR.
-/

inductive PCS where
  | fri  (c : FRIConfig)
  | whir (c : WHIRConfig)

def PCS.label : PCS -> String
  | .fri  _ => "FRI"
  | .whir _ => "WHIR"

def PCS.traceLen : PCS → ℕ
  | .fri c  => c.denseLen
  | .whir _ => 0 -- **TODO**

def PCS.batchSize : PCS → ℕ
  | .fri c  => c.batchSize
  | .whir c => c.batchSize

def PCS.ρ : PCS → Rate
  | .fri c => c.ρ
  | .whir _ => ⟨1/2, by norm_num⟩ -- **TODO**

def PCS.field : PCS → FieldParams
  | .fri c  => c.field
  | .whir c => c.field

def PCS.listErrs (c: PCS) (R: Regime) : List ℚ :=
  match c with
  | .fri c  => c.listErrs R
  | .whir _ => [] -- **TODO**

def PCS.proofSizeWorst : PCS → ℕ
  | .fri c  => c.proofSizeWorst
  | .whir c => c.proofSizeWorst

def PCS.proofSizeExp : PCS → ℕ
  | .fri c  => c.proofSizeExp
  | .whir c => c.proofSizeExp

end Soundcalc
