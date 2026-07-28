import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Common

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `CircuitVM` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/--
  Mirrors Python's `get_report_parameter_lines` for DEEP-ALI circuits.
-/
def DeepAliCfg.renderCircParams (c: DeepAliCfg) : IO String := do
  let mut outStr := ""

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname c.densePCS.field)
  let floatRate ← orExit (rateToFloat mapFloatToRate c.densePCS.ρ)
  let floatRateStr := floatToFloatstr floatRate

  let grindDeepStr :=
    if c.grindDeep > 0 then
      s!"- Grinding DEEP (bits): {c.grindDeep}\n"
    else s!""

  /- Conditional strings -/
  let batchingStr := if c.densePCS.powerBatch then "Powers" else "Affine"
  let grindcommitStr :=
    if c.densePCS.grindCommit > 0 then
      s!"- Grinding commit phase, at every folding round (bits): {c.densePCS.grindCommit}\n"
    else s!""

  let grindBatchStr :=
    if c.densePCS.grindBatch > 0 then
      s!"- Grinding batching phase (bits): {c.densePCS.grindBatch}\n"
    else s!""

  outStr := outStr ++
  s!"- Proof system: {c.proofSystName}\n" ++
  s!"- PCS: FRI\n" ++
  s!"- Hash size (bits): {c.densePCS.hashBits}\n" ++
  s!"- Number of queries: {c.densePCS.numQueries}\n" ++
  s!"- Grinding query phase (bits): {c.densePCS.grindQuery}\n" ++
  /- Conditional grinding string -/
  s!"{grindBatchStr}" ++
  s!"{grindcommitStr}" ++
  s!"- Field: {fieldDisplayName}\n" ++
  s!"- Rate (ρ): {floatRateStr}\n" ++
  s!"- Trace length (H): $2^\{{c.densePCS.h}}$\n" ++
  s!"- FRI rounds: {c.densePCS.rounds}\n" ++
  s!"- FRI folding factors: {c.densePCS.foldingFactors}\n" ++
  s!"- FRI early stop degree: {c.densePCS.earlyStopDeg}\n" ++
  s!"- Batch size: {c.densePCS.batchSize}\n" ++
  s!"- Batching: {batchingStr}\n" ++
  s!"{grindDeepStr}" ++
  s!"- Number of constraints: {c.numConstraints}\n"

  for lookup in c.lookups do
    outStr := outStr ++
    s!"- Lookup (logup): {lookup.name}\n"

  pure outStr

/--
  Mirrors Python's `get_security_levels` for DEEP-ALI circuits.
-/
def DeepAliCfg.getSecurityLevels (c: DeepAliCfg) (R: Regime) : IO (List (String × Nat)) := do
  let mut l : List (String × Nat) := []

  /- Minimum overall secBits -/
  l := l ++ [("total", (secBits (c.totalErr R)))]

  /- Lookup secBits -/
  for lookup in c.lookups do
    l := l ++ [(lookup.name, (secBits lookup.errUB))]

  /- Circuit secBits: ALI, DEEP errors. -/
  l := l ++ [("ALI", (secBits (c.aliErr R)))]
  l := l ++ [("DEEP", (secBits (c.deepErr R)))]

  /- FRIConfig secBits: batching, commit round {i}, query phase -/
  let fcfg := c.densePCS
  l := l ++ [("batching", (secBits (fcfg.batchingErrPowers (R))))]

  for i in rangeAlph fcfg.rounds do
    let roundLabel := s!"commit round {i}"
    l := l ++ [(roundLabel, (secBits (fcfg.commitErr (R) (i-1))))]
  l := l ++ [("query phase", (secBits (fcfg.queryErr (R))))]

  pure l

end Soundcalc
