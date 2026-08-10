import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Common

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `DeepAliCfg` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/--
  Mirrors Python's `get_report_parameter_lines` for DEEP-ALI circuits.
-/
def DeepAliCfg.renderCircParams (c: DeepAliCfg) : IO String := do
  let mut outStr := ""

  /- We interpret `c` as a generic Circuit to access dot-methods shared
     among multiple circuits (`gc.proofSysName`). -/
  let gc : Circuit := .deepali c

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname c.densePCS.field)
  let floatRate ← orExit (rateToFloat mapFloatToRate c.densePCS.ρ)
  let floatRateStr := floatToFloatstr floatRate

  let grindDeepStr :=
    if c.grindDeep > 0 then
      s!"- Grinding DEEP (bits): {c.grindDeep}\n"
    else s!""

  /- Currently-supported PCS: FRI
    **SOUNDCALC TODO** Extend soundcalc to decouple DEEP-ALI+FRI. -/
  match c.densePCS with
  | .fri fcfg =>
    /- Conditional strings -/
    let batchingStr := if fcfg.powerBatch then "Powers" else "Affine"
    let grindcommitStr :=
      if fcfg.grindCommit > 0 then
        s!"- Grinding commit phase, at every folding round (bits): {fcfg.grindCommit}\n"
      else s!""

    let grindBatchStr :=
      if fcfg.grindBatch > 0 then
        s!"- Grinding batching phase (bits): {fcfg.grindBatch}\n"
      else s!""

    outStr := outStr ++
    s!"- Proof system: {gc.proofSysName}\n" ++
    s!"- PCS: {c.densePCS.label}\n" ++
    s!"- Hash size (bits): {fcfg.hashBits}\n" ++
    s!"- Number of queries: {fcfg.numQueries}\n" ++
    s!"- Grinding query phase (bits): {fcfg.grindQuery}\n" ++
    /- Conditional grinding string -/
    s!"{grindBatchStr}" ++
    s!"{grindcommitStr}" ++
    s!"- Field: {fieldDisplayName}\n" ++
    s!"- Rate (ρ): {floatRateStr}\n" ++
    s!"- Trace length (H): $2^\{{fcfg.h}}$\n" ++
    s!"- FRI rounds: {fcfg.rounds}\n" ++
    s!"- FRI folding factors: {fcfg.foldingFactors}\n" ++
    s!"- FRI early stop degree: {fcfg.earlyStopDeg}\n" ++
    s!"- Batch size: {fcfg.batchSize}\n" ++
    s!"- Batching: {batchingStr}\n" ++
    s!"{grindDeepStr}" ++
    s!"- Number of constraints: {c.numConstraints}\n"
  | .whir _ => IO.eprintln "Unsupported PCS scheme (WHIR)."; IO.Process.exit 1

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

  /- Currently-supported PCS: FRI
    **SOUNDCALC TODO** Extend soundcalc to decouple DEEP-ALI+FRI. -/
  match c.densePCS with
  | .fri fcfg =>
  /- FRIConfig secBits: batching, commit round {i}, query phase -/
    l := l ++ [("batching", (secBits (fcfg.batchingErr (R))))]

    for i in rangeAlph fcfg.rounds do
      let roundLabel := s!"commit round {i}"
      l := l ++ [(roundLabel, (secBits (fcfg.commitErr (R) (i-1))))]
    l := l ++ [("query phase", (secBits (fcfg.queryErr (R))))]
  | .whir _ => IO.eprintln "Unsupported PCS scheme (WHIR)."; IO.Process.exit 1
  pure l

end Soundcalc
