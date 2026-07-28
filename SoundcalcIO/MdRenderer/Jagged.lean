import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Common

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `Circuit` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/--
  Mirrors Python's `get_report_parameter_lines` of Jagged circuits.
-/
def JaggedCfg.renderCircParams (c: JaggedCfg) : IO String := do
  let mut outStr := ""

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname c.densePCS.field)
  let floatRate ← orExit (rateToFloat mapFloatToRate c.densePCS.ρ)
  let floatRateStr := floatToFloatstr floatRate

  /- Conditional strings -/
  let batchingStr := if c.densePCS.powerBatch then "Powers" else "Affine"
  let grindcommitStr :=
    if c.densePCS.grindCommit > 0 then
      s!"- Grinding commit phase (bits): {c.densePCS.grindCommit}\n"
    else s!""

  outStr := outStr ++
  s!"- Proof system: {c.proofSystName}\n" ++
  s!"- PCS: FRI\n" ++
  s!"- Hash size (bits): {c.densePCS.hashBits}\n" ++
  s!"- Number of queries: {c.densePCS.numQueries}\n" ++
  s!"- Grinding query phase (bits): {c.densePCS.grindQuery}\n" ++
  /- Conditional grinding string -/
  s!"{grindcommitStr}" ++
  s!"- Field: {fieldDisplayName}\n" ++
  s!"- Rate (ρ): {floatRateStr}\n" ++
  s!"- Dense trace length: $2^\{{c.densePCS.h}}$\n" ++
  s!"- Trace length: {c.traceLength}\n" ++
  s!"- Trace width: {c.traceWidth}\n" ++
  s!"- FRI rounds: {c.densePCS.rounds}\n" ++
  s!"- FRI folding factors: {c.densePCS.foldingFactors}\n" ++
  s!"- FRI early stop degree: {c.densePCS.earlyStopDeg}\n" ++
  s!"- Dense batch size: {c.densePCS.batchSize}\n" ++
  s!"- Batching: {batchingStr}\n"

  for lookup in c.lookups do
    outStr := outStr ++
    s!"- Lookup (logup): {lookup.name}\n"

  pure outStr

/--
  Mirrors Python's `get_security_levels` for Jagged circuits.
-/
def JaggedCfg.getSecurityLevels (c: JaggedCfg) : IO (List (String × Nat)) := do
  let mut l : List (String × Nat) := []

  /- Minimum overall secBits -/
  l := l ++ [("total", (secBits c.totalErr))]

  /- Lookup secBits -/
  for lookup in c.lookups do
    l := l ++ [(lookup.name, (secBits lookup.errUB))]

  /- FRIConfig secBits: batching, commit round {i}, query phase -/
  let fcfg := c.densePCS
  l := l ++ [("batching", (secBits (fcfg.batchingErr (UDR fcfg.field))))]

  for i in rangeAlph fcfg.rounds do
    let roundLabel := s!"commit round {i}"
    l := l ++ [(roundLabel, (secBits (fcfg.commitErr (UDR fcfg.field) (i-1))))]
  l := l ++ [("query phase", (secBits (fcfg.queryErr (UDR fcfg.field))))]

  /- Circuit secBits: reduce to dense PCS, zerocheck -/
  l := l ++ [("reduce to dense PCS", (secBits c.reduceErr))]
  l := l ++ [("zerocheck", (secBits c.zerocheckErr))]

  pure l

end Soundcalc
