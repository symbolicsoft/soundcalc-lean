import Soundcalc
import SoundcalcIO.Common
import SoundcalcIO.MdRenderer.Common

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

/-
  We work in the `Soundcalc` namespace to extend `JaggedCfg` with appropriate rendering methods.
  These methods are defined here (as opposed to being defined in directly in `Soundcalc`),
  as they are exclusively related to the `MdRenderer`.
 -/
namespace Soundcalc

/--
  Mirrors Python's `get_report_parameter_lines` of Jagged circuits.
-/
def JaggedCfg.renderCircParams (c: JaggedCfg) : IO String := do
  let mut outStr := ""

  /- We interpret `c` as a generic Circuit to access dot-methods shared
     among multiple circuits (`gc.proofSysName`). -/
  let gc : Circuit := .jagged c

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname c.densePCS.field)
  let floatRate ← orExit (rateToFloat mapFloatToRate c.densePCS.ρ)
  let floatRateStr := floatToFloatstr floatRate

  /- Currently-supported PCS: FRI
    **SOUNDCALC TODO** Extend soundcalc to decouple Jagged+FRI. -/
  match c.densePCS with
  | .fri fcfg =>
    /- Conditional strings -/
    let batchingStr := if fcfg.powerBatch then "Powers" else "Affine"
    let grindcommitStr :=
      if fcfg.grindCommit > 0 then
        s!"- Grinding commit phase (bits): {fcfg.grindCommit}\n"
      else s!""

    outStr := outStr ++
    s!"- Proof system: {gc.proofSysName}\n" ++
    s!"- PCS: {c.densePCS.label}\n" ++
    s!"- Hash size (bits): {fcfg.hashBits}\n" ++
    s!"- Number of queries: {fcfg.numQueries}\n" ++
    s!"- Grinding query phase (bits): {fcfg.grindQuery}\n" ++
    /- Conditional grinding string -/
    s!"{grindcommitStr}" ++
    s!"- Field: {fieldDisplayName}\n" ++
    s!"- Rate (ρ): {floatRateStr}\n" ++
    s!"- Dense trace length: $2^\{{fcfg.h}}$\n" ++
    s!"- Trace length: {c.traceLength}\n" ++
    s!"- Trace width: {c.traceWidth}\n" ++
    s!"- FRI rounds: {fcfg.rounds}\n" ++
    s!"- FRI folding factors: {fcfg.foldingFactors}\n" ++
    s!"- FRI early stop degree: {fcfg.earlyStopDeg}\n" ++
    s!"- Dense batch size: {fcfg.batchSize}\n" ++
    s!"- Batching: {batchingStr}\n"
  | .whir _ => IO.eprintln "Unsupported PCS scheme (WHIR)."; IO.Process.exit 1

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

  /- Currently-supported PCS: FRI
    **SOUNDCALC TODO** Extend soundcalc to decouple Jagged+FRI. -/
  match c.densePCS with
  | .fri fcfg =>
  /- FRIConfig secBits: batching, commit round {i}, query phase -/
    l := l ++ [("batching", (secBits (fcfg.batchingErr (UDR fcfg.field))))]

    for i in rangeAlph fcfg.rounds do
      let roundLabel := s!"commit round {i}"
      l := l ++ [(roundLabel, (secBits (fcfg.commitErr (UDR fcfg.field) (i-1))))]
    l := l ++ [("query phase", (secBits (fcfg.queryErr (UDR fcfg.field))))]
  | .whir _ => IO.eprintln "Unsupported PCS scheme (WHIR)."; IO.Process.exit 1

  /- Circuit secBits: reduce to dense PCS, zerocheck -/
  l := l ++ [("reduce to dense PCS", (secBits c.reduceErr))]
  l := l ++ [("zerocheck", (secBits c.zerocheckErr))]
  pure l

end Soundcalc
