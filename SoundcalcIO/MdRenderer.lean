import Soundcalc
import SoundcalcIO.TomlParser
import SoundcalcIO.Common

open Soundcalc
open SoundcalcIO

namespace SoundcalcIO.MdRenderer

/--
  Maps supported `FieldParams` to their matching display name.
-/
private def mapFieldParamsToDisplayname : List (FieldParams × String) := [
  (koalaBear4, "KoalaBear⁴"),
]

private def fieldParamsToDisplayname (map : List (FieldParams × String))
                                     (fp : FieldParams) : Except String String :=
  match map.lookup fp with
  | some s => .ok s
  | none   => .error s!"unsupported FieldParams"

/--
  Parses a float as a string without trailing zeroes.
  Used to mirror the display of floats used within `sp1.md`.
-/
private def floatToFloatstr (f : Float) : String :=
  let s := f.toString
  -- only strip after a decimal point
  if s.contains '.' then
    let stripped := (s.dropEndWhile (· == '0')).toString
    -- avoid leaving a bare "1." with no fractional digits
    (stripped.dropEndWhile (· == '.')).toString
  else
    s

/--
  Mirrors Python's `get_report_parameter_lines` of Jagged circuits.
  **TODO** Generalize to other circuits.
-/
private def parseCircuitParams (circ: JaggedCfg) : IO String := do
  let mut outStr := ""

  let fieldDisplayName ← orExit (fieldParamsToDisplayname mapFieldParamsToDisplayname circ.densePCS.field)
  let floatRate ← orExit (rateToFloat mapFloatToRate circ.densePCS.ρ)
  let floatRateStr := floatToFloatstr floatRate

  /- Conditional strings -/
  let batchingStr := if circ.densePCS.powerBatch then "Powers" else "Affine"
  let grindcommitStr :=
    if circ.densePCS.grindCommit > 0 then
      s!"- Grinding commit phase (bits): {circ.densePCS.grindCommit}\n"
    else s!""

  outStr := outStr ++
  s!"- Proof system: {circ.proofSystName}\n" ++
  s!"- PCS: FRI\n" ++ -- **TODO** Generalize
  s!"- Hash size (bits): {circ.densePCS.hashBits}\n" ++
  s!"- Number of queries: {circ.densePCS.numQueries}\n" ++
  s!"- Grinding query phase (bits): {circ.densePCS.grindQuery}\n" ++
  /- Conditional grinding string -/
  s!"{grindcommitStr}" ++
  s!"- Field: {fieldDisplayName}\n" ++
  s!"- Rate (ρ): {floatRateStr}\n" ++
  s!"- Dense trace length: $2^\{{circ.densePCS.h}}$\n" ++
  s!"- Trace length: {circ.traceLength}\n" ++
  s!"- Trace width: {circ.traceWidth}\n" ++
  s!"- FRI rounds: {circ.densePCS.rounds}\n" ++
  s!"- FRI folding factors: {circ.densePCS.foldingFactors}\n" ++
  s!"- FRI early stop degree: {circ.densePCS.earlyStopDeg}\n" ++
  s!"- Dense batch size: {circ.densePCS.batchSize}\n" ++
  s!"- Batching: {batchingStr}\n"

  for lookup in circ.lookups do
    outStr := outStr ++
    s!"- Lookup (logup): {lookup.name}\n"

  pure (outStr)

/--
  Returns the range `[1, n]` in an alphabetically-sorted fashion.
  Mirrors the ordering of "commit round {i}"" used within `soundcalc`.

  Example (`n = 11`):
  `[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]`
  ->
  `[1, 10, 11, 2, 3, 4, 5, 6, 7, 8, 9]`
-/
private def rangeAlph (n : Nat) : List Nat :=
  (
    /- We drop `0` and range to `n` inclusive. -/
    (List.range (n+1)).tail.toArray.qsort
    (fun a b => decide (toString a < toString b))
  ).toList

/--
  Mirrors Python's `get_security_levels` for Jagged circuits.
-/
private def getSecurityLevels (circ: JaggedCfg) : IO (List (String × Nat)) := do
  let mut l : List (String × Nat) := []

  /- Minimum overall secBits -/
  l := l ++ [("total", (secBits circ.totalErr))]

  /- Lookup secBits -/
  for lookup in circ.lookups do
    l := l ++ [(lookup.name, (secBits lookup.errUB))]

  /- FRIConfig secBits: batching, commit round {i}, query phase -/
  let fcfg := circ.densePCS
  l := l ++ [("batching", (secBits (fcfg.batchingErr (UDR fcfg.field))))]

  for i in rangeAlph fcfg.rounds do
    let roundLabel := s!"commit round {i}"
    l := l ++ [(roundLabel, (secBits (fcfg.commitErr (UDR fcfg.field) (i-1))))]
  l := l ++ [("query phase", (secBits (fcfg.queryErr (UDR fcfg.field))))]

  /- Circuit secBits: reduce to dense PCS, zerocheck -/
  l := l ++ [("reduce to dense PCS", (secBits circ.reduceErr))]
  l := l ++ [("zerocheck", (secBits circ.zerocheckErr))]

  pure (l)

/--
  Parses the MD security table.
-/
private def parseSecurityLevels (circ: JaggedCfg) : IO String := do
  let mut headerStr := ""
  let mut sepStr := ""
  let mut secbitsStr := ""

  /- Contains tuples of the form (fieldName, secBits). -/
  let secLevels ← getSecurityLevels circ

  /- Hard-coded regime (sufficient for SP1)
     **TODO**: Generalize to JBR. -/
  headerStr := "| regime "
  sepStr := "| --- "
  secbitsStr := "| UDR "

  for elem in secLevels do
    headerStr := headerStr ++ s!"| {elem.1} "
    sepStr := sepStr ++ s!"| --- "
    secbitsStr := secbitsStr ++ s!"| {elem.2} "

  let outStr := headerStr ++ "|\n" ++ sepStr ++ "|\n" ++ secbitsStr ++ "|\n"

  pure (outStr)

/--
    Parses overview statistics for a list of circuits, including:

    - The name of the final circuit;
    - The proof size of the final circuit (in KiB);
    - The regime with highest minimum security (currently UDR only; JBR **TODO**);
    - The minimum bits of security across all circuits;
    - The name of the circuit with lowest security.

    Mirrors `soundcalc`'s `_compute_overview_stats` method.
-/
private def parseOverviewStats (zkvmcfg: ZkVMCfg) : IO String := do
  let circuits := zkvmcfg.circuits

  let mut outStr := ""
  /- If no circuits are found, we immediately return an empty string.
     The else branch leverages the negated condition `hne` (non-emptiness) to allow
     for safe calling of List methods requiring non-emptiness (`.head`, `.getLast`) -/
  if h : circuits.isEmpty then
    return ""
  else
    have hne : circuits ≠ [] := by simpa using h

    let firstCirc := circuits.head hne
    let lastCirc := circuits.getLast hne

    let finalProofSize := lastCirc.proofSizeWorst / KIB

    /- Evaluates the circuit with the worst overall secBits. -/
    let worstSecBitsCirc := circuits.foldl
      (fun worst c =>
        if secBits c.totalErr < secBits worst.totalErr then c
        else worst)
      firstCirc -- first circuit to accumulate over: always exists due to `hne`!

    /- Parsing helpers. -/
    let minSecBits := secBits worstSecBitsCirc.totalErr
    let worstSecBitsCircFmt := s!"[{worstSecBitsCirc.name}](#{worstSecBitsCirc.name})"
    let lastCircFmt := s!"[{lastCirc.name}](#{lastCirc.name})"

    outStr := outStr ++
      s!"| Metric | Value | Relevant circuit | Notes |\n" ++
      s!"| --- | --- | --- | --- |\n" ++
      s!"| Final bits of security | **{minSecBits} bits** | {worstSecBitsCircFmt} | Regime: UDR |\n" ++
      s!"| Final proof size (worst case) | **{finalProofSize} KiB** | {lastCircFmt} | |" ++
      s!"\n"
  pure (outStr)

private def appBanner : String :=
  s!"mdrenderer - a renderer tool that parses a zkEVM configuration in .toml\n" ++
  s!"into a .md report consistent with soundcalc's Python implementation.\n" ++
  s!"\n" ++
  s!"usage: lake exe mdrenderer\n" ++
  s!"|-> default inputs: ./SoundcalcIO/ZkVM/SP1.toml ./SoundcalcIO/ZkVM/SP1.md\n" ++
  s!"\n" ++
  s!"extended usage: lake exe mdrenderer <in-toml-path> <out-md-path>\n" ++
  s!"|-> supported circuits: SP1.toml\n"

/- *TODO*: generalize to other zkEVMs and circuits. -/
def main (args: List String): IO Unit := do
  IO.println appBanner
  if args.length == 1 then
    IO.eprintln "invalid inputs"; IO.Process.exit 1

  /- Default: `SP1.toml`, `SP1.md` relative to the project root path. -/
  let sp1TomlFile := args.getD 0 "./SoundcalcIO/ZkVM/SP1.toml"
  let sp1MdFile   := args.getD 1 "./SoundcalcIO/ZkVM/SP1.md"

  /- Incremental contents of `SP1.md`.
     We overwrite the file only if the parsing succeeds. -/
  let mut outStr := ""

  let zkvmcfg ← tomlToZkVMCfg sp1TomlFile

  outStr := outStr ++
  s!"# 📊 {zkvmcfg.name} (v{zkvmcfg.version})\n" ++
  s!"\n" ++
  s!"How to read this report:\n" ++
  s!"- Table rows correspond to security regimes\n" ++
  s!"- Table columns correspond to proof system components\n" ++
  s!"- Cells show bits of security per component\n" ++
  s!"- Proof size estimates are indicative (1 KiB = 1024 bytes)\n" ++
  s!"\n"

  /- If the zkVM hosts multiple circuits, we display a summary
     first (final proof size, least-secure circuit). -/
  if zkvmcfg.circuits.length > 1 then do
    let overviewStats ← parseOverviewStats zkvmcfg
    outStr := outStr ++
      s!"## zkVM Overview\n" ++
      s!"\n" ++
      s!"{overviewStats}" ++
      s!"\n"

    outStr := outStr ++
      s!"## Circuits\n" ++
      s!"\n"

    for circ in zkvmcfg.circuits do
      outStr := outStr ++
      s!"- [{circ.name}](#{circ.name})\n"


  if zkvmcfg.circuits.length > 0 then do
    for circ in zkvmcfg.circuits do
      outStr := outStr ++
      s!"\n" ++
      s!"## {circ.name}\n" ++
      s!"\n"

      /- Circuit parameters portion -/
      let circParams ← parseCircuitParams circ
      outStr := outStr ++
      s!"**Parameters:**\n" ++
      s!"{circParams}" ++
      s!"\n"

      /- Proof size portion -/
      let proofSizeExpStr := s!"{circ.proofSizeExp/KIB} KiB (expected)"
      let proofSizeWorstStr := s!"{circ.proofSizeWorst/KIB} KiB (worst case)"

      outStr := outStr ++
      s!"**Proof Size:** {proofSizeExpStr} / {proofSizeWorstStr}\n" ++
      s!"\n"

      /- Security table portion -/
      let securityTable ← parseSecurityLevels circ

      outStr := outStr ++
      s!"{securityTable}" ++
      s!"\n"
    else do
      outStr := outStr ++
      s!"No circuits available.\n"

  IO.FS.writeFile sp1MdFile outStr
  IO.println s!"Successfully parsed {sp1TomlFile} to {sp1MdFile}!"
  IO.Process.exit 0

end SoundcalcIO.MdRenderer

/-
  We preserve the namespace while redeclaring the main.
  This enables the following:
  `lean exe mdrenderer`
-/
def main := SoundcalcIO.MdRenderer.main
