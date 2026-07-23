import Soundcalc
import SoundcalcIO.TomlParser
import SoundcalcIO.Common

open Soundcalc
open SoundcalcIO

namespace SoundcalcIO.MdRenderer

/-!
  Auxiliary methods shared between zkVMs.
-/

/--
  Maps supported `FieldParams` to their matching display name.
-/
private def mapFieldParamsToDisplayname : List (FieldParams × String) := [
  (koalaBear4, "KoalaBear⁴"),
  (mersenne31_4, "M31⁴"),
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
  Derives a circuit markdown link from a circuit name.
-/
private def circLinkFromName (name: String) : String :=
  "(#" ++ name.toLower.replace " " "-" ++ ")"

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
  Shared introductory banner among different zkVM reports.
-/
private def reportBannerStr : String :=
  s!"How to read this report:\n" ++
  s!"- Table rows correspond to security regimes\n" ++
  s!"- Table columns correspond to proof system components\n" ++
  s!"- Cells show bits of security per component\n" ++
  s!"- Proof size estimates are indicative (1 KiB = 1024 bytes)\n" ++
  s!"\n"

/-!
  JaggedVM rendering methods.
-/

/--
  Mirrors Python's `get_report_parameter_lines` for Jagged circuits.
-/
private def jagged_renderCircParams (c: JaggedCfg) : IO String := do
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
private def jagged_getSecLevels (c: JaggedCfg) : IO (List (String × Nat)) := do
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

/--
  Renders the MD security table of a Jagged circuit.
-/
private def jagged_renderSecLevels (c: JaggedCfg) : IO String := do
  let mut headerStr := ""
  let mut sepStr := ""
  let mut secbitsStr := ""

  /- Contains tuples of the form (fieldName, secBits). -/
  let secLevels ← jagged_getSecLevels c

  /- UDR-only (sufficient for SP1) -/
  headerStr := "| regime "
  sepStr := "| --- "
  secbitsStr := "| UDR "

  for elem in secLevels do
    headerStr := headerStr ++ s!"| {elem.1} "
    sepStr := sepStr ++ s!"| --- "
    secbitsStr := secbitsStr ++ s!"| {elem.2} "

  let outStr := headerStr ++
    "|\n" ++
    sepStr ++
    "|\n" ++
    secbitsStr ++
    "|\n"

  pure outStr

/--
    Parses overview statistics for a JaggedVM, including:

    - The name of the final circuit;
    - The proof size of the final circuit (in KiB);
    - The regime with highest minimum security (UDR only for SP1);
    - The minimum bits of security across all circuits;
    - The name of the circuit with lowest security.

    Mirrors `soundcalc`'s `_compute_overview_stats` method.
-/
private def jagged_renderOverviewStats (vm: JaggedVM) : IO String := do
  let circuits := vm.circuits

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
    let worstSecBitsLink := s!"{circLinkFromName worstSecBitsCirc.name}"
    let worstSecBitsCircFmt := s!"[{worstSecBitsCirc.name}]{worstSecBitsLink}"
    let lastCircLink := s!"{circLinkFromName lastCirc.name}"
    let lastCircFmt := s!"[{lastCirc.name}]{lastCircLink}"

    outStr := outStr ++
      s!"| Metric | Value | Relevant circuit | Notes |\n" ++
      s!"| --- | --- | --- | --- |\n" ++
      s!"| Final bits of security | **{minSecBits} bits** | {worstSecBitsCircFmt} | Regime: UDR |\n" ++
      s!"| Final proof size (worst case) | **{finalProofSize} KiB** | {lastCircFmt} | |" ++
      s!"\n"
  pure outStr

/--
  Renders a Jagged zkVM parsed from an input .toml file
  located at `inTomlFile` into a .md report at `outMdFile`
-/
private def jagged_renderVM (inTomlFile: String)(outMdFile: String) : IO Unit := do
  /- Incremental contents of the output MD file. We overwrite the
     (potentially exisiting) file only if the parsing succeeds. -/
  let mut outStr := ""

  let jaggedVM ← tomlToJaggedVM inTomlFile
  let zkvmVer := match jaggedVM.version with
  | some s => s!" (v{s})"
  | none => ""

  outStr := outStr ++
  s!"# 📊 {jaggedVM.name}{zkvmVer}\n" ++
  s!"\n" ++
  s!"{reportBannerStr}"

  let circCnt := jaggedVM.circuits.length
  /- If the zkVM hosts multiple circuits, we display a summary
     first (final proof size, least-secure circuit). -/
  if circCnt > 1 then do
    let overviewStats ← jagged_renderOverviewStats jaggedVM
    outStr := outStr ++
      s!"## zkVM Overview\n" ++
      s!"\n" ++
      s!"{overviewStats}" ++
      s!"\n"

    outStr := outStr ++
      s!"## Circuits\n" ++
      s!"\n"

    for circ in jaggedVM.circuits do
      let circLink := circLinkFromName circ.name
      outStr := outStr ++
      s!"- [{circ.name}]{circLink}\n"

  if circCnt > 0 then do
    for circ in jaggedVM.circuits do

      /- We add a ## header only if more than a circuit is specified. -/
      if circCnt > 1 then do
        outStr := outStr ++
        s!"\n" ++
        s!"## {circ.name}\n" ++
        s!"\n"

      /- Circuit parameters portion -/
      let circParams ← jagged_renderCircParams circ
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
      let securityTable ← jagged_renderSecLevels circ

      outStr := outStr ++
      s!"{securityTable}"

      /- We append a trailing space only if more than a circuit is available.
         Reproduces soundcalc's behaviour. -/
      if circCnt > 1 then
        outStr := outStr ++ "\n"
    else do
      outStr := outStr ++
      s!"No circuits available.\n"

  IO.FS.writeFile outMdFile outStr
  IO.println s!"Successfully parsed {inTomlFile} to {outMdFile}!"


/-!
  DeepAliVM rendering methods.
-/

/--
  Mirrors Python's `get_report_parameter_lines` for DEEP-ALI circuits.
-/
private def deepali_renderCircParams (c: DeepAliCfg) : IO String := do
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
  /- Conditional grinding strings -/
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
private def deepali_getSecLevels (c: DeepAliCfg) (R: Regime) : IO (List (String × Nat)) := do
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

/--
  Parses the MD security table of a DEEP-ALI circuit.
-/
private def deepali_renderSecurityLevels (c: DeepAliCfg) : IO String := do
  let mut headerStr := ""
  let mut sepStr := ""
  let mut secbitsUDRStr := ""
  let mut secbitsJBRStr := ""

  /- Following our Airbender characterization (`Soundcalc/ZkVM/Airbender.lean`),
     we keep `η = ρ/20`, `g = 2^40` as the pinned gap and sqrt granularity.
     **TODO** Use the generic η field once it's defined. -/
  let circ_UDR : Regime := UDR c.field
  let circ_JBR : Regime := JBR c.field (c.densePCS.ρ/20) (2^40)

  /- Contains tuples of the form (fieldName, secBits). -/
  let secLevelsUDR ← deepali_getSecLevels c circ_UDR
  let secLevelsJBR ← deepali_getSecLevels c circ_JBR

  /- Hard-coded supported regimes -/
  headerStr := "| regime "
  sepStr := "| --- "
  secbitsUDRStr := "| UDR "
  secbitsJBRStr := "| JBR "

  for elem in secLevelsUDR do
    headerStr := headerStr ++ s!"| {elem.1} "
    sepStr := sepStr ++ s!"| --- "
    secbitsUDRStr := secbitsUDRStr ++ s!"| {elem.2} "

  for elem in secLevelsJBR do
    secbitsJBRStr := secbitsJBRStr ++ s!"| {elem.2} "

  let outStr := headerStr ++
    "|\n" ++
    sepStr ++
    "|\n" ++
    secbitsUDRStr ++
    "|\n" ++
    secbitsJBRStr ++
    "|\n"

  pure outStr

/--
    Parses overview statistics for a DEEP-ALI VM, including:

    - The name of the final circuit;
    - The proof size of the final circuit (in KiB);
    - The regime with highest minimum security;
    - The minimum bits of security across all circuits;
    - The name of the circuit with lowest security.

    Mirrors `soundcalc`'s `_compute_overview_stats` method.
-/
private def deepali_renderOverviewStats (vm: DeepAliVM) : IO String := do
  let circuits := vm.circuits

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

    /- Evaluates the circuit with the worst overall secBits using UDR. -/
    let worstSecBitsCircUDR := circuits.foldl
      (fun worst c =>
        let circ_UDR : Regime := UDR c.field
        if secBits (c.totalErr circ_UDR) < secBits (worst.totalErr circ_UDR) then c
        else worst)
      firstCirc -- first circuit to accumulate over: always exists due to `hne`!

    /- Evaluates the circuit with the worst overall secBits using JBR. -/
    let worstSecBitsCircJBR := circuits.foldl
      (fun worst c =>
      /- Following our Airbender characterization (`Soundcalc/ZkVM/Airbender.lean`),
         we keep `η = ρ/20`, `g = 2^40` as the pinned gap and sqrt granularity.
        **TODO** Use the generic η field once it's defined. -/
        let circ_JBR : Regime := JBR c.field (c.densePCS.ρ/20) (2^40)
        if secBits (c.totalErr circ_JBR) < secBits (worst.totalErr circ_JBR) then c
        else worst)
      firstCirc -- first circuit to accumulate over: always exists due to `hne`!

    let worstCircUDR : Regime := UDR worstSecBitsCircUDR.field
    let worstCircJBR : Regime := JBR worstSecBitsCircJBR.field (worstSecBitsCircJBR.densePCS.ρ/20) (2^40)

    let minSecBitsUDR := secBits (worstSecBitsCircUDR.totalErr worstCircUDR)
    let minSecBitsJBR := secBits (worstSecBitsCircJBR.totalErr worstCircJBR)

    let (bestRegimeCirc, bestRegimeSecBits, bestRegime) :=
      if minSecBitsUDR > minSecBitsJBR then (worstSecBitsCircUDR, minSecBitsUDR, "UDR")
      else (worstSecBitsCircJBR, minSecBitsJBR, "JBR")

    /- Parsing helpers. -/
    let minSecBits := bestRegimeSecBits
    let worstSecBitsLink := s!"{circLinkFromName bestRegimeCirc.name}"
    let worstSecBitsCircFmt := s!"[{bestRegimeCirc.name}]{worstSecBitsLink}"
    let lastCircLink := s!"{circLinkFromName lastCirc.name}"
    let lastCircFmt := s!"[{lastCirc.name}]{lastCircLink}"

    outStr := outStr ++
      s!"| Metric | Value | Relevant circuit | Notes |\n" ++
      s!"| --- | --- | --- | --- |\n" ++
      s!"| Final bits of security | **{minSecBits} bits** | {worstSecBitsCircFmt} | Regime: {bestRegime} |\n" ++
      s!"| Final proof size (worst case) | **{finalProofSize} KiB** | {lastCircFmt} | |" ++
      s!"\n"
  pure outStr

/--
  Renders a DEEP-ALI zkVM parsed from an input .toml file
  located at `inTomlFile` into a .md report at `outMdFile`
-/
private def deepali_renderVM (inTomlFile: String)(outMdFile: String) : IO Unit := do
  /- Incremental contents of the output MD file. We overwrite the
     (potentially exisiting) file only if the parsing succeeds. -/
  let mut outStr := ""

  let deepAliVM ← tomlToDeepAliVM inTomlFile
  let zkvmVer := match deepAliVM.version with
  | some s => s!" (v{s})"
  | none => ""

  outStr := outStr ++
  s!"# 📊 {deepAliVM.name}{zkvmVer}\n" ++
  s!"\n" ++
  s!"{reportBannerStr}"

  let circCnt := deepAliVM.circuits.length
  /- If the zkVM hosts multiple circuits, we display a summary
     first (final proof size, least-secure circuit). -/
  if circCnt > 1 then do
    let overviewStats ← deepali_renderOverviewStats deepAliVM
    outStr := outStr ++
      s!"## zkVM Overview\n" ++
      s!"\n" ++
      s!"{overviewStats}" ++
      s!"\n"

    outStr := outStr ++
      s!"## Circuits\n" ++
      s!"\n"

    for circ in deepAliVM.circuits do
      let circLink := circLinkFromName circ.name
      outStr := outStr ++
      s!"- [{circ.name}]{circLink}\n"

  if circCnt > 0 then do
    for circ in deepAliVM.circuits do

      /- We add a ## header only if more than a circuit is specified. -/
      if circCnt > 1 then do
        outStr := outStr ++
        s!"\n" ++
        s!"## {circ.name}\n" ++
        s!"\n"

      /- Circuit parameters portion -/
      let circParams ← deepali_renderCircParams circ
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
      let securityTable ← deepali_renderSecurityLevels circ

      outStr := outStr ++
      s!"{securityTable}"

      /- We append a trailing space only if more than a circuit is available.
         Reproduces soundcalc's behaviour. -/
      if circCnt > 1 then
        outStr := outStr ++ "\n"
    else do
      outStr := outStr ++
      s!"No circuits available.\n"

  IO.FS.writeFile outMdFile outStr
  IO.println s!"Successfully parsed {inTomlFile} to {outMdFile}!"

private def appBanner : String :=
  s!"mdrenderer - a renderer tool that parses a zkEVM configuration in .toml\n" ++
  s!"into a .md report consistent with soundcalc's Python implementation.\n" ++
  s!"\n" ++
  s!"usage: lake exe mdrenderer\n" ++
  s!"|-> default behaviour: parse all supported zkVMs. \n" ++
  s!"|-> supported zkVMs: sp1.toml, airbender.toml\n" ++
  s!"\n" ++
  s!"extended usage: lake exe mdrenderer <in-toml-path> <out-md-path>\n"

/--
  Currently-supported VMs:
  - JaggedVM: SP1
  - DeepAliVM: Airbender
-/
def main (args: List String): IO Unit := do
  IO.println appBanner

  /- Default: we parse all the supported zkVMs. -/
  if args.length = 0 then
    let relPath := "./SoundcalcIO/ZkVM"
    jagged_renderVM  s!"{relPath}/Ref/sp1.toml" s!"{relPath}/sp1.md"
    deepali_renderVM s!"{relPath}/Ref/airbender.toml" s!"{relPath}/airbender.md"
  /- Extended usage: specify and render one specific zkVM. -/
  else if h: args.length = 2 then
    /- The arguments below always exist. -/
    let inTomlFile := args[0]'(by omega)
    let outMdFile  := args[1]'(by omega)

    let VMFamily ← tomlToVMFamily inTomlFile
    match VMFamily with
      | "JAGGED"    => jagged_renderVM inTomlFile outMdFile
      | "FRI_STARK" => deepali_renderVM inTomlFile outMdFile
      | _           => IO.eprintln "Unsupported zkVM family."; IO.Process.exit 1
  else
    IO.eprintln "Invalid inputs."; IO.Process.exit 1

  IO.Process.exit 0

end SoundcalcIO.MdRenderer

/-
  We preserve the namespace while redeclaring the main.
  This enables the following:
  `lean exe mdrenderer`
-/
def main := SoundcalcIO.MdRenderer.main
