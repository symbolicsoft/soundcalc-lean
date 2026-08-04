import Soundcalc
import SoundcalcIO.TomlParser
import SoundcalcIO.MdRenderer.Circuit

open Soundcalc
open SoundcalcIO
open SoundcalcIO.MdRenderer

namespace SoundcalcIO.MdRenderer

/--
  Renders the markdown security table of a generic
  Circuit, following soundcalc's reference.
-/
private def renderSecurityLevels (c: Circuit) : IO String := do
  let mut headerStr := "| regime "
  let mut sepStr := "| --- "
  let mut secbitsUDRStr := "| UDR "
  let mut secbitsJBRStr := "| JBR "

  /- Contains tuples of the form (fieldName, secBits). -/
  let secLevelsUDR ← c.secParamsUDR
  let secLevelsJBR ← c.secParamsJBR

  let isUDR := c.isUDR
  let isJBR := c.isJBR

  /- **FEAT TODO** Revisit once an appropriate generalization
    of fields is introduced at circuit-level. -/
  if isUDR then
    for elem in secLevelsUDR do
      headerStr := headerStr ++ s!"| {elem.1} "
      sepStr := sepStr ++ s!"| --- "
      secbitsUDRStr := secbitsUDRStr ++ s!"| {elem.2} "

    /- If the circuit does not support JBR, the loop below does not run. -/
    for elem in secLevelsJBR do
      secbitsJBRStr := secbitsJBRStr ++ s!"| {elem.2} "

  else if isJBR then
    for elem in secLevelsJBR do
      headerStr := headerStr ++ s!"| {elem.1} "
      sepStr := sepStr ++ s!"| --- "
      secbitsJBRStr := secbitsJBRStr ++ s!"| {elem.2} "

    /- If the circuit does not support UDR, the loop below does not run. -/
    for elem in secLevelsUDR do
      secbitsUDRStr := secbitsUDRStr ++ s!"| {elem.2} "

  let outStr := headerStr ++
    "|\n" ++
    sepStr ++
    "|\n"
  let outStr :=
    if !isUDR then outStr
    else outStr ++ secbitsUDRStr ++ "|\n"
  let outStr :=
    if !isJBR then outStr
    else outStr ++ secbitsJBRStr ++ "|\n"

  pure outStr

/--
    Parses overview statistics of a generic zkVM, including:

    - The name of the final circuit;
    - The proof size of the final circuit (in KiB);
    - The regime with highest minimum security;
    - The minimum bits of security across all circuits;
    - The name of the circuit with lowest security.

    Mirrors `soundcalc`'s `_compute_overview_stats` method.
-/
private def renderOverviewStats (vm: ZkVM) : IO String := do
  let vm_circuits := vm.circuits

  let mut outStr := ""
  /- If no circuits are found, we immediately return an empty string.
     The else branch leverages the negated condition `hne` (non-emptiness) to allow
     for safe calling of List methods requiring non-emptiness (`.head`, `.getLast`) -/
  if h : vm_circuits.isEmpty then
    return ""
  else
    have hne : vm_circuits ≠ [] := by simpa using h

    let vm_firstCirc := vm_circuits.head hne
    let vm_lastCirc  := vm_circuits.getLast hne

    let vm_finalProofSize := vm_lastCirc.proofSizeWorst / KIB

    /-
      We identify the circuit that has the worst overall secBits, following `soundcalc`'s semantics:
      - If no global regime is found, each circuit contributes to the overall zkVM with its best regime.
        This yields a "mixed" regime.
      - If exactly one global regime is found, we output the circuit with the worst security bits for that regime.
      - If both global regimes are found, we output the circuit with the worst security bits for the best regime.
      Ref: https://github.com/ethereum/soundcalc/blob/cee252916d6d9f8579c3d41b2eddb946c329d743/soundcalc/report_md.py#L86

      Current support: UDR, JBR, mirroring `soundcalc`.
      **TODO** Revisit whenever regimes are generalized.
    -/
    let vm_globalUDR := vm_circuits.foldl (
      fun acc c => c.isUDR && acc
    ) (vm_firstCirc.isUDR)

    let vm_globalJBR := vm_circuits.foldl (
      fun acc c => c.isJBR && acc
    ) (vm_firstCirc.isJBR)

    let (worstRegimeCirc, bestRegimeSecBits, bestRegime) := match vm_globalUDR, vm_globalJBR with
      /- If no global regime is supported, each circuit contributes with its best regime.
         The final regime is denoted as "mixed".-/
      | false, false =>
        let worstCirc := vm_circuits.foldl
          (fun (worst c: Circuit) =>
            if max c.totalSecBitsUDR c.totalSecBitsJBR < max worst.totalSecBitsUDR worst.totalSecBitsJBR then c
            else worst)
          vm_firstCirc -- first circuit to accumulate over: always exists due to `hne`!

        let bestRegimeSecBits := max (worstCirc.totalSecBitsUDR) (worstCirc.totalSecBitsJBR)
        (worstCirc, bestRegimeSecBits, "mixed")
      /- In what's below, at least one global regime is defined. -/
      | globalUDR, globalJBR =>
        /- Evaluates the circuit with the worst overall secBits using UDR. -/
        let worstCircUDR := vm_circuits.foldl
          (fun (worst c: Circuit) =>
            if c.totalSecBitsUDR < worst.totalSecBitsUDR then c
            else worst)
          vm_firstCirc

        let minSecBitsUDR := worstCircUDR.totalSecBitsUDR

        /- Evaluates the circuit with the worst overall secBits using JBR. -/
        let worstCircJBR := vm_circuits.foldl
          (fun (worst c: Circuit) =>
            if c.totalSecBitsJBR < worst.totalSecBitsJBR then c
            else worst)
          vm_firstCirc

        let minSecBitsJBR := worstCircJBR.totalSecBitsJBR

        /- If all the circuits in the zkVM have exactly one shared regime, we pick that.
         Otherwise, we pick the best among the two. -/
        if globalUDR && globalJBR then
          if minSecBitsUDR > minSecBitsJBR then (worstCircUDR, minSecBitsUDR, "UDR")
          else (worstCircJBR, minSecBitsJBR, "JBR")
        else if globalUDR then (worstCircUDR, minSecBitsUDR, "UDR")
        else (worstCircJBR, minSecBitsJBR, "JBR")

    /- Parsing helpers. -/
    let minSecBits := bestRegimeSecBits
    let worstRegimeCircName := worstRegimeCirc.name
    let worstSecBitsLink := s!"{circLinkFromName worstRegimeCircName}"
    let worstSecBitsCircFmt := s!"[{worstRegimeCircName}]{worstSecBitsLink}"
    let lastCircName := vm_lastCirc.name
    let lastCircLink := s!"{circLinkFromName lastCircName}"
    let lastCircFmt := s!"[{lastCircName}]{lastCircLink}"

    outStr := outStr ++
      s!"| Metric | Value | Relevant circuit | Notes |\n" ++
      s!"| --- | --- | --- | --- |\n" ++
      s!"| Final bits of security | **{minSecBits} bits** | {worstSecBitsCircFmt} | Regime: {bestRegime} |\n" ++
      s!"| Final proof size (worst case) | **{vm_finalProofSize} KiB** | {lastCircFmt} | |" ++
      s!"\n"
  pure outStr

/--
  Renders a generic VM.
-/
private def renderVMStr (vm: ZkVM) : IO String := do
  /- Incremental contents of the output MD file. We overwrite the
     (potentially exisiting) file only if the parsing succeeds. -/
  let mut outStr := ""

  let vm_name := vm.name
  let vm_version := match vm.version with
  | some s => s!" (v{s})"
  | none => ""
  let vm_circuits := vm.circuits
  let vm_circLen  := vm_circuits.length

  outStr := outStr ++
  s!"# 📊 {vm_name}{vm_version}\n" ++
  s!"\n" ++
  s!"How to read this report:\n" ++
  s!"- Table rows correspond to security regimes\n" ++
  s!"- Table columns correspond to proof system components\n" ++
  s!"- Cells show bits of security per component\n" ++
  s!"- Proof size estimates are indicative (1 KiB = 1024 bytes)\n" ++
  s!"\n"

  /- If the zkVM hosts multiple circuits, we display a summary
     first (final proof size, least-secure circuit). -/

  if vm_circLen > 1 then do
    let overviewStats ← renderOverviewStats vm
    outStr := outStr ++
      s!"## zkVM Overview\n" ++
      s!"\n" ++
      s!"{overviewStats}" ++
      s!"\n"

    outStr := outStr ++
      s!"## Circuits\n" ++
      s!"\n"

    for circ in vm_circuits do
      let circ_name := circ.name
      let circ_link := circLinkFromName circ_name
      outStr := outStr ++
      s!"- [{circ_name}]{circ_link}\n"

  if vm_circLen > 0 then do
    for circ in vm_circuits do
      let circ_name := circ.name

      /- We add a ## header only if more than a circuit is specified. -/
      if vm_circLen > 1 then do
        outStr := outStr ++
        s!"\n" ++
        s!"## {circ_name}\n" ++
        s!"\n"

      /- Circuit parameters portion -/
      let circ_params ← circ.circParamsStr
      outStr := outStr ++
      s!"**Parameters:**\n" ++
      s!"{circ_params}" ++
      s!"\n"

      /- Proof size portion -/
      let proofSizeExpStr := s!"{circ.proofSizeExp/KIB} KiB (expected)"
      let proofSizeWorstStr := s!"{circ.proofSizeWorst/KIB} KiB (worst case)"

      outStr := outStr ++
      s!"**Proof Size:** {proofSizeExpStr} / {proofSizeWorstStr}\n" ++
      s!"\n"

      /- Security table portion -/
      let circ_security_levels ← renderSecurityLevels circ

      outStr := outStr ++
      s!"{circ_security_levels}"

      /- We append a trailing space only if more than a circuit is available.
         Reproduces soundcalc's behaviour. -/
      if vm_circLen > 1 then
        outStr := outStr ++ "\n"
    else do
      outStr := outStr ++
      s!"No circuits available.\n"
  pure outStr

/--
  Renders a generic zkVM as a into a
  `.md` report located at `outMdFile`.
-/
private def renderMd (inVM: ZkVM)(outMdFile: String) : IO Unit := do
  let zkVMreport ← renderVMStr inVM
  IO.FS.writeFile outMdFile zkVMreport

private def appBanner : String :=
  s!"mdrenderer - a renderer tool that parses a zkEVM configuration in .toml\n" ++
  s!"into a .md report consistent with soundcalc's Python implementation.\n" ++
  s!"\n" ++
  s!"usage: lake exe mdrenderer\n" ++
  s!"|-> default behaviour: parse all supported zkVMs. \n" ++
  s!"|-> supported zkVMs: sp1, airbender, openvm, pico, zisk, venus, openvm2, zkdtvm\n" ++
  s!"\n" ++
  s!"extended usage: lake exe mdrenderer <in-toml-path> <out-md-path>\n" ++
  s!"|-> render one specific zkVM.\n"

/--
  Currently-supported VMs.
-/
def supportedvms : List String := [
  "sp1",                                             -- Jagged
  "airbender", "openvm", "pico", "zisk", "venus",    -- DEEP-ALI
  "openvm2",                                         -- SWIRL
  "zkdtvm"
]

def main (args: List String): IO Unit := do
  IO.println appBanner

  /- Default: we parse all the supported zkVMs. -/
  if args.length = 0 then
    let relPath := "./SoundcalcIO/ZkVM"

    for vmname in supportedvms do
       let inTomlFile := s!"{relPath}/Ref/{vmname}.toml"
       let outMdFile  := s!"{relPath}/{vmname}.md"

       let zkVM ← tomlToZkVM inTomlFile
       renderMd zkVM outMdFile
       IO.println s!"Successfully parsed {inTomlFile} to {outMdFile}!"

  /- Extended usage: specify and render one specific zkVM. -/
  else if h: args.length = 2 then
    /- The arguments below always exist. -/
    let inTomlFile := args[0]'(by omega)
    let outMdFile  := args[1]'(by omega)

    let zkVM ← tomlToZkVM inTomlFile
    renderMd zkVM outMdFile
    IO.println s!"Successfully parsed {inTomlFile} to {outMdFile}!"
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
