import Soundcalc
import SoundcalcIO.TomlParser
import SoundcalcIO.Common

open Soundcalc
open SoundcalcIO

namespace SoundcalcIO.LeanEmitter

/-!
  # `SoundcalcIO.LeanEmitter` —  (roadmap S7; partial)
    A parsing tool that generates `SP1.lean` from `sp1.toml`.
    The `.lean` file wraps together all the structures defined in companion
    files (`JaggedCfg`, `LookupCfg`, `FRIConfig`), enabling formal arithmetic
    verification of the `sp1.md` report of `soundcalc` by means of cell-wise
    evaluations of the security bits table, as well as reported proof sizes
    (both worst-case and expected).

    usage: `lean exe leanemitter`

  *TODOs.* While the structure of the current parser is general, its instantiation
  is tailored to SP1 only. Extensions to other zkEVMs will be addressed as they
  are introduced within the roadmap.
-/

/--
  Header string declaring the imports of `SP1.lean`.
-/
private def getSP1ImportStr : String :=
    s!"/- Automatically generated from `LeanEmitter.lean` and `sp1.toml`. -/\n" ++
    s!"\n" ++
    s!"import Mathlib\n" ++
    s!"import Soundcalc\n" ++
    s!"\n" ++
    s!"open Soundcalc\n" ++
    s!"\n"

/-
  The values below are for now manually parsed from `soundcalc`'s `sp1.md`
  (https://github.com/ethereum/soundcalc/blob/main/reports/sp1.md).
  *TODO*: Lots of polishing; possibly, automatic parsing from the `.md`.
-/

private def getSP1CoreReportStr : String :=
  "/- Sanity check against `sp1.md`'s reported values.-/\n" ++
  "\n" ++
  "/- **Security bits table** -/\n" ++
  "example : secBits (SP1_core_jagged.totalErr) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits (SP1_core_lookup_lookup.errUB) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits (SP1_core_FRI.batchingErr (UDR koalaBear4)) = 104 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 0) = 103 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 9) = 112 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 10) = 113 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 11) = 114 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 12) = 115 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 13) = 116 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 14) = 117 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 15) = 118 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 16) = 119 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 17) = 120 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 18) = 121 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 1) = 104 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 19) = 121 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 20) = 122 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 2) = 105 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 3) = 106 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 4) = 107 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 5) = 108 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 6) = 109 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 7) = 110 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.commitErr (UDR koalaBear4) 8) = 111 := by native_decide\n" ++
  "example : secBits (SP1_core_FRI.queryErr (UDR koalaBear4)) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits SP1_core_jagged.reduceErr = 116 := by native_decide\n" ++
  "example : secBits SP1_core_jagged.zerocheckErr = 112 := by native_decide\n" ++
  "\n" ++
  "/- **Proof sizes (FRI-only, Jagged circuit)** -/\n" ++
  "example : sp1CoreFRI.proofSizeExp          / KIB = 913  := by native_decide\n" ++
  "example : sp1CoreFRI.proofSizeWorst        / KIB = 1474 := by native_decide\n" ++
  "\n" ++
  "example : sp1CoreJagged.proofSizeExp       / KIB = 918  := by native_decide\n" ++
  "example : sp1CoreJagged.proofSizeWorst     / KIB = 1479 := by native_decide\n" ++
  "\n"

private def getSP1CompressReportStr : String :=
  "/- Sanity check against `sp1.md`'s reported values.-/\n" ++
  "\n" ++
  "/- **Security bits table** -/\n" ++
  "example : secBits (SP1_compress_jagged.totalErr) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits (SP1_compress_lookup_lookup.errUB) = 107 := by native_decide\n" ++
  "\n" ++
  "example : secBits (SP1_compress_FRI.batchingErr (UDR koalaBear4)) = 105 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 0) = 104 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 9) = 113 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 10) = 114 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 11) = 115 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 12) = 116 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 13) = 117 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 14) = 118 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 15) = 119 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 16) = 120 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 17) = 121 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 18) = 121 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 1) = 105 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 19) = 122 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 2) = 106 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 3) = 107 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 4) = 108 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 5) = 109 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 6) = 110 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 7) = 111 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.commitErr (UDR koalaBear4) 8) = 112 := by native_decide\n" ++
  "example : secBits (SP1_compress_FRI.queryErr (UDR koalaBear4)) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits SP1_compress_jagged.reduceErr = 116 := by native_decide\n" ++
  "example : secBits SP1_compress_jagged.zerocheckErr = 115 := by native_decide\n" ++
  "\n" ++
  "/- **Proof sizes (FRI-only, Jagged circuit)** -/\n" ++
  "example : sp1CompressFRI.proofSizeExp      / KIB = 730  := by native_decide\n" ++
  "example : sp1CompressFRI.proofSizeWorst    / KIB = 1261 := by native_decide\n" ++
  "\n" ++
  "example : sp1CompressJagged.proofSizeExp   / KIB = 735  := by native_decide\n" ++
  "example : sp1CompressJagged.proofSizeWorst / KIB = 1267 := by native_decide\n" ++
  "\n"


private def getSP1ShrinkReportStr : String :=
  "/- Sanity check against `sp1.md`'s reported values.-/\n" ++
  "\n" ++
  "/- **Security bits table** -/\n" ++
  "example : secBits (SP1_shrink_jagged.totalErr) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits (SP1_shrink_lookup_lookup.errUB) = 109 := by native_decide\n" ++
  "\n" ++
  "example : secBits (SP1_shrink_FRI.batchingErr (UDR koalaBear4)) = 106 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 0) = 105 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 9) = 114 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 10) = 115 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 11) = 116 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 12) = 117 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 13) = 118 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 14) = 119 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 15) = 120 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 16) = 120 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 17) = 121 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 1) = 106 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 2) = 107 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 3) = 108 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 4) = 109 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 5) = 110 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 6) = 111 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 7) = 112 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.commitErr (UDR koalaBear4) 8) = 113 := by native_decide\n" ++
  "example : secBits (SP1_shrink_FRI.queryErr (UDR koalaBear4)) = 100 := by native_decide\n" ++
  "\n" ++
  "example : secBits SP1_shrink_jagged.reduceErr = 116 := by native_decide\n" ++
  "example : secBits SP1_shrink_jagged.zerocheckErr = 115 := by native_decide\n" ++
  "\n" ++
  "/- **Proof sizes (FRI-only, Jagged circuit)** -/\n" ++
  "example : sp1ShrinkFRI.proofSizeExp        / KIB = 524  := by native_decide\n" ++
  "example : sp1ShrinkFRI.proofSizeWorst      / KIB = 882  := by native_decide\n" ++
  "\n" ++
  "example : sp1ShrinkJagged.proofSizeExp     / KIB = 529  := by native_decide\n" ++
  "example : sp1ShrinkJagged.proofSizeWorst   / KIB = 887  := by native_decide\n" ++
  "\n"

/--
  Contains theorems tying together the hand-written configs in
  `Soundcalc/ZkVM/SP1.lean` with the ones parsed from `sp1.toml`. -/
private def consistencyProofs : String :=
  "/- Theorems tying together the hand-written configs in\n" ++
  "   `Soundcalc/ZkVM/SP1.lean` with the ones parsed from `sp1.toml`.-/\n" ++
  "example : SP1_core_jagged = sp1CoreJagged := by rfl\n" ++
  "example : SP1_compress_jagged = sp1CompressJagged := by rfl\n" ++
  "example : SP1_shrink_jagged = sp1ShrinkJagged := by rfl"


private def appBanner : String :=
  s!"leanemitter - a parsing tool that parses a zkEVM configuration in .toml\n" ++
  s!"into an equivalent .lean file verifiable by Soundcalc.\n" ++
  s!"\n" ++
  s!"usage: lake exe leanemitter\n" ++
  s!"|-> default inputs: ./SoundcalcIO/ZkVM/Ref/sp1.toml ./SoundcalcIO/ZkVM/SP1.lean\n" ++
  s!"\n" ++
  s!"extended usage: lake exe leanemitter <in-toml-path> <out-lean-path>\n" ++
  s!"|-> supported zkVMs: sp1.toml\n"

/-
  Maps supported `FieldParams` to their matching variable name.
-/
private def mapFieldParamsToVarname : List (FieldParams × String) := [
  (koalaBear4, "koalaBear4"),
]

private def fieldParamsToVarname (map : List (FieldParams × String)) (fp : FieldParams) : Except String String :=
  match map.lookup fp with
  | some s => .ok s
  | none   => .error s!"unsupported FieldParams"

/- *TODO*: generalize to other zkEVMs, circuits, and related fields to parse. -/
def main (args: List String): IO Unit := do
  IO.println appBanner
  if args.length == 1 then
    IO.eprintln "invalid inputs"; IO.Process.exit 1

  /- Default: `sp1.toml`, `SP1.lean` relative to the project root path. -/
  let sp1TomlFile := args.getD 0 "./SoundcalcIO/ZkVM/Ref/sp1.toml"
  let sp1LeanFile := args.getD 1 "./SoundcalcIO/ZkVM/SP1.lean"

  let zkVM ← tomlToZkVM sp1TomlFile

  /- Incremental contents of `SP1.lean`.
     We overwrite the file only if the parsing succeeds. -/
  let mut outStr := ""
  outStr := outStr ++ getSP1ImportStr

  /-
    We iterate over all the [[circuits]], collecting the lean
    variables we parse along the way. These variables will
    be collected in the final `zkVM` Lean structure.
  -/
  let mut jaggedcfg_lean_vars : List String := []

  for circ in zkVM.circuits do
    match circ with
    | .jagged jcirc =>
      /-
        We iterate over all the [[circuit.lookups]], collecting the
        lean variables along the way. These variables will be
        collected in the final `JaggedCfg` Lean structure.
      -/
      let mut lookupcfg_lean_vars : List String := []

      for lookupcfg in jcirc.lookups do
        let lookupcfg_lean_var := s!"{zkVM.name}_{jcirc.name}_{lookupcfg.name}_lookup"

        /- We retrieve the variable name associated with the field
          specified within `lookupcfg.field` from the map
          `mapFieldParamsToVarname`. -/
        let lookupcfg_field_leanvar ← orExit (
          fieldParamsToVarname
          mapFieldParamsToVarname
          lookupcfg.field
        )

        outStr := outStr ++
          s!"/- ZkVM `{zkVM.name}` | Circuit `{jcirc.name}` | Lookup `{lookupcfg.name}` -/\n" ++
          s!"\n" ++
          s!"def {lookupcfg_lean_var} : LookupCfg where\n" ++
          s!"  name            := \"{lookupcfg.name}\"\n" ++
          s!"  field           := {lookupcfg_field_leanvar}\n" ++
          s!"  isLogUpMultivar := {lookupcfg.isLogUpMultivar}\n" ++
          s!"  rowsL           := {lookupcfg.rowsL}\n" ++
          s!"  rowsT           := {lookupcfg.rowsT}\n" ++
          s!"  numColumnsS     := {lookupcfg.numColumnsS}\n" ++
          s!"  numLookupsM     := {lookupcfg.numLookupsM}\n" ++
          s!"  grindBitsLookup := {lookupcfg.grindBitsLookup}\n" ++
          s!"\n"

        /- Collecting `LookupCfg` Lean variables in a list. -/
        lookupcfg_lean_vars := lookupcfg_lean_vars.concat lookupcfg_lean_var

      let densePCS := jcirc.densePCS
      let densePCS_lean_var := s!"{zkVM.name}_{jcirc.name}_{densePCS.label}"

      /- We retrieve the variable name associated with the field
      specified within `jaggedcfg.densePCS.field` from the map
      `mapFieldParamsToVarname`. -/
      let densePCS_field_leanvar ← orExit (
        fieldParamsToVarname
        mapFieldParamsToVarname
        jcirc.densePCS.field
      )

      match densePCS with
      | .fri c =>
      outStr := outStr ++
        s!"/- ZkVM `{zkVM.name}` | Circuit `{jcirc.name}` -/\n" ++
        s!"\n" ++
        s!"def {densePCS_lean_var} : FRIConfig where\n" ++
        s!"  hashBits        := {c.hashBits}\n" ++
        s!"  ρ               := ⟨{c.ρ}, by norm_num⟩\n" ++
        s!"  field           := {densePCS_field_leanvar}\n" ++
        s!"  denseLen        := {c.denseLen}\n" ++
        s!"  batchSize       := {c.batchSize}\n" ++
        s!"  powerBatch      := {c.powerBatch}\n" ++
        s!"  multilinBatch   := {c.multilinBatch}\n" ++
        s!"  numQueries      := {c.numQueries}\n" ++
        s!"  foldingFactors  := {c.foldingFactors}\n" ++
        s!"  earlyStopDeg    := {c.earlyStopDeg}\n" ++
        s!"  grindQuery      := {c.grindQuery}\n" ++
        s!"  grindBatch      := {c.grindBatch}\n" ++
        s!"\n"
      | .whir _ => IO.eprintln "Unsupported PCS (WHIR)."; IO.Process.exit 1

      let jaggedcfg_lean_var := s!"{zkVM.name}_{jcirc.name}_jagged"

      /- We retrieve the variable name associated with the field
      specified within `jaggedcfg.field` from the map
      `mapFieldParamsToVarname`. -/
      let jaggedcfg_field_leanvar ← orExit (
        fieldParamsToVarname
        mapFieldParamsToVarname
        jcirc.field
      )

      outStr := outStr ++
      s!"def {jaggedcfg_lean_var} : JaggedCfg where\n" ++
        s!"  name            := \"{jcirc.name}\"\n" ++
        s!"  field           := {jaggedcfg_field_leanvar}\n" ++
        s!"  densePCS        := .fri {densePCS_lean_var}\n" ++
        s!"  traceLength     := {jcirc.traceLength}\n" ++
        s!"  traceWidth      := {jcirc.traceWidth}\n" ++
        s!"  numConstraints  := {jcirc.numConstraints}\n" ++
        s!"  airMaxDegree    := {jcirc.airMaxDegree}\n" ++
        s!"  lookups         := {lookupcfg_lean_vars}\n" ++
        s!"\n"

      /- Collecting `JaggedCfg` Lean variables in a list. -/
      jaggedcfg_lean_vars := jaggedcfg_lean_vars.concat jaggedcfg_lean_var

      /-
        For now, we only support per-cell verification of
        circuits relevant to `sp1.md`.
      -/
      match jcirc.name with
      | "core" => outStr := outStr ++ getSP1CoreReportStr
      | "compress" => outStr := outStr ++ getSP1CompressReportStr
      | "shrink" => outStr := outStr ++ getSP1ShrinkReportStr
      | _ => IO.eprintln "Unsupported circuit"; IO.Process.exit 1
    | _ => IO.eprintln "Unsupported circuit family"; IO.Process.exit 1

  outStr := outStr ++ consistencyProofs

  IO.FS.writeFile sp1LeanFile outStr
  IO.println s!"Successfully parsed {sp1TomlFile} to {sp1LeanFile}!"
  IO.Process.exit 0

end SoundcalcIO.LeanEmitter

/-
  We preserve the namespace while redeclaring the main.
  This enables the following:
  `lean exe leanemitter`
-/
def main := SoundcalcIO.LeanEmitter.main
