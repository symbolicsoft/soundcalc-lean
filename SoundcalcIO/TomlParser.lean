import Lake.Toml.Load
import Lake.Toml.Data.Value
import Lean.Parser.Types

open Lake.Toml Lean Parser

namespace SoundcalcIO.TomlParser

/-!
  # `SoundcalcIO.TomlParser` —  (roadmap S7; partial)
    A parsing tool that generates `SP1.lean` from `SP1.toml`.
    The `.lean` file wraps together all the structures defined in companion
    files (`JaggedCfg`, `LookupCfg`, `FRIConfig`), enabling a formal arithmetic
    verification of the `sp1.md` report of  `soundcalc` by means of cell-wise
    evaluations.

    usage: `lean exe tomlparser`

  *TODOs.* While the structure of the current parser is general, its instantiation
  is tailored to SP1 only. Extensions to other zkEVMs will be addressed as they
  are introduced within the roadmap.
-/

/-
  Auxiliary methods to parse `.toml` files robustly.
  If a field is missing, is incomplete, or it does not match the
  expected type within the `.toml`, the Parser errors out.
-/

def orExit {T : Type} (e : Except String T) : IO T :=
  match e with
  | .ok v    => return v
  | .error m => do IO.eprintln s!"error: {m}"; IO.Process.exit 1

private def getString (tbl : Table) (key : String) : Except String String :=
  match tbl.find? (.mkSimple key) with
  | some (.string _ s)  => .ok s
  | some _              => .error s!"key '{key}' exists but is not a string"
  | none                => .error s!"key '{key}' not found"

private def getNat (tbl : Table) (key : String) : Except String Nat :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .error s!"key '{key}' not found"

private def getBool (tbl : Table) (key : String) : Except String Bool :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .error s!"key '{key}' not found"

private def getFloat (tbl : Table) (key : String) : Except String Float :=
  match tbl.find? (.mkSimple key) with
  | some (.float _ f)   => .ok f
  | some _              => .error s!"key '{key}' exists but is not a float"
  | none                => .error s!"key '{key}' not found"

private def getArray (tbl : Table) (key : String) : Except String (Array Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .error s!"key '{key}' not found"

private def getArrayOrNone (tbl : Table) (key : String) : Except String (Array Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .ok #[]

private def getList (tbl : Table) (key : String) : Except String (List Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a.toList
  | some _              => .error s!"key '{key}' exists but is not a List"
  | none                => .error s!"key '{key}' not found"

private def getListNat (tbl : Table) (key : String) : Except String (List Nat) := do
  let l ← getList tbl key
  l.mapM fun
  | .integer _ i =>
      if i ≥ 0 then .ok i.toNat
      else .error s!"The List indexed by '{key}' contains a negative integer"
  | _ => .error s!"The List indexed by '{key}' contains non-integer values"

private def getTable (tbl : Table) (key : String) : Except String (RBDict Name Value Name.quickCmp) :=
  match tbl.find? (.mkSimple key) with
  | some (.table' _ t)  => .ok t
  | some _              => .error s!"key '{key}' exists but is not a Table"
  | none                => .error s!"key '{key}' not found"

/-- More parsing auxiliary methods. -/

/-
  Removes all `^` symbols while lower-casing the first letter of a string.
  Main use: parsing field names (e.g., `KoalaBear^4` -> `koalaBear4`).
-/
private def cleanFieldName (s: String) : String :=
  let s := s.replace "^" ""
  match s.toList with
  | []      => ""
  | c :: cs => String.ofList (c.toLower :: cs)

/-
  **IMPORTANT**
  The TOML file contains exact rationals represented as floats.
  With the following approach, we ensure the semantics of exact rationals
  are preserved. We do that by:

  - Converting the float to a string, stripping trailing zeroes;
  - Mapping the resulting string to an exact rational.

  *NOTE* This strategy assumes that meaningful float values can always be
  expressed as exact rationals, and that the map is relatively contained
  (as it is the case for the rate parameter ρ in SP1).

  In the general case, we would give up the accuracy of reasoning
  in terms of exact rationals instead.
-/
private def mapFloatstrToRat : List (String × Rat) := [
  ("1",      1/1),
  ("0.5",    1/2),
  ("0.25",   1/4),
  ("0.125",  1/8),
  ("0.0625", 1/16),
]

private def stripTrailingZeros (s : String) : String :=
  -- only strip after a decimal point
  if s.contains '.' then
    let stripped := (s.dropEndWhile (· == '0')).toString
    -- avoid leaving a bare "1." with no fractional digits
    (stripped.dropEndWhile (· == '.')).toString
  else
    s

private def floatToRat (map : List (String × Rat)) (f : Float) : Except String Rat :=
  let key := stripTrailingZeros f.toString
  match map.lookup key with
  | some r => .ok r
  | none   => .error s!"no entry for '{f}' (normalized to '{key}')"

/-
  Header string declaring the imports of `SP1.lean`.
  *TODO* Polishing namespaces.
-/

private def getSP1ImportStr : String :=
    s!"/- Automatically generated from `TomlParser.lean` and `SP1.toml`. -/\n" ++
    s!"\n" ++
    s!"import Mathlib\n" ++
    s!"import Soundcalc\n" ++
    s!"import Soundcalc.Field\n" ++
    s!"import Soundcalc.Lookup\n" ++
    s!"\n" ++
    s!"open Soundcalc\n" ++
    s!"open Soundcalc.Lookup\n" ++
    s!"open Soundcalc.Field\n" ++
    s!"\n"

/-
  The values below are for now manually parsed from `soundcalc`'s `sp1.md`
  (https://github.com/ethereum/soundcalc/blob/main/reports/sp1.md).
  *TODO*: Lots of polishing; possibly, automatic parsing from the `.md`.
-/

private def getSP1CoreReportStr : String :=
  "/- Sanity check against `sp1.md`'s reported values.-/" ++
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
  "\n"

private def getSP1CompressReportStr : String :=
  "/- Sanity check against `sp1.md`'s reported values.-/" ++
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
  "\n"

private def getSP1ShrinkReportStr : String :=
  "/- Sanity check against `sp1.md`'s reported values.-/" ++
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
  "\n"

private def appBanner : String :=
  s!"tomlparser - a parsing tool that parses a zkEVM configuration in .toml\n" ++
  s!"into an equivalent .lean file verifiable by Soundcalc.\n" ++
  s!"\n" ++
  s!"usage: lake exe tomlparser\n" ++
  s!"|-> default inputs: ./SoundcalcIO/ZkVM/SP1.toml ./SoundcalcIO/ZkVM/SP1.lean\n" ++
  s!"\n" ++
  s!"extended usage: lake exe tomlparser <in-toml-path> <out-lean-path>\n" ++
  s!"|-> supported circuits: SP1.toml\n"

/- *TODO*: generalize to other zkEVMs, circuits, and related fields to parse. -/
def main (args: List String): IO Unit := do
  IO.println appBanner
  if args.length == 1 then
    IO.eprintln "invalid inputs"; IO.Process.exit 1

  /- Default: `SP1.toml`, `SP1.lean` relative to the project root path. -/
  let sp1TomlFile := args.getD 0 "./SoundcalcIO/ZkVM/SP1.toml"
  let sp1LeanFile := args.getD 1 "./SoundcalcIO/ZkVM/SP1.lean"

  let inToml ← IO.FS.readFile sp1TomlFile
  let ictx : InputContext := mkInputContext inToml sp1LeanFile
  let .ok tbl ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  /- Incremental contents of `SP1.lean`.
     We overwrite the file only if the parsing succeeds. -/
  let mut outStr := ""
  outStr := outStr ++ getSP1ImportStr

  /- Parsing [zkevm]-/
  let zkevm_tab ← orExit (getTable tbl "zkevm")

  let zkevm_name ← orExit (getString zkevm_tab "name")
  let zkevm_protocol_family ← orExit (getString zkevm_tab "protocol_family")
  let zkevm_field ← orExit (getString zkevm_tab "field")
  let zkevm_field := cleanFieldName zkevm_field -- 1st letter lowercase; no '^'
  let zkevm_version ← orExit (getString zkevm_tab "version")
  let zkevm_hash_size_bits ← orExit (getNat zkevm_tab "hash_size_bits")

  let zkevm_circs ← orExit (getArray tbl "circuits")

  /- We loop over all the [[circuits]] -/
  for circ in zkevm_circs do
    match circ with
    | .table' _ circ_tab =>
      /- Parsing all the fields found within SP1 -/
      let circ_name ← orExit (getString circ_tab "name")
      let circ_udr_only ← orExit (getBool circ_tab "udr_only")
      let circ_blowup_factor ← orExit (getNat circ_tab "blowup_factor")
      /- We interpret the float as an exact rational according
         to the `mapFloatstrToRat` map. Note: if the float is
         malformed, the conversion fails. -/
      let circ_rho ← orExit (getFloat circ_tab "rho")
      let circ_rho ← orExit (floatToRat mapFloatstrToRat circ_rho)
      let circ_trace_length ← orExit (getNat circ_tab "trace_length")
      let circ_trace_columns ← orExit (getNat circ_tab "trace_columns")
      let circ_dense_length ← orExit (getNat circ_tab "dense_length")
      let circ_dense_batch ← orExit (getNat circ_tab "dense_batch")
      let circ_num_constraints ← orExit (getNat circ_tab "num_constraints")
      let circ_air_max_degree ← orExit (getNat circ_tab "air_max_degree")
      let circ_opening_points ← orExit (getNat circ_tab "opening_points")
      let circ_power_batching ← orExit (getBool circ_tab "power_batching")
      let circ_pmultilinear_batching ← orExit (getBool circ_tab "multilinear_batching")
      let circ_multilinear_zerocheck ← orExit (getBool circ_tab "multilinear_zerocheck")
      let circ_num_queries ← orExit (getNat circ_tab "num_queries")
      /- We interpret the list as a list of Naturals. -/
      let circ_fri_folding_factors ← orExit (getListNat circ_tab "fri_folding_factors")
      let circ_fri_early_stop_degree ← orExit (getNat circ_tab "fri_early_stop_degree")
      let circ_grinding_batching_phase ← orExit (getNat circ_tab "grinding_batching_phase")
      let circ_grinding_query_phase ← orExit (getNat circ_tab "grinding_query_phase")

      outStr := outStr ++
      s!"/- {zkevm_name}: {circ_name} -/\n" ++
      s!"\n" ++
      s!"def {zkevm_name}_{circ_name}_jagged : JaggedCfg where\n" ++
      s!"  field           := {zkevm_field}\n" ++
      s!"  denseLen        := {circ_dense_length}\n" ++
      s!"  batchSize       := {circ_dense_batch}\n" ++
      s!"  traceWidth      := {circ_trace_columns}\n" ++
      s!"  traceLength     := {circ_trace_length}\n" ++
      s!"  numConstraints  := {circ_num_constraints}\n" ++
      s!"  airMaxDegree    := {circ_air_max_degree}\n" ++
      s!"\n" ++
      s!"def {zkevm_name}_{circ_name}_FRI : FRIConfig where\n" ++
      s!"  field           := {zkevm_field}\n" ++
      s!"  ρ               := ⟨{circ_rho}, by norm_num⟩\n" ++
      s!"  denseLen        := {circ_dense_length}\n" ++
      s!"  batchSize       := {circ_dense_batch}\n" ++
      s!"  numQueries      := {circ_num_queries}\n" ++
      s!"  foldingFactors  := {circ_fri_folding_factors}\n" ++
      s!"  earlyStopDeg    := {circ_fri_early_stop_degree}\n" ++
      s!"  grindQuery      := {circ_grinding_query_phase}\n" ++
      s!"  grindBatch      := {circ_grinding_batching_phase}\n" ++
      s!"\n"

      /-
        We loop over all the [[circuit.lookups]]
        If no lookups are defined, we return an empty array instead of an error.
        If lookups is defined not as an array, we still error out.
      -/
      let circ_lookups ← orExit (getArrayOrNone circ_tab "lookups")

      for lookup in circ_lookups do
        match lookup with
        | .table' _ lookup_tab =>
          let lookup_name ← orExit (getString lookup_tab "name")
          let lookup_logup_type ← orExit (getString lookup_tab "logup_type")
          let lookup_rows_L ← orExit (getNat lookup_tab "rows_L")
          let lookup_rows_T ← orExit (getNat lookup_tab "rows_T")
          let lookup_num_columns_S ← orExit (getNat lookup_tab "num_columns_S")
          let lookup_num_lookups_M ← orExit (getNat lookup_tab "num_lookups_M")
          let lookup_grinding_bits_lookup ← orExit (getNat lookup_tab "grinding_bits_lookup")
          let lookup_multilinear_fingerprint ← orExit (getBool lookup_tab "multilinear_fingerprint")

          outStr := outStr ++
          s!"def {zkevm_name}_{circ_name}_{lookup_name}_lookup : LookupCfg where\n" ++
          s!"  field           := {zkevm_field}\n" ++
          s!"  rowsT           := {lookup_rows_T}\n" ++
          s!"  rowsL           := {lookup_rows_L}\n" ++
          s!"  numColumnsS     := {lookup_num_columns_S}\n" ++
          s!"  numLookupsM     := {lookup_num_lookups_M}\n" ++
          s!"  grindBitsLookup := {lookup_grinding_bits_lookup}\n" ++
          s!"\n"
        |_ => IO.eprintln "Unexpected non-table lookup item"; IO.Process.exit 1

      /- For now, we only support circuits relevant to `sp1.md`. -/
      match circ_name with
        | "core" => outStr := outStr ++ getSP1CoreReportStr
        | "compress" => outStr := outStr ++ getSP1CompressReportStr
        | "shrink" => outStr := outStr ++ getSP1ShrinkReportStr
        | _ => IO.eprintln "Unsupported circuit"; IO.Process.exit 1
    | _ => IO.eprintln "Unexpected non-table circuit item"; IO.Process.exit 1

  IO.FS.writeFile sp1LeanFile outStr
  IO.println s!"Successfully parsed {sp1TomlFile} to {sp1LeanFile}!"
  IO.Process.exit 0

end SoundcalcIO.TomlParser

/-
  We preserve the namespace while redeclaring the main.
  This enables the following:
  `lean --run TomlParser.lean`
-/
def main := SoundcalcIO.TomlParser.main
