import Lake.Toml.Load
import Lake.Toml.Data.Value
import Lean.Parser.Types
import SoundcalcIO.Common
import SoundcalcIO.TomlParser.Common
import SoundcalcIO.TomlParser.Circuit.Circuit

import Soundcalc

open Lake.Toml Lean Parser
open Soundcalc
open SoundcalcIO
open SoundcalcIO.TomlParser

namespace SoundcalcIO

/--
  Parse a `ZkVM` from an input `.toml` file `inTomlFile`.
  If the `.toml` is invalid, the process errors out with a descriptive error message.
-/
def tomlToZkVM (inTomlFile: String) : IO ZkVM := do
  let inToml ← IO.FS.readFile inTomlFile
  let ictx : InputContext := mkInputContext inToml inTomlFile
  let .ok toml_tab ← (loadToml ictx).toIO' | IO.eprintln "Parse failed"; IO.Process.exit 1

  /- Parsing [zkevm]-/
  let zkvm_tab ← orExit (getTable toml_tab "zkevm")

  let zkvm_circs ← orExit (getArray toml_tab "circuits")

  /-  List of Circuits contained within the ZkVM -/
  let mut circuit_list : List Circuit := []

  /- We parse all the [[circuits]] -/
  for circ in zkvm_circs do
    match circ with
    | .table' _ circ_tab =>
      let circuit ← Circuit.parseFromToml circ_tab zkvm_tab toml_tab
      circuit_list := circuit_list.concat circuit
    | _ => IO.eprintln "Unexpected non-table circuit item"; IO.Process.exit 1

  let zkvm_name ← orExit (getString zkvm_tab "name")
  let zkvm_field ← orExit (getString zkvm_tab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field)
  let zkvm_version ← orExit (getOptString zkvm_tab "version")

  /- We compute a proof showing that the fields contained in all the
      circuits of the zkVM are consistent with each other. -/
  let h_circuits_lifted : PLift (circuit_list.all (·.field == zkvm_field) = true) ←
    match decEq (circuit_list.all (·.field == zkvm_field)) true with
    | .isTrue h  => pure (PLift.up h)
    | .isFalse _ => IO.eprintln "Circuit field mismatch: not all circuits share the zkVM's field"; IO.Process.exit 1

  let zkVM : ZkVM := {
    name             := zkvm_name
    field            := zkvm_field
    version          := zkvm_version
    circuits         := circuit_list
    h_circuits_field := PLift.down (α := circuit_list.all (·.field == zkvm_field) = true) h_circuits_lifted
  }
  pure zkVM

end SoundcalcIO
