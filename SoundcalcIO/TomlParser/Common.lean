import Soundcalc
import SoundcalcIO.Common
import Lake.Toml.Data.Value

import Soundcalc

open Lake.Toml Lean

open Soundcalc
open SoundcalcIO

namespace SoundcalcIO.TomlParser

/-! # .toml getter combinators
  Auxiliary methods to parse `.toml` files robustly.
  Base strategy: if a field is missing, is incomplete, or it
  does not match the expected type within the `.toml`, the program
  errors out with an explicative error message.

  Combinator variants:
  - `getOpt*` does not error out if a field is missing (returns `none` instead).
  - `get*D` allows for setting a default value if a field is missing.
-/

def getString (tbl : Table) (key : String) : Except String String :=
  match tbl.find? (.mkSimple key) with
  | some (.string _ s)  => .ok s
  | some _              => .error s!"key '{key}' exists but is not a string"
  | none                => .error s!"key '{key}' not found"

def getOptString (tbl : Table) (key : String) : Except String (Option String) :=
  match tbl.find? (.mkSimple key) with
  | some (.string _ s)  => .ok s
  | some _              => .error s!"key '{key}' exists but is not a string"
  | none                => .ok none

/--
  Returns an encoding of the LogUp string indexed by `key` if it exists in `tbl`.
  If a value is indexed by `key` but it is not a LogUp string or it does not exist, return an error.
-/
def getLogUpBoolFromStr (tbl : Table) (key : String) : Except String Bool :=
  let s := getString tbl key
  match s with
  | .ok "univariate"   => .ok false
  | .ok "multivariate" => .ok true
  | _ => .error s!"key '{key}' is an invalid LogUp string."

/--
  Returns an encoding of the supported regime variable indexed by `key` if it exists in `tbl`.
  If a value is indexed by `key` but it is not a valid regime string, return an error.
-/
def getOptRegime (tbl : Table) (key : String) : Except String (Option SupportedRegime) :=
  let s := getOptString tbl key
  match s with
  | .ok "unique" => .ok (SupportedRegime.UDR)
  | .ok "list"   => .ok (SupportedRegime.JBR)
  | .ok none     => .ok none
  | _ => .error s!"key '{key}' is an invalid supported regime string."

def getNat (tbl : Table) (key : String) : Except String Nat :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .error s!"key '{key}' not found"

/--
  Returns the natural indexed by `key` if it exists in `tbl`.
  If it does not exist, return `d` instead.
  If a value is indexed by `key` but it is not a natural, return an error.
-/
def getNatD (tbl : Table) (key : String) (d : Nat) : Except String Nat :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .ok d

def getOptNat (tbl : Table) (key : String) : Except String (Option Nat) :=
  match tbl.find? (.mkSimple key) with
  | some (.integer _ i) => if i ≥ 0 then .ok i.toNat
                           else .error s!"key '{key}' is a negative integer"
  | some _              => .error s!"key '{key}' exists but is not a natural"
  | none                => .ok none

def getBool (tbl : Table) (key : String) : Except String Bool :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .error s!"key '{key}' not found"

/--
  Returns the bool indexed by `key` if it exists in `tbl`.
  If it does not exist, return `d` instead.
  If a value is indexed by `key` but it is not a bool, return an error.
-/
def getBoolD (tbl : Table) (key : String) (d : Bool) : Except String Bool :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .ok d

def getOptBool (tbl : Table) (key : String) : Except String (Option Bool) :=
  match tbl.find? (.mkSimple key) with
  | some (.boolean _ b) => .ok b
  | some _              => .error s!"key '{key}' exists but is not a boolean"
  | none                => .ok none

def getFloat (tbl : Table) (key : String) : Except String Float :=
  match tbl.find? (.mkSimple key) with
  | some (.float _ f)   => .ok f
  | some _              => .error s!"key '{key}' exists but is not a float"
  | none                => .error s!"key '{key}' not found"

def getOptFloat (tbl : Table) (key : String) : Except String (Option Float) :=
  match tbl.find? (.mkSimple key) with
  | some (.float _ f)   => .ok f
  | some _              => .error s!"key '{key}' exists but is not a float"
  | none                => .ok none

def getArray (tbl : Table) (key : String) : Except String (Array Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .error s!"key '{key}' not found"

/--
  Returns the array indexed by `key` if it exists in `tbl`.
  If it does not exist, return `d` instead.
  If a value is indexed by `key` but it is not an array, return an error.
-/
def getArrayD (tbl : Table) (key : String) (d: Array Value) : Except String (Array Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .ok d

def getOptArray (tbl : Table) (key : String) : Except String (Option (Array Value)) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a
  | some _              => .error s!"key '{key}' exists but is not an Array"
  | none                => .ok none

def getList (tbl : Table) (key : String) : Except String (List Value) :=
  match tbl.find? (.mkSimple key) with
  | some (.array _ a)   => .ok a.toList
  | some _              => .error s!"key '{key}' exists but is not a List"
  | none                => .error s!"key '{key}' not found"

def getListNat (tbl : Table) (key : String) : Except String (List Nat) := do
  let l ← getList tbl key
  l.mapM fun
  | .integer _ i =>
      if i ≥ 0 then .ok i.toNat
      else .error s!"The List indexed by '{key}' contains a negative integer"
  | _ => .error s!"The List indexed by '{key}' contains non-integer values"

def getTable (tbl : Table) (key : String) : Except String (RBDict Name Value Name.quickCmp) :=
  match tbl.find? (.mkSimple key) with
  | some (.table' _ t)  => .ok t
  | some _              => .error s!"key '{key}' exists but is not a Table"
  | none                => .error s!"key '{key}' not found"

/- More parsing auxiliary methods. -/

/--
  Map of supported `String` -> `FieldParams`.
-/
def mapStrToFieldParams : List (String × FieldParams) := [
  ("KoalaBear^4", koalaBear4),
  ("M31^4", mersenne31_4),
  ("BabyBear^4", babyBear4),
  ("Goldilocks^3", goldilocks3),
  ("KoalaBear^5", koalaBear5),
]

/--
  Maps strings to supported `FieldParams`.
-/
def strToFieldParams (map : List (String × FieldParams)) (s : String) : Except String FieldParams :=
  match map.lookup s with
  | some fp => .ok fp
  | none    => .error s!"no FieldParams defined for '{s}'"

/--
  Returns the field from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.

  If any circuit-level conf is specified for `field`,
  it overrides the global zkVM configs.
  Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L85
-/
def getCircField (circTab : Table)
                         (zkvmTab : Table) : IO FieldParams := do
  let zkvm_field_str ← orExit (getString zkvmTab "field")
  let zkvm_field ← orExit (strToFieldParams mapStrToFieldParams zkvm_field_str)

  let circ_field_str ← orExit (getOptString circTab "field")
  let circ_field ← match circ_field_str with
  | some s => orExit (strToFieldParams mapStrToFieldParams s)
  | none   => pure zkvm_field

  pure circ_field

/--
  Returns the hash bits from a circuit table `circTab` contained
  in a zkVM table `zkvmTab`, which is parsed from a `.toml` file.

  If any circuit-level conf is specified for `hash_size_bits`,
  it overrides the global zkVM configs.
  Ref: https://github.com/ethereum/soundcalc/blob/d9078d64c9c3ae15b0931f6d249b2dc073194f15/soundcalc/zkvms/zkvm.py#L81
-/
def getCircHashBits (circTab : Table)
                            (zkvmTab : Table) : IO Nat := do
  let zkvm_hash_size_bits ← orExit (getNat zkvmTab "hash_size_bits")
  let circ_hash_size_bits ← orExit (getNatD circTab "hash_size_bits" zkvm_hash_size_bits)

  pure circ_hash_size_bits

end SoundcalcIO.TomlParser
