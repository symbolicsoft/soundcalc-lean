import Soundcalc
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
def mapFieldParamsToDisplayname : List (FieldParams × String) := [
  (koalaBear4, "KoalaBear⁴"),
  (mersenne31_4, "M31⁴"),
  (babyBear4, "BabyBear⁴"),
  (goldilocks3, "Goldilocks³"),
]

def fieldParamsToDisplayname (map : List (FieldParams × String))
                                     (fp : FieldParams) : Except String String :=
  match map.lookup fp with
  | some s => .ok s
  | none   => .error s!"unsupported FieldParams"

/--
  Parses a float as a string without trailing zeroes.
  Used to mirror the display of floats used within `sp1.md`.
-/
def floatToFloatstr (f : Float) : String :=
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
def circLinkFromName (name: String) : String :=
  "(#" ++ name.toLower.replace " " "-" ++ ")"

/--
  Returns the range `[1, n]` in an alphabetically-sorted fashion.
  Mirrors the ordering of "commit round {i}"" used within `soundcalc`.

  Example (`n = 11`):
  `[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]`
  ->
  `[1, 10, 11, 2, 3, 4, 5, 6, 7, 8, 9]`
-/
def rangeAlph (n : Nat) : List Nat :=
  (
    /- We drop `0` and range to `n` inclusive. -/
    (List.range (n+1)).tail.toArray.qsort
    (fun a b => decide (toString a < toString b))
  ).toList

end SoundcalcIO.MdRenderer
