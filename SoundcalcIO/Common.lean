import Soundcalc

open Soundcalc

namespace SoundcalcIO

/--
  Generic error-handling routine.

  If `e` is a `.ok` value, it returns the unwrapped value.
  Otherwise, it causes the program to terminate with an error code,
  printing the contents of the string error specified in `e`.
-/
def orExit {T : Type} (e : Except String T) : IO T :=
  match e with
  | .ok v    => return v
  | .error m => do IO.eprintln s!"error: {m}"; IO.Process.exit 1

/--
  **IMPORTANT**
  The TOML files of interest for this project contain exact rationals
  represented as floats. With the following approach, we ensure the
  semantics of exact rationals are preserved. We do that by
  mapping the float to an exact rational, which is also a *rate*
  (i.e., `0 < ρ < 1`).

  *NOTE* This strategy assumes that relevant float values can always be
  expressed as exact rationals, and that the map is relatively contained
  (as it is the case for the rate parameter `ρ` in SP1).

  In the general case, we would give up the accuracy of reasoning
  in terms of exact rationals instead.

  The direct map is used in `TomlParser.lean`;
  The reverse map in `MdRenderer.lean`.
-/
def mapFloatToRate : List (Float × Rate) := [
  (0.5,      Rate.half),
  (0.25,     Rate.quarter),
  (0.125,    Rate.eighth),
  (0.0625,   Rate.sixteenth),
  (0.031250, Rate.thirtysecond),
]

/--
  Maps a float `f` to its exact Rate counterpart, as specified by `map`.
-/
def floatToRate (map : List (Float × Rate)) (f : Float) : Except String Rate :=
  match map.lookup f with
  | some rate => .ok rate
  | none      => .error s!"no entry for '{f}')"

/-
  Reverse maps a Rate `rate` to its float counterpart, as specified by `map`.
-/
def rateToFloat (map : List (Float × Rate))
                (rate : Rate) : Except String Float :=
  match map.find? (fun (_, q) => q = rate) with
  | some (f, _) => .ok f
  | none        => .error s!"no entry for '{rate}'"

/--
  Maps an Option Float f representing a `gap_to_radius` to its exact ℚ counterpart.

  Valid `gap_to_radius` are multiples of `1/3000`, in line with
  with `Soundcalc/ZkVM/ZisK` (currently the only zkVM leveraging this field).
-/
def gapToRadiusRat (f: Option Float) : Except String (Option Rat) := Id.run do
  match f with
    | some f =>
    /- Parsing mismatches between soundcalc's .toml float representation
       and Lean's float representation are handled as separate explicit cases.  -/
    if f == 0.003333333333333333 then return .ok (some ((10: ℚ)/3000))
    if f == 0.005999999999999999 then return .ok (some ((18: ℚ)/3000))
    if f == 0.006666666666666666 then return .ok (some ((20: ℚ)/3000))

    for i in List.range 3000 do
      if ((i : ℚ)/3000).toFloat == f then return .ok (some ((i : ℚ)/3000))
    return .error s!"Invalid gap-to-radius"
    | none => .ok none
end SoundcalcIO
