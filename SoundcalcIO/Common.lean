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
  (0.5,    Rate.half),
  (0.25,   Rate.quarter),
  (0.125,  Rate.eighth),
  (0.0625, Rate.sixteenth),
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

end SoundcalcIO
