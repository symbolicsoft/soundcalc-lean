import Mathlib
import Soundcalc.Regime

namespace Soundcalc

private abbrev N := Nat
private abbrev Q := Rat

/-!
# Jagged circuit error bounds

Pure integer `|F|` terms for the jagged reduction and zerocheck protocols
(corresponding to `circuits/jagged.py`).

With `ℓ = ⌈log₂ d⌉ + ⌈log₂ b⌉ = 21 + 8 = 29`:

* **reduceErr**: `(⌈log₂ w⌉ + 2ℓ + 2(2ℓ + 2)) / |F|`
  where `w` is the trace width.

* **zerocheckErr**: `(C + (deg + 2) ⌈log₂ H⌉) / |F|`
  where `C` is the constraint count, `deg` is the AIR max degree, and `H` is
  the trace length.
-/

/-- Parameters for a jagged circuit instance. -/
structure JaggedCfg where
  field          : FieldParams
  denseLen       : N    -- e.g. 2^21 (FRI dimension d)
  batchSize      : N    -- e.g. 193  (contributes ⌈log₂ b⌉ to ℓ)
  traceWidth     : N    -- e.g. 3741
  traceLength    : N    -- e.g. 2^22 (one gotcha: use trace length, not FRI dimension)
  numConstraints : N    -- e.g. 3412
  airMaxDegree   : N    -- e.g. 3

/-- Reduction soundness error.

`ℓ = ⌈log₂ denseLen⌉ + ⌈log₂ batchSize⌉`; the formula counts variables checked
in two rounds of the jagged sumcheck (width term + linear and quadratic bookkeeping). -/
def JaggedCfg.reduceErr (c : JaggedCfg) : Q :=
  let l := Nat.clog 2 c.denseLen + Nat.clog 2 c.batchSize  -- 21 + 8 = 29
  ((Nat.clog 2 c.traceWidth : Q) + 2 * l + 2 * (2 * l + 2)) / (c.field.card : Q)

/-- Zerocheck soundness error.

Standard AIR zerocheck: `C` constraint terms plus `(deg + 2)` per sumcheck variable
over `⌈log₂ H⌉` variables. -/
def JaggedCfg.zerocheckErr (c : JaggedCfg) : Q :=
  ((c.numConstraints : Q) + (c.airMaxDegree + 2) * Nat.clog 2 c.traceLength)
  / (c.field.card : Q)

/-!
## SP1 core instance

Parameters from `circuits/jagged.py`:
* `denseLen = 2^21`, `batchSize = 193` → `ℓ = 21 + 8 = 29`
* `traceWidth = 3741`, `numConstraints = 3412`, `airMaxDegree = 3`
* `traceLength = 2^22` (the "length gotcha": trace rows, not FRI domain size)
-/
def sp1Core : JaggedCfg where
  field          := koalaBear4
  denseLen       := 2 ^ 21
  batchSize      := 193
  traceWidth     := 3741
  traceLength    := 2 ^ 22
  numConstraints := 3412
  airMaxDegree   := 3

/-!
## Exit criteria

`secBits (sp1Core.reduceErr) = 116` and `secBits (sp1Core.zerocheckErr) = 112`.

Derivation sketch:
* `ℓ = 29`, numerator of `reduceErr = 12 + 58 + 120 = 190`, `secBits = ⌊log₂(|F|/190)⌋ = 116`
* numerator of `zerocheckErr = 3412 + 5·22 = 3522`, `secBits = ⌊log₂(|F|/3522)⌋ = 112`
-/

example : secBits sp1Core.reduceErr = 116 := by native_decide

example : secBits sp1Core.zerocheckErr = 112 := by native_decide

end Soundcalc
