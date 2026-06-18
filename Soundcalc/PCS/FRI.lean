import Mathlib
import Soundcalc.Regime   -- brings in FieldParams, Rate, Regime, UDR, koalaBear4
                          -- and transitively SecBits (secBits)

open Soundcalc

/-!
# FRI soundness configuration

Verbatim from the spec: `FRIConfig`, `FRIConfig.batchingErr`,
`FRIConfig.commitErr`, `FRIConfig.queryErr`, and the *statement* of
`FRIConfig.earlyStop_ok`.

`ρ` is stored as `Rate` (the subtype `{ρ : ℚ // 0 < ρ ∧ ρ < 1}`) so the
constraint is enforced at construction time and Regime's field signatures are
satisfied without any conversion at call sites.
-/

abbrev N := Nat
abbrev Q := Rat

/-! ## FRI configuration -/

structure FRIConfig where
  field          : FieldParams
  ρ              : Rate          -- rate, constrained to (0,1) by the Rate subtype
  denseLen       : N             -- = 2^21 for SP1 core
  batchSize      : N             -- = 193
  numQueries     : N             -- = 124
  foldingFactors : List N        -- = [2,2,...] (21 entries)
  earlyStopDeg   : N             -- = 4
  grindQuery     : N             -- = 16
  grindBatch     : N             -- = 5

def FRIConfig.batchingErr (c : FRIConfig) (R : Regime) : Q :=
  R.errMultilinear c.ρ c.denseLen c.batchSize / 2 ^ c.grindBatch

def FRIConfig.commitErr (c : FRIConfig) (R : Regime) (i : N) : Q :=
  let acc := (c.foldingFactors.take (i + 1)).foldl (· * ·) 1
  R.errPowers c.ρ (c.denseLen / acc) (c.foldingFactors.getD i 1)

def FRIConfig.queryErr (c : FRIConfig) (R : Regime) : Q :=
  (1 - R.θ c.ρ c.denseLen) ^ c.numQueries / 2 ^ c.grindQuery

/-! ## SP1 core config

`denseLen` is the FRI dimension `d`; `n = d/ρ = 2^23`.  The trace length
(`2^22`, used by the S5 zerocheck) is a *separate* quantity and deliberately
does **not** appear in `FRIConfig`. -/

def sp1CoreFRI : FRIConfig where
  field          := koalaBear4
  ρ              := ⟨1 / 4, by norm_num⟩   -- 0 < 1/4 < 1, proved at definition time
  denseLen       := 2 ^ 21
  batchSize      := 193
  numQueries     := 124
  foldingFactors := List.replicate 21 2
  earlyStopDeg   := 4
  grindQuery     := 16
  grindBatch     := 5

/-! ## Early-stop side condition

The statement is the spec's, with explicit `ℚ` coercions made visible:
`c.denseLen / (c.ρ : Q)` mixes `ℕ` and `ℚ`; the cast `(c.ρ : Q)` extracts
the value from the `Rate` subtype. -/

theorem FRIConfig.earlyStop_ok (c : FRIConfig) (hc : c = sp1CoreFRI) :
    ((c.denseLen : Q) / (c.ρ : Q)) / ((c.foldingFactors.foldl (· * ·) 1 : N) : Q)
      = (c.earlyStopDeg : Q) := by
  subst hc
  simp only [sp1CoreFRI]
  norm_num [show ((List.replicate 21 2).foldl (· * ·) 1 : N) = 2097152 from by decide]

/-! ## Exit criteria

`queryErr` is fully determined by `θ = (1−ρ)/2`, so it closes now:
`(1 − 3/8)^124 / 2^16 = (5/8)^124 / 2^16`, whose `⌊−log₂⌋` is `100`. -/

example : secBits (sp1CoreFRI.queryErr (UDR koalaBear4)) = 100 := by native_decide
  -- `decide` should also work: `pow` is structural (124 GMP-backed `Rat` mults),
  -- `floor`/`log2Fuel` use GMP-accelerated `Nat` ops.

/-
The other three depend on the `errPowers` / `errMultilinear` numerators, which
are placeholders above.  Once they match fri.py, these close `by decide`:

    secBits (sp1CoreFRI.batchingErr (UDR koalaBear4))    = 104
    secBits (sp1CoreFRI.commitErr   (UDR koalaBear4) 0)  = 103
    secBits (sp1CoreFRI.commitErr   (UDR koalaBear4) 20) = 122

and `earlyStop_ok` is one `subst`+`norm_num` for each of the three SP1 configs.
-/
