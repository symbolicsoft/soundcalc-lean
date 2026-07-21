import Mathlib
import Soundcalc.SecBits
import Soundcalc.Regime
import Soundcalc.PCS.FRI
import Soundcalc.Lookup

namespace Soundcalc

/-!
# DEEP-ALI circuit error bounds

Error formulas for the Algebraic Linking (ALI) and Deep Out-Of-Domain (DEEP)
terms from BCHKS25 Theorem 8 / eprint 2022/1216.

Parallel to `Soundcalc/Circuit/Jagged.lean` for Airbender (which is not jagged).

Both `aliErr` and `deepErr` scale with the regime's list size `L⁺`, which
re-introduces `√ρ` (and thus the JBR rational envelope) into the circuit layer.

**DEEP denominator note**: `deepErr` divides by `|F| − H − D`, not `|F|`.
With `|F| ≈ 2¹²⁴` and `H + D = 2²⁴ + 2²⁵` this is a small but real
correction — do not simplify to `|F|`.
-/

/-- Parameters for a DEEP-ALI circuit instance (`circuits/deep_ali.py: DeepAliConfig`). -/
structure DeepAliCfg where
  name           : String
  field          : FieldParams
  proofSystName  : String
  densePCS       : FRIConfig
  numConstraints : N    -- C = 928
  airMaxDegree   : N    -- deg = 2
  maxCombo       : N    -- m_max = 2 (max column entries in one constraint)
  grindDeep      : N    -- = 12
  lookups        : List LookupCfg := []
  /- The theorems below enforce that fields are mutually consistent
    (same guard as `JaggedCfg.h_densePCS_field` / `h_lookups_field`). -/
  h_densePCS_field : densePCS.field = field := by rfl
  h_lookups_field  : lookups.all (·.field == field) = true := by decide

/-- `e_ALI = L⁺ · C / |F|`.
    Regime-dependent purely through `L⁺ = R.listSize`; for UDR `L⁺ = 1`. -/
def DeepAliCfg.aliErr (c : DeepAliCfg) (R : Regime) : Q :=
  let traceLen := c.densePCS.denseLen -- *TODO* rename denseLen to traceLen in FRIConfig at some point
  R.listSize c.densePCS.ρ traceLen * (c.numConstraints : Q) / (c.field.card : Q)

/-- `e_DEEP = L⁺ · (deg·(H + m_max − 1) + (H − 1)) / (|F| − H − D) / 2^grindDeep`,
    where `D = H / ρ` is the FRI evaluation domain size.
    The denominator is `|F| − H − D`, **not** `|F|` — see module docstring. -/
def DeepAliCfg.deepErr (c : DeepAliCfg) (R : Regime) : Q :=
  let traceLen := c.densePCS.denseLen -- *TODO* rename denseLen to traceLen in FRIConfig at some point
  let H  : Q := (traceLen : Q)
  let D  : Q := H / (c.densePCS.ρ : Q)
  let Lp : Q := R.listSize c.densePCS.ρ traceLen
  let num : Q := (c.airMaxDegree : Q) * (H + (c.maxCombo : Q) - 1) + (H - 1)
  Lp * num / ((c.field.card : Q) - H - D) / 2 ^ c.grindDeep

/-- Multi-point side condition: the decode window `(1 − θUB) · D` exceeds `H + m_max`.
    Uses `θUB` (upper bound on true θ) so the checked window is a lower bound on the
    true window — if the guard passes here it passes with the exact θ. -/
def DeepAliCfg.multiPointOk (c : DeepAliCfg) (R : Regime) : Prop :=
  let traceLength := c.densePCS.traceLen -- *TODO* rename denseLen to traceLen in FRIConfig at some point
  ((traceLength : Q) + (c.maxCombo : Q)) <
    (1 - R.θUB c.densePCS.ρ traceLength) * ((traceLength : Q) / (c.densePCS.ρ : Q))


/-! ## Cell error collection -/

/--
  Enumerates all the soundness errors of a DeepAli circuit for regime `R`:
  Batching, one commit cell per fold, query, ALI, DEEP, 4 lookups (regime-independent).
-/
def DeepAliCfg.listErrs (c: DeepAliCfg)(R: Regime) : List ℚ := do
  let mut l : List ℚ := []
  l := l ++ [c.densePCS.batchingErrPowers R]
  let fcfg := c.densePCS
  for i in List.range fcfg.rounds do
    l := l ++ [fcfg.commitErr (R) i]
  l := l ++ [c.densePCS.queryErr R]
  l := l ++ [c.aliErr R]
  l := l ++ [c.deepErr R]
  for lcfg in c.lookups do
    l := l ++ [lcfg.errUB]
  l

/-- Worst-case (maximum) error across all Airbender cells on regime R.
    `secBits (airbenderTotalErr R) = ((airbenderRounds R).map secBits).minimum` by `secBits_min'`. -/
def DeepAliCfg.totalErr (c: DeepAliCfg)(R: Regime) : ℚ :=
  (listErrs c R).foldr max 0

/-! ## Full DEEP-ALI proof size -/

private def getDeepAliProofSizes (c: DeepAliCfg) (expected: Bool) : ℕ :=
  let proofSizePCS :=
    if expected then c.densePCS.proofSizeExp
    else c.densePCS.proofSizeWorst

  proofSizePCS

def DeepAliCfg.proofSizeExp (c: DeepAliCfg) : ℕ :=
  getDeepAliProofSizes c true

def DeepAliCfg.proofSizeWorst (c: DeepAliCfg) : ℕ :=
  getDeepAliProofSizes c false

end Soundcalc
