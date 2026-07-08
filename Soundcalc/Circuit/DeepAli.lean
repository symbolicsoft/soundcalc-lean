import Mathlib
import Soundcalc.SecBits
import Soundcalc.Regime
import Soundcalc.PCS.FRI

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
  field          : FieldParams
  ρ              : Rate
  traceLength    : N    -- H = 2^24 (also the FRI dimension for Airbender)
  numConstraints : N    -- C = 928
  airMaxDegree   : N    -- deg = 2
  maxCombo       : N    -- m_max = 2 (max column entries in one constraint)
  grindDeep      : N    -- = 12

/-- Airbender DEEP-ALI configuration (eprint 2022/1216, Thm 8). -/
def airbenderDeepAli : DeepAliCfg where
  field          := mersenne31_4
  ρ              := ⟨1/2, by norm_num, by norm_num⟩
  traceLength    := 2^24
  numConstraints := 928
  airMaxDegree   := 2
  maxCombo       := 2
  grindDeep      := 12

/-- `e_ALI = L⁺ · C / |F|`.
    Regime-dependent purely through `L⁺ = R.listSize`; for UDR `L⁺ = 1`. -/
def DeepAliCfg.aliErr (c : DeepAliCfg) (R : Regime) : Q :=
  R.listSize c.ρ c.traceLength * (c.numConstraints : Q) / (c.field.card : Q)

/-- `e_DEEP = L⁺ · (deg·(H + m_max − 1) + (H − 1)) / (|F| − H − D) / 2^grindDeep`,
    where `D = H / ρ` is the FRI evaluation domain size.
    The denominator is `|F| − H − D`, **not** `|F|` — see module docstring. -/
def DeepAliCfg.deepErr (c : DeepAliCfg) (R : Regime) : Q :=
  let H  : Q := (c.traceLength : Q)
  let D  : Q := H / (c.ρ : Q)
  let Lp : Q := R.listSize c.ρ c.traceLength
  let num : Q := (c.airMaxDegree : Q) * (H + (c.maxCombo : Q) - 1) + (H - 1)
  Lp * num / ((c.field.card : Q) - H - D) / 2 ^ c.grindDeep

/-- Multi-point side condition (`fri.py`/`deep_ali.py: 164` runtime assert): the decode
    window `(1 − θ) · D` strictly exceeds the trace-plus-combo length `H + m_max`.
    Checked separately for each regime because `θ_JBR ≠ θ_UDR`; a config that
    satisfied UDR but violated the JBR window would be an unsound silent skip. -/
theorem DeepAliCfg.multiPoint_ok (c : DeepAliCfg) (R : Regime)
    (hc : c = airbenderDeepAli)
    (hR : R = UDR c.field ∨ R = JBR c.field (1/40) (2^40)) :
    ((c.traceLength : Q) + (c.maxCombo : Q)) <
      (1 - R.θUB c.ρ c.traceLength) * ((c.traceLength : Q) / (c.ρ : Q)) := by
  subst hc
  rcases hR with rfl | rfl <;> native_decide

/-! ## A4 exit criteria -/

example : secBits (airbenderDeepAli.aliErr (UDR mersenne31_4)) = 114 := by native_decide
example : secBits (airbenderDeepAli.deepErr (UDR mersenne31_4)) = 110 := by native_decide
example : secBits (airbenderDeepAli.aliErr (JBR mersenne31_4 (1/40) (2^40))) = 109 := by native_decide
example : secBits (airbenderDeepAli.deepErr (JBR mersenne31_4 (1/40) (2^40))) = 105 := by native_decide

end Soundcalc
