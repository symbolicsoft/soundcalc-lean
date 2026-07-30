import Soundcalc.Field.Core

/-! # Mersenne31 — `p = 2^31 − 1`; Airbender uses its degree-4 extension, `|F| ≈ 2^124`. -/

namespace Soundcalc

/-- Mersenne31, `p = 2^31 − 1`; Airbender uses its degree-4 extension, `|F| ≈ 2^124`. -/
def mersenne31_4 : FieldParams where
  p               := 2 ^ 31 - 1
  e               := 4
  twoAdicity      := 1
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-- `|F|` matches the Python `M31_4.F`. -/
example : mersenne31_4.card = (2 ^ 31 - 1) ^ 4 := by
  unfold FieldParams.card mersenne31_4; norm_num

/-- An M31⁴ element is 124 bits (`31 · 4`) — same sandwich proof as `koalaBear4_baseBits`. -/
theorem mersenne31_4_baseBits : mersenne31_4.baseElementSizeBits = 31 := by
  show Nat.clog 2 (2 ^ 31 - 1) = 31
  have hle : Nat.clog 2 (2 ^ 31 - 1) ≤ 31 := by
    rw [Nat.clog_le_iff_le_pow] <;> norm_num
  have hlt : 30 < Nat.clog 2 (2 ^ 31 - 1) := by
    rw [Nat.lt_clog_iff_pow_lt] <;> norm_num
  omega

theorem mersenne31_4_elementBits : mersenne31_4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, mersenne31_4_baseBits]; rfl

end Soundcalc
