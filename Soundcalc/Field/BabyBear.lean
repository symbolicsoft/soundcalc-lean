import Soundcalc.Field.Core

/-! # BabyBear — `p = 2^31 - 2^27 + 1`; OpenVM/OpenVM2 use its degree-4 extension. -/

namespace Soundcalc

/-- BabyBear, `p = 2^31 - 2^27 + 1`; OpenVM uses its degree-4 extension. -/
def babyBear4 : FieldParams where
  p               := 2 ^ 31 - 2 ^ 27 + 1
  e               := 4
  twoAdicity      := 27
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-- `|F|` matches the Python `BABYBEAR_4.F`. -/
example : babyBear4.card = (2 ^ 31 - 2 ^ 27 + 1) ^ 4 := by
  unfold FieldParams.card babyBear4; norm_num

theorem babyBear4_baseBits : babyBear4.baseElementSizeBits = 31 := by
  show Nat.clog 2 (2 ^ 31 - 2 ^ 27 + 1) = 31
  have hle : Nat.clog 2 (2 ^ 31 - 2 ^ 27 + 1) ≤ 31 := by
    rw [Nat.clog_le_iff_le_pow] <;> norm_num
  have hlt : 30 < Nat.clog 2 (2 ^ 31 - 2 ^ 27 + 1) := by
    rw [Nat.lt_clog_iff_pow_lt] <;> norm_num
  omega

theorem babyBear4_elementBits : babyBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, babyBear4_baseBits]; rfl

end Soundcalc
