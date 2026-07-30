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

theorem babyBear4_baseBits : babyBear4.baseElementSizeBits = 31 :=
  babyBear4.baseElementSizeBits_eq 31 (by norm_num [babyBear4]) (by norm_num [babyBear4])

theorem babyBear4_elementBits : babyBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, babyBear4_baseBits]; rfl

end Soundcalc
