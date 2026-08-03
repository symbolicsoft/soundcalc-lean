import Soundcalc.Field.Core

/-! # BabyBear — `p = 2^31 - 2^27 + 1`; OpenVM/OpenVM2 use its degree-4 extension. -/

namespace Soundcalc

/-- The BabyBear prime field, `p = 2^31 - 2^27 + 1`. -/
def babyBear : PrimeField where
  p               := 2 ^ 31 - 2 ^ 27 + 1
  prime           := by norm_num
  twoAdicity      := 27
  twoAdicity_spec := by decide

/-- BabyBear degree-4 extension; OpenVM/OpenVM2 use it. -/
def babyBear4 : FieldParams := babyBear.extension 4

/-- `|F|` matches the Python `BABYBEAR_4.F`. -/
example : babyBear4.card = (2 ^ 31 - 2 ^ 27 + 1) ^ 4 := by
  norm_num [FieldParams.card, babyBear4, PrimeField.extension, babyBear]

theorem babyBear4_baseBits : babyBear4.baseElementSizeBits = 31 :=
  babyBear4.baseElementSizeBits_eq 31 (by norm_num [babyBear4, PrimeField.extension, babyBear])
    (by norm_num [babyBear4, PrimeField.extension, babyBear])

theorem babyBear4_elementBits : babyBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, babyBear4_baseBits]; rfl

end Soundcalc
