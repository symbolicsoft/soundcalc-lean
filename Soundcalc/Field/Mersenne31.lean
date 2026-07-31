import Soundcalc.Field.Core

/-! # Mersenne31 — `p = 2^31 − 1`; Airbender uses its degree-4 extension, `|F| ≈ 2^124`. -/

namespace Soundcalc

/-- The Mersenne31 prime field, `p = 2^31 − 1`. -/
def mersenne31 : PrimeField where
  p               := 2 ^ 31 - 1
  prime           := by norm_num
  twoAdicity      := 1
  twoAdicity_spec := by decide

/-- Mersenne31 degree-4 extension; Airbender uses it, `|F| ≈ 2^124`. -/
def mersenne31_4 : FieldParams := mersenne31.extension 4

/-- `|F|` matches the Python `M31_4.F`. -/
example : mersenne31_4.card = (2 ^ 31 - 1) ^ 4 := by
  norm_num [FieldParams.card, mersenne31_4, PrimeField.extension, mersenne31]

/-- An M31⁴ element is 124 bits (`31 · 4`) — same sandwich proof as `koalaBear4_baseBits`. -/
theorem mersenne31_4_baseBits : mersenne31_4.baseElementSizeBits = 31 :=
  mersenne31_4.baseElementSizeBits_eq 31 (by norm_num [mersenne31_4, PrimeField.extension, mersenne31])
    (by norm_num [mersenne31_4, PrimeField.extension, mersenne31])

theorem mersenne31_4_elementBits : mersenne31_4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, mersenne31_4_baseBits]; rfl

end Soundcalc
