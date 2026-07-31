import Soundcalc.Field.Core

/-! # KoalaBear — `p = 2^31 - 2^24 + 1`; SP1 uses its degree-4 extension, zkDTVM its degree-5. -/

namespace Soundcalc

/-- The KoalaBear prime field, `p = 2^31 - 2^24 + 1`. -/
def koalaBear : PrimeField where
  p               := 2 ^ 31 - 2 ^ 24 + 1
  prime           := by norm_num
  twoAdicity      := 24
  twoAdicity_spec := by decide

/-- KoalaBear degree-4 extension; SP1 uses it. -/
def koalaBear4 : FieldParams := koalaBear.extension 4
/-- KoalaBear degree-5 extension; zkDTVM uses it. -/
def koalaBear5 : FieldParams := koalaBear.extension 5

/-! ## S2 exit criteria (all kernel-checked, no `sorry`, no `native_decide`) -/

/-- `|F|` matches the Python `field.F` for SP1 core. -/
example : koalaBear4.card = (2 ^ 31 - 2 ^ 24 + 1) ^ 4 := by
  norm_num [FieldParams.card, koalaBear4, PrimeField.extension, koalaBear]

/-- Reusable pattern for evaluating `Nat.clog` without `decide`/`native_decide`
(it is well-founded recursion, so it does not reduce in the kernel): bound it
both ways via the characterization lemmas, then `omega`. -/
theorem koalaBear4_baseBits : koalaBear4.baseElementSizeBits = 31 :=
  koalaBear4.baseElementSizeBits_eq 31 (by norm_num [koalaBear4, PrimeField.extension, koalaBear])
    (by norm_num [koalaBear4, PrimeField.extension, koalaBear])

/-- An extension-field element of KoalaBear⁴ is 124 bits (`31 · 4`). -/
theorem koalaBear4_elementBits : koalaBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, koalaBear4_baseBits]; rfl

/-- A KoalaBear⁵ element is 155 bits (`31 · 5`); shares the base bits with `koalaBear4`. -/
theorem koalaBear5_baseBits : koalaBear5.baseElementSizeBits = 31 :=
  koalaBear5.baseElementSizeBits_eq 31 (by norm_num [koalaBear5, PrimeField.extension, koalaBear])
    (by norm_num [koalaBear5, PrimeField.extension, koalaBear])

theorem koalaBear5_elementBits : koalaBear5.elementSizeBits = 155 := by
  rw [FieldParams.elementSizeBits, koalaBear5_baseBits]; rfl

end Soundcalc
