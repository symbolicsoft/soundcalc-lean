import Soundcalc.Field.Core

/-! # KoalaBear — `p = 2^31 - 2^24 + 1`; SP1 uses its degree-4 extension, zkDTVM its degree-5. -/

namespace Soundcalc

/-- KoalaBear, `p = 2^31 - 2^24 + 1`; SP1 uses its degree-4 extension. -/
def koalaBear4 : FieldParams where
  p               := 2 ^ 31 - 2 ^ 24 + 1
  e               := 4
  twoAdicity      := 24
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-! ## S2 exit criteria (all kernel-checked, no `sorry`, no `native_decide`) -/

/-- `|F|` matches the Python `field.F` for SP1 core. -/
example : koalaBear4.card = (2 ^ 31 - 2 ^ 24 + 1) ^ 4 := by
  unfold FieldParams.card koalaBear4; norm_num

/-- Reusable pattern for evaluating `Nat.clog` without `decide`/`native_decide`
(it is well-founded recursion, so it does not reduce in the kernel): bound it
both ways via the characterization lemmas, then `omega`. -/
theorem koalaBear4_baseBits : koalaBear4.baseElementSizeBits = 31 :=
  koalaBear4.baseElementSizeBits_eq 31 (by norm_num [koalaBear4]) (by norm_num [koalaBear4])

/-- An extension-field element of KoalaBear⁴ is 124 bits (`31 · 4`). -/
theorem koalaBear4_elementBits : koalaBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, koalaBear4_baseBits]; rfl

/-- KoalaBear, degree-5 extension; zkDTVM runs over `KoalaBear⁵`. -/
def koalaBear5 : FieldParams where
  p               := 2 ^ 31 - 2 ^ 24 + 1
  e               := 5
  twoAdicity      := 24
  prime           := by norm_num
  epos            := by decide
  twoAdicity_spec := by decide

/-- `|F| = p⁵` for zkDTVM. -/
example : koalaBear5.card = (2 ^ 31 - 2 ^ 24 + 1) ^ 5 := by
  unfold FieldParams.card koalaBear5; norm_num

theorem koalaBear5_baseBits : koalaBear5.baseElementSizeBits = 31 :=
  koalaBear5.baseElementSizeBits_eq 31 (by norm_num [koalaBear5]) (by norm_num [koalaBear5])

/-- A KoalaBear⁵ element is 155 bits (`31 · 5`). -/
theorem koalaBear5_elementBits : koalaBear5.elementSizeBits = 155 := by
  rw [FieldParams.elementSizeBits, koalaBear5_baseBits]; rfl

end Soundcalc
