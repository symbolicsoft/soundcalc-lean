import Soundcalc.Field.Core

/-! # KoalaBear — `p = 2^31 - 2^24 + 1`; SP1 uses its degree-4 extension. -/

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
theorem koalaBear4_baseBits : koalaBear4.baseElementSizeBits = 31 := by
  show Nat.clog 2 (2 ^ 31 - 2 ^ 24 + 1) = 31
  have hle : Nat.clog 2 (2 ^ 31 - 2 ^ 24 + 1) ≤ 31 := by
    rw [Nat.clog_le_iff_le_pow]
    norm_num
    norm_num
  have hlt : 30 < Nat.clog 2 (2 ^ 31 - 2 ^ 24 + 1) := by
    rw [Nat.lt_clog_iff_pow_lt]
    norm_num
    norm_num
  omega

/-- An extension-field element of KoalaBear⁴ is 124 bits (`31 · 4`). -/
theorem koalaBear4_elementBits : koalaBear4.elementSizeBits = 124 := by
  rw [FieldParams.elementSizeBits, koalaBear4_baseBits]; rfl

end Soundcalc
