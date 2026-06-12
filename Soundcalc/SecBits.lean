import Mathlib

/-!
# secBits, and one cell of `reports/sp1.md`

Milestone M0 seed. This `secBits` handles only the shapes the example needs;
the library version will be total, specified by `le_secBits_iff`, and proved
against it.
-/

namespace Soundcalc

/-- Bits of security of a rational error: the largest `k` with `ε ≤ 2 ^ (-k)`.
For `0 < ε ≤ 1` this is `⌊log₂ (1 / ε)⌋`, computed on numerator/denominator. -/
def secBits (ε : ℚ) : ℕ :=
  if ε ≤ 0 then 0
  else (ε.den / ε.num.toNat).log2

/-- SP1 core, query phase, UDR: θ = 3/8, 124 queries, 16 grinding bits. -/
def sp1CoreQueryErr : ℚ := (5 / 8) ^ 124 / 2 ^ 16

/-- One cell of `reports/sp1.md`, as a kernel-checked fact. -/
theorem sp1_core_query_bits : secBits sp1CoreQueryErr = 100 := by decide

/-- The two-sided check, directly against the spec shape:
`2 ^ (-101) < ε ≤ 2 ^ (-100)`. -/
theorem sp1_core_query_bound :
    sp1CoreQueryErr ≤ 1 / 2 ^ 100 ∧ 1 / 2 ^ 101 < sp1CoreQueryErr := by
  constructor <;> norm_num [sp1CoreQueryErr]

end Soundcalc
