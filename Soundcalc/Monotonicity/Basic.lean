import Soundcalc.SecBits
import Soundcalc.Field.Core

/-!
# Monotonicity — shared foundations

The pieces every proof-system-specific monotonicity file (`Monotonicity.FRI`, `.WHIR`, `.Regime`)
builds on:

* `two_sqrt_le` — the AM–GM root `2√ρ ≤ 1 + ρ` behind both the FRI radius bound and the WHIR
  agreement bound.
* `secBits_le_field` / `secBits_grind` / `secBits_grinded_le_field` — the field ceiling and the
  fact that grinding is *exactly* additive in security bits (statistical + PoW decomposition).
* `scanl_step_le` / `scanl_step_ge` — `scanl` monotonicity, used for WHIR's per-iteration rate/degree.
-/

namespace Soundcalc

/-! ## The AM–GM root -/

/-- **The root** (AM–GM / `(1-√ρ)² ≥ 0`): `2√ρ ≤ 1 + ρ`. Both the FRI radius bound and the WHIR
agreement bound are corollaries. (In `ℝ`, since `√ρ` is irrational in general.) -/
theorem two_sqrt_le {ρ : ℝ} (h0 : 0 ≤ ρ) : 2 * Real.sqrt ρ ≤ 1 + ρ := by
  nlinarith [sq_nonneg (1 - Real.sqrt ρ), Real.sq_sqrt h0, Real.sqrt_nonneg ρ]

/-! ## `scanl` monotonicity -/

/-- `scanl` with a per-step non-decreasing update is non-decreasing (consecutive form). -/
theorem scanl_step_le {α : Type*} (f : ℕ → α → ℕ) (hf : ∀ x a, x ≤ f x a) :
    ∀ (b : ℕ) (l : List α) (i : ℕ), i < l.length →
      (List.scanl f b l).getD i 0 ≤ (List.scanl f b l).getD (i + 1) 0 := by
  intro b l
  induction l generalizing b with
  | nil => intro i hi; simp at hi
  | cons a l' ih =>
    intro i hi
    cases i with
    | zero => simpa using hf b a
    | succ j => simpa using ih (f b a) j (by simpa using hi)

/-- `scanl` with a per-step non-increasing update is non-increasing (consecutive form). -/
theorem scanl_step_ge {α : Type*} (f : ℕ → α → ℕ) (hf : ∀ x a, f x a ≤ x) :
    ∀ (b : ℕ) (l : List α) (i : ℕ), i < l.length →
      (List.scanl f b l).getD (i + 1) 0 ≤ (List.scanl f b l).getD i 0 := by
  intro b l
  induction l generalizing b with
  | nil => intro i hi; simp at hi
  | cons a l' ih =>
    intro i hi
    cases i with
    | zero => simpa using hf b a
    | succ j => simpa using ih (f b a) j (by simpa using hi)

/-! ## Query-cell shape monotonicity (shared by FRI `queryErr` and WHIR `epsilonQuery`)

Both PCSs' query cells have the same shape `(1 - θ)^t / 2^g` — a decoding radius `θ`, a query
count `t`, and query-phase grinding `g`. These generic lemmas are the shared core; `Monotonicity.FRI`
and `Monotonicity.WHIR` each wrap them for their config's cell. -/

/-- A query cell `(1 - θ)^t / 2^g` is **antitone in the decoding radius** `θ`. -/
theorem queryShape_antitone_radius {θ θ' : ℚ} (hle : θ ≤ θ') (h1 : θ' ≤ 1) (t g : ℕ) :
    (1 - θ') ^ t / 2 ^ g ≤ (1 - θ) ^ t / 2 ^ g := by
  have h0' : (0 : ℚ) ≤ 1 - θ' := by linarith
  have hmono : (1 : ℚ) - θ' ≤ 1 - θ := by linarith
  gcongr

/-- A larger decoding radius never gives fewer query-cell security bits. -/
theorem secBits_queryShape_mono_radius {θ θ' : ℚ} (hle : θ ≤ θ') (h1 : θ' < 1) (t g : ℕ) :
    secBits ((1 - θ) ^ t / 2 ^ g) ≤ secBits ((1 - θ') ^ t / 2 ^ g) := by
  apply secBits_anti
  · have : 0 < 1 - θ' := by linarith
    positivity
  · exact queryShape_antitone_radius hle (le_of_lt h1) t g

/-- A query cell `(1 - θ)^t / 2^g` is **antitone in the query count** `t` (base `≤ 1`). -/
theorem queryShape_antitone_numQueries {θ : ℚ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t t' : ℕ}
    (h : t ≤ t') (g : ℕ) :
    (1 - θ) ^ t' / 2 ^ g ≤ (1 - θ) ^ t / 2 ^ g := by
  have hpow : (1 - θ) ^ t' ≤ (1 - θ) ^ t := pow_le_pow_of_le_one (by linarith) (by linarith) h
  gcongr

/-- More queries never reduce query-cell security (the "minimum queries for a target" enabler). -/
theorem secBits_queryShape_mono_numQueries {θ : ℚ} (h0 : 0 ≤ θ) (h1 : θ < 1) {t t' : ℕ}
    (h : t ≤ t') (g : ℕ) :
    secBits ((1 - θ) ^ t / 2 ^ g) ≤ secBits ((1 - θ) ^ t' / 2 ^ g) := by
  apply secBits_anti
  · have : 0 < 1 - θ := by linarith
    positivity
  · exact queryShape_antitone_numQueries h0 (le_of_lt h1) h g

/-! ## The field ceiling and grinding decomposition -/

/-- The base field cardinality is positive. -/
theorem FieldParams.card_pos (F : FieldParams) : 0 < F.card := by
  simpa [FieldParams.card] using pow_pos F.prime.pos F.e

/-- **Field ceiling.** Every algebraic cell error has the form `(≥ 1)/|F|`, so `1/|F| ≤ ε`; hence no
such cell can report more security bits than the field baseline `secBits (1/|F|) = ⌊log₂|F|⌋`. -/
theorem secBits_le_field {ε : ℚ} {card : ℕ} (hcard : 0 < card) (hlo : 1 / (card : ℚ) ≤ ε) :
    secBits ε ≤ secBits (1 / (card : ℚ)) := by
  have : (0 : ℚ) < (card : ℚ) := by exact_mod_cast hcard
  exact secBits_anti (by positivity) hlo

/-- **Grinding is exactly additive in security bits.** Dividing an error `ε ∈ (0,1]` by `2^g`
(proof-of-work of `g` bits) raises `secBits` by *exactly* `g`. (The codebase author anticipated
this — see `secBits_ge`'s docstring.) -/
theorem secBits_grind {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) (g : ℕ) :
    secBits (ε / 2 ^ g) = secBits ε + g := by
  have h2g : (0 : ℚ) < 2 ^ g := by positivity
  have hδpos : 0 < ε / 2 ^ g := by positivity
  have h1g : (1 : ℚ) ≤ 2 ^ g := by exact_mod_cast Nat.one_le_pow g 2 (by norm_num)
  have hδ1 : ε / 2 ^ g ≤ 1 := by rw [div_le_one h2g]; linarith
  refine le_antisymm ?_ ?_
  · by_contra hc
    have hk : secBits ε + g + 1 ≤ secBits (ε / 2 ^ g) := by omega
    have hle : ε / 2 ^ g ≤ 1 / 2 ^ (secBits ε + g + 1) := le_secBits_if _ hδpos hδ1 _ hk
    rw [div_le_div_iff₀ h2g (by positivity), one_mul,
        show secBits ε + g + 1 = (secBits ε + 1) + g by omega, pow_add] at hle
    have hεsmall : ε ≤ 1 / 2 ^ (secBits ε + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have hle' : (ε * 2 ^ (secBits ε + 1)) * 2 ^ g ≤ 1 * 2 ^ g := by
        rw [one_mul, mul_assoc]; exact hle
      exact le_of_mul_le_mul_right hle' h2g
    have : secBits ε + 1 ≤ secBits ε := secBits_ge ε hε _ hεsmall
    omega
  · apply secBits_ge _ hδpos
    have hεbnd : ε ≤ 1 / 2 ^ secBits ε := (le_secBits_iff ε hε hε1 (secBits ε)).mp le_rfl
    calc ε / 2 ^ g ≤ (1 / 2 ^ secBits ε) / 2 ^ g := by gcongr
      _ = 1 / 2 ^ (secBits ε + g) := by rw [pow_add]; ring

/-- **Field ceiling + PoW, for a grinded cell.** A reported cell of the form `algErr / 2^g` where
the algebraic error is `≥ 1/|F|` (and `≤ 1`) reports at most `⌊log₂|F|⌋ + g` bits: statistical
security capped by the field, plus exactly the grinding bits on top. This is the shape of the real
FRI/lookup cells — `batchingErr = errMultilinear/2^grindBatch`, `commitErr = errPowers/2^grindCommit`,
`errUB = (baseError+gkr)/2^grindBitsLookup` — so it applies to each via the matching
`1/|F| ≤ algErr` connector (e.g. `one_div_card_le_errLinear`). -/
theorem secBits_grinded_le_field {alg : ℚ} {card g : ℕ} (hcard : 0 < card)
    (hlo : 1 / (card : ℚ) ≤ alg) (hhi : alg ≤ 1) :
    secBits (alg / 2 ^ g) ≤ secBits (1 / (card : ℚ)) + g := by
  have hcardQ : (0 : ℚ) < (card : ℚ) := by exact_mod_cast hcard
  have halgpos : 0 < alg := lt_of_lt_of_le (by positivity) hlo
  rw [secBits_grind halgpos hhi g]
  exact Nat.add_le_add_right (secBits_le_field hcard hlo) g

/-- **Grinding is antitone.** Dividing a nonnegative error by more PoW bits never increases it — the
shared `grind ↓` mechanism behind every grinded cell (`queryErr`, `batchingErr`, `commitErr`,
`deepErr`, `errUB`). -/
theorem div_pow_two_antitone {a : ℚ} (ha : 0 ≤ a) {g g' : ℕ} (h : g ≤ g') :
    a / 2 ^ g' ≤ a / 2 ^ g := by
  have hg : (2 : ℚ) ^ g ≤ 2 ^ g' := by gcongr; norm_num
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact mul_le_mul_of_nonneg_left hg ha

end Soundcalc
