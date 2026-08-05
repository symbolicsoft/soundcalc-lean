# Monotonicity — theorem reference

Monotonicity / optimality theorems for the PCS soundness and proof-size formulas: the "more than a
point-wise calculator" layer. One-line summary of every theorem in `Soundcalc/Monotonicity/`.

## Shared quantities (referenced by several theorems)

- **Query cell** — FRI's `queryErr` and WHIR's `epsilonQuery` share the shape
  `ε = (1 − θ)ᵗ / 2ᵍ`, for a decoding radius `θ`, query count `t`, and query-phase grinding `g`.
- **FRI decoding radius** — UDR: `θ = (1 − ρ)/2`; JBR (Johnson): `θ ≈ (1 − η) − √ρ`.
- **WHIR per-iteration recurrence** — `mᵢ₊₁ = mᵢ − kᵢ` (log-degree) and `μᵢ₊₁ = μᵢ + (kᵢ − 1)`
  (log-inverse-rate), so the rate `ρᵢ = 2^(−μᵢ)` falls every iteration while the degree shrinks.
- **Linear (Schwartz–Zippel) error** — `errLinear = (θ·(d/ρ) + 1) / |F|`, numerator `≥ 1`.
- **Field ceiling** — `secBits(1/|F|) = ⌊log₂ |F|⌋`, the most bits an algebraic cell can report.

---

## `Basic.lean` — shared foundations

| theorem | description |
|---|---|
| `two_sqrt_le` | AM–GM root `2√ρ ≤ 1 + ρ`; both the FRI radius and WHIR agreement bounds are corollaries. |
| `scanl_step_le` | `scanl` is non-decreasing when every step is (`x ≤ f x a`). |
| `scanl_step_ge` | `scanl` is non-increasing when every step is (`f x a ≤ x`). |
| `queryShape_antitone_radius` | The query cell `(1 − θ)ᵗ/2ᵍ` is antitone in the decoding radius `θ`. |
| `secBits_queryShape_mono_radius` | A larger decoding radius never gives fewer query-cell bits. |
| `queryShape_antitone_numQueries` | The query cell is antitone in the query count `t` (base `≤ 1`). |
| `secBits_queryShape_mono_numQueries` | More queries never reduce query-cell security. |
| `FieldParams.card_pos` | `0 < |F|`. |
| `secBits_le_field` | Field ceiling: `1/|F| ≤ ε ⇒ secBits ε ≤ secBits(1/|F|)`. |
| `secBits_grind` | Grinding is exactly additive: `secBits(ε / 2ᵍ) = secBits ε + g`. |
| `secBits_grinded_le_field` | A grinded algebraic cell reports `≤ ⌊log₂|F|⌋ + g` bits (statistical + PoW). |

## `Regime.lean` — Johnson vs. unique decoding

| theorem | description |
|---|---|
| `johnson_beats_unique` | The Johnson radius `1 − √ρ` beats the unique-decoding radius `(1−ρ)/2` (slack `(1−√ρ)²/2`). |
| `one_div_card_le_errLinear` | The linear soundness error is `≥ 1/|F|`, so the field ceiling bites on algebraic cells. |
| `secBits_errLinear_le_field` | The linear cell can never report more bits than the field baseline `⌊log₂|F|⌋`. |
| `UDR_errLinear_mono_dim` | The linear error is monotone in the dimension `d` — smaller instance ⇒ more sound. |

## `FRI.lean`

Uses the query cell `queryErr R = (1 − θLB)^numQueries / 2^grindQuery` and the proof-size accumulator
`getFRIProofSizeBits`.

| theorem | description |
|---|---|
| `FRIConfig.queryErr_antitone_radius` | `queryErr` is antitone in the decoding radius `θLB` (larger radius ⇒ smaller error). |
| `FRIConfig.queryBits_mono` | Larger radius ⇒ at least as many query-cell bits (`UDR ≤ JBR` on the query cell). |
| `getSizeOfMerkleProofBits_mono_tupleSize` | A bigger folding factor makes each Merkle opening larger (the folding-leaf cost). |
| `getSizeOfMerkleMultiProofBits_worst_mono_numOpenings` | Worst-case multi-proof grows with the query count (the shared proof-size atom). |
| `friFold_mono` | The proof-size `foldl` is monotone in `numQueries` (domain thread shared, bit thread grows). |
| `getFRIProofSizeBits_mono_numQueries` | **No free lunch:** the FRI proof size grows with `numQueries` (pairs with the security gain). |
| `UDR_errPowers_mono_batch` | **Batching soundness cost:** `errPowers = errLinear·(batch−1)` grows with `batchSize`. |
| `getSizeOfMerkleMultiProofBits_worst_mono_tupleSize` | Worst multi-proof grows with the folding-leaf size `tupleSize`. |
| `getFRIProofSizeBits_mono_batchSize` | **Batching proof-size cost:** more batched polys ⇒ bigger proof (they ride the initial multi-proof). |
| `friAcc_mono` | The accumulated folding factor `∏_{j≤i} kⱼ` grows with the round `i`. |
| `friDimension_antitone` | **The folded dimension shrinks each round** — the FRI analog of `logDegree_anti`; with `UDR_errLinear_mono_dim`, later rounds are more secure. |

## `WHIR.lean`

Uses the query cell `epsilonQuery R i = (1 − δᵢ)^tᵢ / 2^gᵢ` and the per-iteration recurrence
`mᵢ₊₁ = mᵢ − kᵢ`, `μᵢ₊₁ = μᵢ + (kᵢ − 1)`.

| theorem | description |
|---|---|
| `WHIRConfig.epsilonQuery_antitone_radius` | `epsilonQuery` is antitone in the decoding radius `δᵢ` (FRI analog). |
| `WHIRConfig.epsilonQuery_bits_mono` | Larger radius ⇒ at least as many query-cell bits (FRI analog). |
| `whir_agreement_list_le_unique` | List-regime agreement `√ρ·(1 + 1/2m)` ≤ unique `(1+ρ)/2` — exactly when `√ρ ≤ m·(1−√ρ)²`. |
| `whir_listSize_ge_one` | List-regime list size `(m+½)/√ρ ≥ 1` — the cost that offsets the query-cell win. |
| `WHIRConfig.logInvRate_mono` | The rate falls every iteration (`μᵢ ≤ μᵢ₊₁`) — WHIR's fixed-domain-shift signature. |
| `WHIRConfig.logDegree_anti` | The degree shrinks every iteration (`mᵢ₊₁ ≤ mᵢ`). |
