# Monotonicity — theorem reference

Monotonicity / optimality theorems for the PCS soundness and proof-size formulas: the "more than a
point-wise calculator" layer.

Each file is organised in **two tiers**:

- **Catalogue** — the user-facing results. Config-level theorems that say how a *cell* (soundness
  error, security bits, or proof size) moves when you turn one *knob* — either a configuration field
  (`{c with numQueries := …}`) or the decoding regime (UDR vs JBR). These are the rows of the
  sensitivity catalog below.
- **Foundations** — the bare-parameter mechanisms the catalogue is built from (the query-cell shape,
  the Merkle proof-size atoms, the `scanl`/`foldl` monotonicities, the real-analysis facts). Not
  user-facing; they are the proof toolkit.

## Shared quantities (referenced by several theorems)

- **Query cell** — FRI's `queryErr` and WHIR's `epsilonQuery` share the shape
  `ε = (1 − θ)ᵗ / 2ᵍ`, for a decoding radius `θ`, query count `t`, and query-phase grinding `g`.
- **FRI decoding radius** — UDR: `θ = (1 − ρ)/2`; JBR (Johnson): `θ ≈ (1 − η) − √ρ`.
- **WHIR per-iteration recurrence** — `mᵢ₊₁ = mᵢ − kᵢ` (log-degree) and `μᵢ₊₁ = μᵢ + (kᵢ − 1)`
  (log-inverse-rate), so the rate `ρᵢ = 2^(−μᵢ)` falls every iteration while the degree shrinks.
- **Linear (Schwartz–Zippel) error** — `errLinear = ((1−ρ)/2·(d/ρ) + 1) / |F|`; the powers-batching
  error is `errPowers = errLinear·(batch − 1)`.
- **Field ceiling** — `secBits(1/|F|) = ⌊log₂ |F|⌋`, the most bits an algebraic cell can report.

---

## Sensitivity catalog

How each error term moves as a knob **grows** — `↓` error falls (security rises), `↑` error rises,
`—` the knob does not occur, `∗` provably non-monotone (interior optimum). Directions verified
against the UDR formulas; each has (or will have) a backing lemma. `H` is the trace/dense length.

| Error term | queries `q` | grind | rate `ρ` | `H` | batch | `\|F\|` | backing lemma(s) |
|---|:---:|:---:|:---:|:---:|:---:|:---:|---|
| FRI query `(1−θ)^q/2^g` | ↓ | ↓ | ↑ | — | — | — | `queryErr_antitone_numQueries`, `queryErr_antitone_radius` |
| FRI commit / batching | — | ↓ | ↓ | ↑ | ↑ | ↓ | `batchingErr_mono_batchSize`; `UDR_errLinear_mono_dim` (H); ρ, `\|F\|`: *planned* |
| FRI proof size | ↑ | — | — | — | ↑ | — | `proofSizeWorst_mono_numQueries`, `proofSizeWorst_mono_batchSize` |
| ALI `L⁺·C/\|F\|` | — | — | — | — | — | ↓ | *planned* (`DeepAliCfg`) |
| DEEP | — | ↓ | ↓ | ↑ | — | ↓ | *planned* (`DeepAliCfg`) |
| LogUp / GKR | — | ↓ | — | ↑ | ↑ | ↓ | *planned* (`LookupCfg`) |
| JBR gap `η` / multiplicity `m` | | | | | | | `η`: ↓ error; `m`: ∗ — `whir_agreement_list_le_unique` + `whir_listSize_ge_one` |

Currently populated: the FRI query, commit/batching (partial), and proof-size rows. The ALI / DEEP /
LogUp rows and the ρ / `|F|` cells are the follow-up (new configs, not yet lifted).

---

## `FRI.lean`

Query cell `queryErr R = (1 − θLB)^numQueries / 2^grindQuery`; proof-size accumulator
`getFRIProofSizeBits`. The record-update knobs are `numQueries` and `batchSize` (the others —
`denseLen`, `ρ`, `foldingFactors` — are pinned together by the config's `h_earlyStop` invariant).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `FRIConfig.queryErr_antitone_radius` | regime | `queryErr` is antitone in the decoding radius `θLB` (larger radius ⇒ smaller error). |
| `FRIConfig.queryBits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (`UDR ≤ JBR` on the query cell). |
| `FRIConfig.queryErr_antitone_numQueries` | `numQueries` | More queries never raise the query-cell error. |
| `FRIConfig.queryBits_mono_numQueries` | `numQueries` | More queries never lower the query-cell security (benefit side). |
| `FRIConfig.proofSizeWorst_mono_numQueries` | `numQueries` | **No free lunch:** more queries never shrink the proof (cost side). |
| `FRIConfig.batchingErr_mono_batchSize` | `batchSize` | **Batching soundness cost:** more batched polys ⇒ larger batching error (`power_batching` path). |
| `FRIConfig.proofSizeWorst_mono_batchSize` | `batchSize` | **Batching proof-size cost:** the batched polys ride the initial multi-proof, so more of them ⇒ bigger proof. |

### Foundations

| theorem | description |
|---|---|
| `getSizeOfMerkleProofBits_mono_tupleSize` | A bigger folding factor makes each Merkle opening larger (the folding-leaf cost). |
| `getSizeOfMerkleMultiProofBits_worst_mono_numOpenings` | Worst-case multi-proof grows with the query count (the shared proof-size atom). |
| `getSizeOfMerkleMultiProofBits_worst_mono_tupleSize` | Worst multi-proof grows with the folding-leaf size `tupleSize`. |
| `friFold_mono` | The proof-size `foldl` is monotone in `numQueries` (domain thread shared, bit thread grows). |
| `getFRIProofSizeBits_mono_numQueries` / `_mono_batchSize` | Bare-parameter proof-size monotonicity (lifted to the catalogue above). |
| `UDR_errPowers_mono_batch` | Regime-level: `errPowers = errLinear·(batch−1)` grows with `batchSize` (lifted above). |
| `friAcc_mono` | The accumulated folding factor `∏_{j≤i} kⱼ` grows with the round `i`. |
| `friDimension_antitone` | **The folded dimension shrinks each round** — the FRI analog of `logDegree_anti`; with `UDR_errLinear_mono_dim`, later rounds are more secure. |

## `WHIR.lean`

Query cell `epsilonQuery R i = (1 − δᵢ)^tᵢ / 2^gᵢ`; per-iteration recurrence `mᵢ₊₁ = mᵢ − kᵢ`,
`μᵢ₊₁ = μᵢ + (kᵢ − 1)`. WHIR has no record-update config-field knob (its query counts `tᵢ` are a
list, so the query-count sensitivity is the shared shape lemma in `Basic.lean`).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `WHIRConfig.epsilonQuery_antitone_radius` | regime | `epsilonQuery` is antitone in the decoding radius `δᵢ` (FRI analog). |
| `WHIRConfig.epsilonQuery_bits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (FRI analog). |
| `WHIRConfig.logInvRate_mono` | round `i` | The rate falls every iteration (`μᵢ ≤ μᵢ₊₁`) — WHIR's fixed-domain-shift signature (no FRI analog). |
| `WHIRConfig.logDegree_anti` | round `i` | The degree shrinks every iteration (`mᵢ₊₁ ≤ mᵢ`). |

### Foundations

| theorem | description |
|---|---|
| `whir_agreement_list_le_unique` | List-regime agreement `√ρ·(1 + 1/2m)` ≤ unique `(1+ρ)/2` — exactly when `√ρ ≤ m·(1−√ρ)²`. |
| `whir_listSize_ge_one` | List-regime list size `(m+½)/√ρ ≥ 1` — the cost that offsets the query-cell win. |

## `Regime.lean` — foundations (Johnson vs. unique decoding, field ceiling)

| theorem | description |
|---|---|
| `johnson_beats_unique` | The Johnson radius `1 − √ρ` beats the unique-decoding radius `(1−ρ)/2` (slack `(1−√ρ)²/2`). |
| `one_div_card_le_errLinear` | The linear soundness error is `≥ 1/|F|`, so the field ceiling bites on algebraic cells. |
| `secBits_errLinear_le_field` | The linear cell can never report more bits than the field baseline `⌊log₂|F|⌋`. |
| `UDR_errLinear_mono_dim` | The linear error is monotone in the dimension `d` — smaller instance ⇒ more sound (lifted by FRI's `H` cells). |

## `Basic.lean` — shared foundations

| theorem | description |
|---|---|
| `two_sqrt_le` | AM–GM root `2√ρ ≤ 1 + ρ`; both the FRI radius and WHIR agreement bounds are corollaries. |
| `scanl_step_le` / `scanl_step_ge` | `scanl` is non-decreasing / non-increasing when every step is. |
| `queryShape_antitone_radius` | The query cell `(1 − θ)ᵗ/2ᵍ` is antitone in the decoding radius `θ`. |
| `secBits_queryShape_mono_radius` | A larger decoding radius never gives fewer query-cell bits. |
| `queryShape_antitone_numQueries` | The query cell is antitone in the query count `t` (base `≤ 1`). |
| `secBits_queryShape_mono_numQueries` | More queries never reduce query-cell security. |
| `FieldParams.card_pos` | `0 < |F|`. |
| `secBits_le_field` | Field ceiling: `1/|F| ≤ ε ⇒ secBits ε ≤ secBits(1/|F|)`. |
| `secBits_grind` | Grinding is exactly additive: `secBits(ε / 2ᵍ) = secBits ε + g`. |
| `secBits_grinded_le_field` | A grinded algebraic cell reports `≤ ⌊log₂|F|⌋ + g` bits (statistical + PoW). |
