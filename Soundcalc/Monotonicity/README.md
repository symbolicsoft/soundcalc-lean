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
against the UDR formulas; each is backed by a named lemma (below the table). `H` is the trace/dense
length, `L` the decoder list size.

| Error term | `q` | grind | `ρ` | `H` | batch | `\|F\|` | `L` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| FRI query `(1−θ)^q·2^{−g}` | ↓ | ↓ | ↑ | — | — | — | — |
| FRI commit / batching | — | ↓ | ↓ | ↑ | ↑ | ↓ | — |
| ALI `L⁺·C/\|F\|` | — | — | — | — | — | ↓ | ↑ |
| DEEP | — | ↓ | ↓ | ↑ | — | ↓ | ↑ |
| LogUp / GKR | — | ↓ | — | ↑ | ↑ | ↓ | ↑† |
| JBR terms in `η`/`m` (own knobs, not columns) | — | — | — | — | — | — | — |

Backing lemma per cell (`—` cells omitted):

| Error term | backing lemmas |
|---|---|
| FRI query | `queryErr_antitone_numQueries` (q), `queryErr_antitone_grindQuery` (grind), `queryErr_antitone_radius` (ρ enters via `θ_LB = (1−ρ)/2`, which is antitone in ρ) |
| FRI commit / batching | `batchingErr_antitone_grindBatch` (grind), `UDR_errPowers_antitone_rho` (ρ), `UDR_errPowers_mono_dim` (H), `batchingErr_mono_batchSize` (batch), `UDR_errPowers_antitone_card` (`\|F\|`) |
| ALI | `\|F\|`: pinned by config (field ceiling `secBits_errLinear_le_field`); `L`: `aliErr_mono_listSize`; also `aliErr_mono_numConstraints` (`C`, not a table column) |
| DEEP | grind: `deepErr_antitone_grindDeep`; ρ/H/`\|F\|`: pinned by config; `L`: `deepErr_mono_listSize`; also `deepErr_mono_airMaxDegree`, `deepErr_mono_maxCombo` (`deg`/`m_max`) |
| LogUp / GKR | grind: `errUB_antitone_grindBitsLookup`; H: `errUB_mono_rowsT`; batch: `errUB_mono_numLookupsM`, `errUB_mono_numColumnsS`; `\|F\|`: `errUB_antitone_card` |
| JBR `m` = ∗ | `whir_agreement_antitone_m` (helps the query cell) **vs** `whir_listSize_mono_m` (hurts the list-size cells) |
| FRI proof size (size, not error) | `proofSizeWorst_mono_numQueries` (q ↑), `proofSizeWorst_mono_batchSize` (batch ↑) |

Notes.
`†` — the list size multiplies the lookup error only in the SWIRL analysis; the FRI-based zkVMs'
`LookupCfg.errUB` is regime-independent, so its formalized `L` column is actually `—` (the `↑` is the
SWIRL behavior).
"pinned" — the cell is blocked as a **record-update knob** by a config invariant (FRI's `h_earlyStop`
pins `ρ`/`H`; DeepAli's `h_densePCS_field` pins `ρ`/`H`/`|F|`). Two sub-cases:
 - FRI commit/batching `ρ`/`H`/`|F|` **are** backed — by the regime-level `errPowers` lemmas
   (`UDR_errPowers_antitone_rho` / `_mono_dim` / `_antitone_card`), since those cells *are*
   `errPowers`-shaped.
 - ALI `|F|` and DEEP `ρ`/`H`/`|F|` are **directionally verified against the formula but not
   individually lemma-backed**: their configs pin the field and these cells are not `errPowers`-shaped
   (they carry `L⁺` and, for DEEP, the `|F|−H−D` denominator). Adding formula-level `antitone`
   lemmas for them is a small follow-up.
`∗` — provably non-monotone: `m` has no single direction, and the two opposing lemmas *are* the
interior optimum.
JBR row — its knobs are the gap `η` and multiplicity `m`, which are not among the columns: the error
is `↓` in `η` (larger gap ⇒ smaller error) and `∗` in `m` (interior optimum). `η` is derived from
`(F, ρ, g)` in our model (`etaLB`/`etaUB`), so it is not a free record-update knob.

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
| `FRIConfig.queryErr_antitone_grindQuery` | `grindQuery` | More query-phase PoW bits ⇒ smaller query error. |
| `FRIConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error. |

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
| `whir_agreement_antitone_m` | **Interior optimum (`∗`):** the agreement `√ρ·(1+1/2m)` *improves* (antitone) as the multiplicity `m` grows. |
| `whir_listSize_mono_m` | **Interior optimum (`∗`):** the list size `(m+½)/√ρ` *grows* (monotone) with `m` — the opposing force. |

## `Lookup.lean`

`errUB = (baseError + gkrError) / 2^grindBitsLookup` with `baseError = numLookupsM·H·R / |F|`
(`H = rowsL + rowsT`, `R = columnAggregFactor`). `LookupCfg` has no coherence invariant, so every
field is a record-update knob.

### Catalogue

| theorem | knob | description |
|---|---|---|
| `LookupCfg.errUB_antitone_grindBitsLookup` | `grindBitsLookup` | More PoW bits ⇒ smaller lookup error (needs `reductionErr ≥ 0`). |
| `LookupCfg.errUB_antitone_card` | `field` | Larger field ⇒ smaller lookup error (`|F|` column). |
| `LookupCfg.errUB_mono_rowsT` | `rowsT` | More table rows ⇒ larger lookup error (`H` column). |
| `LookupCfg.errUB_mono_numLookupsM` | `numLookupsM` | More lookups ⇒ larger error (batch). |
| `LookupCfg.errUB_mono_numColumnsS` | `numColumnsS` | More columns ⇒ larger error (batch, via `R`; GKR is `S`-independent). |

### Foundations

| theorem | description |
|---|---|
| `log2UB_mono` / `log2UB_nonneg` | `log2UB` is monotone and nonnegative. |
| `columnAggregFactor_mono` / `columnAggregFactor_nonneg` | The column-aggregation factor `R` is monotone in `S` and nonnegative. |
| `gkrErrorUB_mono_alphabet` / `gkrErrorUB_mono_lookups` | The GKR term grows with the alphabet size and the lookup count. |
| `gkrErrorUB_antitone_card` / `gkrErrorUB_nonneg` | The GKR term is antitone in `|F|` and nonnegative. |

## `DeepAli.lean`

`aliErr = L⁺·C / |F|` and `deepErr = L⁺·num / (|F| − H − D) / 2^grindDeep`
(`num = deg·(H + m_max − 1) + (H − 1)`, `H = traceLen`, `D = H/ρ`, `L⁺ = R.listSize`). `DeepAliCfg`
pins `field`/`densePCS`/`lookups` via its coherence invariants, so `|F|`/`ρ`/`H` are **not**
record-update knobs; the DEEP cells carry the side condition `|F| − H − D > 0`.

### Catalogue

| theorem | knob | description |
|---|---|---|
| `DeepAliCfg.aliErr_mono_numConstraints` | `numConstraints` | More constraints ⇒ larger ALI error (`C`). |
| `DeepAliCfg.aliErr_mono_listSize` | regime | Larger list size ⇒ larger ALI error (`L` column). |
| `DeepAliCfg.deepErr_antitone_grindDeep` | `grindDeep` | More PoW bits ⇒ smaller DEEP error. |
| `DeepAliCfg.deepErr_mono_airMaxDegree` | `airMaxDegree` | Higher AIR degree ⇒ larger DEEP error. |
| `DeepAliCfg.deepErr_mono_maxCombo` | `maxCombo` | Larger max-combo ⇒ larger DEEP error. |
| `DeepAliCfg.deepErr_mono_listSize` | regime | Larger list size ⇒ larger DEEP error (`L` column). |

## `Regime.lean` — foundations (Johnson vs. unique decoding, field ceiling)

| theorem | description |
|---|---|
| `johnson_beats_unique` | The Johnson radius `1 − √ρ` beats the unique-decoding radius `(1−ρ)/2` (slack `(1−√ρ)²/2`). |
| `one_div_card_le_errLinear` | The linear soundness error is `≥ 1/|F|`, so the field ceiling bites on algebraic cells. |
| `secBits_errLinear_le_field` | The linear cell can never report more bits than the field baseline `⌊log₂|F|⌋`. |
| `UDR_errLinear_mono_dim` | The linear error is monotone in the dimension `d` — smaller instance ⇒ more sound (lifted by FRI's `H` cells). |
| `UDR_errLinear_antitone_card` / `UDR_errPowers_antitone_card` | Larger field ⇒ smaller error (`|F|` column). |
| `UDR_errLinear_antitone_rho` / `UDR_errPowers_antitone_rho` | Higher rate `ρ` ⇒ smaller error (`ρ` column). |
| `UDR_errPowers_mono_dim` | Powers error monotone in the dimension (`H` column for the commit/batching cell). |
| `UDR_errPowers_nonneg` | The powers-batching error is nonnegative (`b ≥ 1`) — used by the grind knobs. |

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
