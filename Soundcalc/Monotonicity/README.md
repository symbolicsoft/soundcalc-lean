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
| FRI query | `queryErr_antitone_numQueries` (q), `queryErr_antitone_grindQuery` (grind), `queryErr_mono_rho` (ρ — `((1+ρ)/2)^q/2^g` is monotone in ρ) |
| FRI commit / batching | `batchingErr_antitone_grindBatch` (grind), `UDR_errPowers_antitone_rho` (ρ), `UDR_errPowers_mono_dim` (H), `batchingErr_mono_batchSize` (batch), `UDR_errPowers_antitone_card` (`\|F\|`) |
| ALI | `\|F\|`: `aliErr_antitone_card`; `L`: `aliErr_mono_listSize`; also `aliErr_mono_numConstraints` (`C`, not a table column) |
| DEEP | grind: `deepErr_antitone_grindDeep`; ρ: `deepErr_antitone_rho`; H: `deepErr_mono_traceLen`; `\|F\|`: `deepErr_antitone_card`; `L`: `deepErr_mono_listSize`; also `deepErr_mono_airMaxDegree`, `deepErr_mono_maxCombo` (`deg`/`m_max`) |
| LogUp / GKR | grind: `errUB_antitone_grindBitsLookup`; H: `errUB_mono_rowsL`/`errUB_mono_rowsT`; batch: `errUB_mono_numLookupsM`, `errUB_mono_numColumnsS`; `\|F\|`: `errUB_antitone_card` |
| JBR `m` = ∗ | `whir_multiplicity_interior_optimum` (**proves** the reported security is non-monotone in `m` — strict interior maximum), built from `whir_agreement_antitone_m` (query security rises) **vs** `whir_listSize_mono_m` (algebraic security falls) via `min_rise_fall_interior_max` |
| FRI proof size (size, not error) | `proofSizeWorst_mono_numQueries` (q ↑), `proofSizeWorst_mono_batchSize` / `proofSizeExp_mono_batchSize` (batch ↑, worst **and** expected) |

Notes.
`†` — the list size multiplies the lookup error only in the SWIRL analysis; the FRI-based zkVMs'
`LookupCfg.errUB` is regime-independent, so its formalized `L` column is actually `—` (the `↑` is the
SWIRL behavior).
"pinned" — the cell cannot be moved by a **single-field record update** (FRI's `h_earlyStop`
couples `ρ`/`H`; DeepAli's field-coherence invariants couple `|F|`; `ρ`/`H` sit behind the `PCS`
inductive and its `FRIConfig.h_earlyStop`). These cells are still lemma-backed, in one of two ways:
 - FRI commit/batching `ρ`/`H`/`|F|` — by the regime-level `errPowers` lemmas
   (`UDR_errPowers_antitone_rho` / `_mono_dim` / `_antitone_card`), since those cells *are*
   `errPowers`-shaped.
 - ALI `|F|` and DEEP `ρ`/`H`/`|F|` — by **two-config** lemmas (`aliErr_antitone_card`,
   `deepErr_antitone_card` / `_antitone_rho` / `_mono_traceLen`) that compare two configs agreeing on
   the other projections (the "same circuit, bigger field / slower rate / longer trace" comparison).
`∗` — provably non-monotone: `whir_multiplicity_interior_optimum` proves the reported security
(`min` over cells) has a *strict interior maximum* in `m`, since query security rises while algebraic
security falls; so `m` has no monotone direction.
JBR row — its knobs are the gap `η` and multiplicity `m`, which are not among the columns: the error
is `↓` in `η` (larger gap ⇒ smaller error) and `∗` in `m` (interior optimum). `η` is derived from
`(F, ρ, g)` in our model (`etaLB`/`etaUB`), so it is not a free record-update knob.

---

## `FRI.lean`

Query cell `queryErr R = (1 − θLB)^numQueries / 2^grindQuery`; proof-size accumulator
`getFRIProofSizeBits`. The record-update knobs are `numQueries` and `batchSize` (the others —
`denseLen`, `ρ`, `foldingFactors` — are pinned together by the config's `h_earlyStop` invariant).

### Sensitivity (`q` = numQueries, `gQ`/`gB` = grind query/batch, `H` = denseLen)

| cell | `q` | `gQ` | `gB` | `ρ` | `H` | batch | `\|F\|` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `queryErr` | ↓ | ↓ | — | ↑ | — | — | — |
| `batchingErr` | — | — | ↓ | ↓ | ↑ | ↑ | ↓ |

`ρ`/`H`/`\|F\|` on `batchingErr` are proved at the regime level (`UDR_errPowers_*`).
**Proof size** (a size, not an error): proven monotone in `q` and `batch` (`batch` worst **and**
expected). It also grows with the domain (`H`, `ρ`) and field width (`\|F\|`), which are pinned by
`h_earlyStop`, so those aren't `—` — just not turned into theorems.
**Per round** (structural, not a knob): the folded dimension shrinks each round
(`friDimension_antitone`, the FRI analog of WHIR's `logDegree_anti`).

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
| `FRIConfig.proofSizeExp_mono_batchSize` | `batchSize` | Same, for the **expected** (amortized, `expected = true`) proof size — `batchSize` scales only the initial leaves. |
| `FRIConfig.queryErr_antitone_grindQuery` | `grindQuery` | More query-phase PoW bits ⇒ smaller query error. |
| `FRIConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error. |
| `FRIConfig.queryErr_mono_rho` | `ρ` (pinned) | Higher rate ⇒ larger query error (`((1+ρ)/2)^q/2^g`); two configs agreeing on the other query inputs, at UDR. |

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
`μᵢ₊₁ = μᵢ + (kᵢ − 1)`. The query counts `tᵢ` are a list (query-count sensitivity is the shared shape
lemma in `Basic.lean`), but `batchSize` **is** a record-update knob — a *semi-pinned* one, since
`h_batchSize : 1 ≤ batchSize` must be re-supplied. Its batching-error and proof-size monotonicities
mirror FRI exactly, closing the FRI↔WHIR asymmetry on the batch knob.

### Sensitivity (`batch` = batchSize, `gB` = grindBatch; plus regime radius `δ`, round index `i`)

WHIR's knobs are a mix: config fields (`batch`, `gB`), the decoding radius `δ` (regime), and the
round index `i` (structural — the fixed-domain-shift recurrences, no FRI analog).

| cell / quantity | batch | `gB` | radius `δ` | round `i` |
|---|:---:|:---:|:---:|:---:|
| `epsilonQuery` (query error) | — | — | ↓ | — |
| `batchingErr` | ↑ | ↓ | — | — |
| proof size | ↑ | — | — | — |
| `logInvRate μᵢ` (rate `= 2^−μ` falls) | — | — | — | ↑ |
| `logDegree mᵢ` (degree) | — | — | — | ↓ |

`batch`/`gB` are the config knobs (`batch` semi-pinned); `δ` is cross-regime (`epsilonQuery` antitone
in the radius); the round-`i` rows are WHIR's rate-falls / degree-shrinks signature. The JBR
multiplicity `m` (a regime quantity, not a config field) is the catalog's one `∗` cell —
`whir_multiplicity_interior_optimum` (see the top-level table / foundations below).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `WHIRConfig.epsilonQuery_antitone_radius` | regime | `epsilonQuery` is antitone in the decoding radius `δᵢ` (FRI analog). |
| `WHIRConfig.epsilonQuery_bits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (FRI analog). |
| `WHIRConfig.batchingErr_mono_batchSize` | `batchSize` | More batched polys ⇒ larger batching error (FRI analog of `batchingErr_mono_batchSize`). |
| `WHIRConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error (FRI analog). |
| `WHIRConfig.proofSizeWorst_mono_batchSize` | `batchSize` | More batched polys ⇒ bigger proof — worst case (FRI analog). |
| `WHIRConfig.proofSizeExp_mono_batchSize` | `batchSize` | Same, expected/amortized proof size (FRI analog). |
| `WHIRConfig.logInvRate_mono` | round `i` | The rate falls every iteration (`μᵢ ≤ μᵢ₊₁`) — WHIR's fixed-domain-shift signature (no FRI analog). |
| `WHIRConfig.logDegree_anti` | round `i` | The degree shrinks every iteration (`mᵢ₊₁ ≤ mᵢ`). |

### Foundations

| theorem | description |
|---|---|
| `whir_agreement_list_le_unique` | List-regime agreement `√ρ·(1 + 1/2m)` ≤ unique `(1+ρ)/2` — exactly when `√ρ ≤ m·(1−√ρ)²`. |
| `whir_listSize_ge_one` | List-regime list size `(m+½)/√ρ ≥ 1` — the cost that offsets the query-cell win. |
| `whir_agreement_antitone_m` | Interior optimum (`∗`), force 1: the agreement `√ρ·(1+1/2m)` *improves* (antitone) as `m` grows — query security rises. |
| `whir_listSize_mono_m` | Interior optimum (`∗`), force 2: the list size `(m+½)/√ρ` *grows* (monotone) with `m` — algebraic security falls. |
| `min_rise_fall_interior_max` | The `min` of a rising and a falling function has a strict interior maximum (the reported-security mechanism). |
| `whir_multiplicity_interior_optimum` | **Proves `∗`:** the reported security `min(rise, fall)` is non-monotone in `m` — a strict interior maximum (`2 < 4 > 2` at `m = 2,4,6`). |

## `Lookup.lean`

`errUB = (baseError + gkrError) / 2^grindBitsLookup` with `baseError = numLookupsM·H·R / |F|`
(`H = rowsL + rowsT`, `R = columnAggregFactor`). `LookupCfg` has no coherence invariant, so every
field is a record-update knob.

### Sensitivity (one cell, `errUB`)

| knob | `grindBitsLookup` | `rowsL`/`rowsT` (`H`) | `numLookupsM` | `numColumnsS` | `\|F\|` |
|---|:---:|:---:|:---:|:---:|:---:|
| `errUB` | ↓ | ↑ | ↑ | ↑ | ↓ |

(`H = rowsL + rowsT` — both halves are proven; `numLookupsM`/`numColumnsS` are the two batch knobs.)

### Catalogue

| theorem | knob | description |
|---|---|---|
| `LookupCfg.errUB_antitone_grindBitsLookup` | `grindBitsLookup` | More PoW bits ⇒ smaller lookup error (needs `reductionErr ≥ 0`). |
| `LookupCfg.errUB_antitone_card` | `field` | Larger field ⇒ smaller lookup error (`|F|` column). |
| `LookupCfg.errUB_mono_rowsT` | `rowsT` | More table rows ⇒ larger lookup error (`H` column). |
| `LookupCfg.errUB_mono_rowsL` | `rowsL` | The other `H` half — more `rowsL` rows ⇒ larger lookup error. |
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

### Sensitivity (`C` = numConstraints, `deg` = airMaxDegree, `mₓ` = maxCombo, `gD` = grindDeep)

| cell | `C` | `deg` | `mₓ` | `gD` | `ρ` | `H` | `\|F\|` | `L` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `aliErr` | ↑ | — | — | — | — | — | ↓ | ↑ |
| `deepErr` | — | ↑ | ↑ | ↓ | ↓ | ↑ | ↓ | ↑ |

`ρ`/`H`/`\|F\|` are two-config lemmas (those fields are pinned); `L` is cross-regime (`listSize`).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `DeepAliCfg.aliErr_mono_numConstraints` | `numConstraints` | More constraints ⇒ larger ALI error (`C`). |
| `DeepAliCfg.aliErr_mono_listSize` | regime | Larger list size ⇒ larger ALI error (`L` column). |
| `DeepAliCfg.deepErr_antitone_grindDeep` | `grindDeep` | More PoW bits ⇒ smaller DEEP error. |
| `DeepAliCfg.deepErr_mono_airMaxDegree` | `airMaxDegree` | Higher AIR degree ⇒ larger DEEP error. |
| `DeepAliCfg.deepErr_mono_maxCombo` | `maxCombo` | Larger max-combo ⇒ larger DEEP error. |
| `DeepAliCfg.deepErr_mono_listSize` | regime | Larger list size ⇒ larger DEEP error (`L` column). |
| `DeepAliCfg.aliErr_antitone_card` | field (2-config) | Larger `\|F\|` ⇒ smaller ALI error. |
| `DeepAliCfg.deepErr_antitone_card` | field (2-config) | Larger `\|F\|` ⇒ smaller DEEP error. |
| `DeepAliCfg.deepErr_antitone_rho` | rate (2-config) | Higher `ρ` ⇒ smaller DEEP error (via `H/ρ` in the denominator). |
| `DeepAliCfg.deepErr_mono_traceLen` | trace (2-config) | Longer trace `H` ⇒ larger DEEP error. |

## `Jagged.lean`

`zerocheckErr = (C + (deg+2)·⌈log₂ H⌉)/|F|` and `reduceErr = (⌈log₂ w⌉ + …)/|F|`. `JaggedCfg` pins
`field`/`densePCS`/`lookups`; `traceLength`/`traceWidth`/`numConstraints`/`airMaxDegree` are free
knobs. Proof size is omitted — `getJaggedProofSizeBits` is private and reads only the pinned dense
PCS, so it has no Jagged-level knob and inherits the dense PCS's proof-size monotonicity.

### Sensitivity (`C` = numConstraints, `deg` = airMaxDegree, `H` = traceLength, `w` = traceWidth)

| cell | `C` | `deg` | `H` | `w` | `\|F\|` |
|---|:---:|:---:|:---:|:---:|:---:|
| `zerocheckErr` | ↑ | ↑ | ↑ | — | ↓ |
| `reduceErr` | — | — | — | ↑ | ↓ |

`reduceErr`'s `H` is the *dense-PCS* trace length (`—` here, since Jagged's own `traceLength` feeds
only `zerocheckErr`); `\|F\|` is a two-config lemma (field pinned).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `JaggedCfg.zerocheckErr_mono_numConstraints` | `numConstraints` | More constraints ⇒ larger zerocheck error. |
| `JaggedCfg.zerocheckErr_mono_airMaxDegree` | `airMaxDegree` | Higher AIR degree ⇒ larger zerocheck error. |
| `JaggedCfg.zerocheckErr_mono_traceLength` | `traceLength` | Longer trace ⇒ larger zerocheck error (via `⌈log₂ H⌉`). |
| `JaggedCfg.reduceErr_mono_traceWidth` | `traceWidth` | Wider trace ⇒ larger reduction error (via `⌈log₂ w⌉`). |
| `JaggedCfg.zerocheckErr_antitone_card` | field (2-config) | Larger `\|F\|` ⇒ smaller zerocheck error. |
| `JaggedCfg.reduceErr_antitone_card` | field (2-config) | Larger `\|F\|` ⇒ smaller reduction error. |

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
