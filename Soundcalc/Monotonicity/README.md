# Monotonicity — theorem reference

Monotonicity / optimality theorems for the PCS soundness and proof-size formulas: the "more than a
point-wise calculator" layer.

This is the **catalogue** — config-level results that say how a *cell* (soundness error, security
bits, or proof size) moves when you turn one *knob*: a configuration field (`{c with numQueries := …}`)
or the decoding regime (UDR vs JBR). The cross-cutting table comes first, then one grid per component.
(The supporting lemmas — the query-cell shape, Merkle proof-size atoms, `scanl`/`foldl` monotonicities,
`errLinear`/`errPowers` mechanisms, and real-analysis facts — live in `Basic.lean` / `Regime.lean` and
the foundations of each file; they're the proof toolkit, not catalogued here.)

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
| FRI commit / batching | `batchingErr_antitone_grindBatch` / `commitErr_antitone_grindCommit` (grind), `UDR_errPowers_antitone_rho` (ρ), `UDR_errPowers_mono_dim` (H), `batchingErr_mono_batchSize` (batch), `UDR_errPowers_antitone_card` (`\|F\|`) |
| ALI | `\|F\|`: `aliErr_antitone_card`; `L`: `aliErr_mono_listSize`; also `aliErr_mono_numConstraints` (`C`, not a table column) |
| DEEP | grind: `deepErr_antitone_grindDeep`; ρ: `deepErr_antitone_rho`; H: `deepErr_mono_traceLen`; `\|F\|`: `deepErr_antitone_card`; `L`: `deepErr_mono_listSize`; also `deepErr_mono_airMaxDegree`, `deepErr_mono_maxCombo` (`deg`/`m_max`) |
| LogUp / GKR | grind: `errUB_antitone_grindBitsLookup`; H: `errUB_mono_rowsL`/`errUB_mono_rowsT`; batch: `errUB_mono_numLookupsM`, `errUB_mono_numColumnsS`; `\|F\|`: `errUB_antitone_card` |
| JBR `m` = ∗ | `whir_multiplicity_interior_optimum` (**proves** the reported security is non-monotone in `m` — strict interior maximum), built from `whir_agreement_antitone_m` (query security rises) **vs** `whir_listSize_mono_m` (algebraic security falls) via `min_rise_fall_interior_max` |

(Proof **size** is a separate quantity — see its own section below; it is only carried for FRI/WHIR.)

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

## Proof size

Proof *size* (bits) is a separate quantity from the soundness error, and only **FRI and WHIR** carry
proof-size monotonicity theorems — the circuit/lookup cells route their proof size through the dense
PCS, so they inherit these. Both the worst-case (`proofSizeWorst`, `expected = false`) and the
amortized (`proofSizeExp`, `expected = true`) sizes are covered. `↑` = proven monotone; `open` = the
direction is expected but not yet a theorem.

We catalogue only the parameters that **trade proof size against a soundness gain** — the design
levers `numQueries` and `batchSize` (more queries/batching buys security *and* costs proof size).
Proof size also grows with other parameters (hash/field element size, domain size, folding structure,
and WHIR's `constraintDegree`/`numOodSamples`), but those don't buy soundness — and several are pinned
— so they're outside the "no free lunch" story this table is about.

### FRI proof size

| cell | `numQueries` | `batchSize` |
|---|:---:|:---:|
| `proofSizeWorst` | ↑ | ↑ |
| `proofSizeExp` | open† | ↑ |

Theorems: `FRIConfig.proofSizeWorst_mono_numQueries`, `FRIConfig.proofSizeWorst_mono_batchSize`,
`FRIConfig.proofSizeExp_mono_batchSize`.

### WHIR proof size

| cell | `batchSize` |
|---|:---:|
| `proofSizeWorst` | ↑ |
| `proofSizeExp` | ↑ |

Theorems: `WHIRConfig.proofSizeWorst_mono_batchSize`, `WHIRConfig.proofSizeExp_mono_batchSize`
(`batchSize` semi-pinned: `1 ≤ batchSize` is re-supplied on the record update).

`†` — the `expected = true` `numQueries` cell is open: it needs monotonicity of the `numHashes`
inclusion–exclusion sum in the number of openings.

---

## `FRI.lean`

Query cell `queryErr R = (1 − θLB)^numQueries / 2^grindQuery`; proof-size accumulator
`getFRIProofSizeBits`. The record-update knobs are `numQueries` and `batchSize` (the others —
`denseLen`, `ρ`, `foldingFactors` — are pinned together by the config's `h_earlyStop` invariant).

### Sensitivity (`q` = numQueries, `gQ`/`gB`/`gC` = grind query/batch/commit, `H` = denseLen)

| cell | `q` | `gQ` | `gB` | `gC` | `ρ` | `H` | batch | `\|F\|` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `queryErr` | ↓ | ↓ | — | — | ↑ | — | — | — |
| `batchingErr` | — | — | ↓ | — | ↓ | ↑ | ↑ | ↓ |
| `commitErr` | — | — | — | ↓ | ↓ | ↑ | — | ↓ |

`ρ`/`H`/`\|F\|` on `batchingErr`/`commitErr` are proved at the regime level (`UDR_errPowers_*`);
`commitErr`'s batch arg is the folding factor `kᵢ` (pinned), so the `batch` column is `—` there.
(Proof size has its own section above.)
**Per round** (structural, not a knob): the folded dimension shrinks each round
(`friDimension_antitone`, the FRI analog of WHIR's `logDegree_anti`).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `FRIConfig.queryErr_antitone_radius` | regime | `queryErr` is antitone in the decoding radius `θLB` (larger radius ⇒ smaller error). |
| `FRIConfig.queryBits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (`UDR ≤ JBR` on the query cell). |
| `FRIConfig.queryErr_antitone_numQueries` | `numQueries` | More queries never raise the query-cell error. |
| `FRIConfig.queryBits_mono_numQueries` | `numQueries` | More queries never lower the query-cell security (benefit side). |
| `FRIConfig.batchingErr_mono_batchSize` | `batchSize` | **Batching soundness cost:** more batched polys ⇒ larger batching error — **both** paths (`errPowers` and the SP1 `errMultilinear` path). |
| `FRIConfig.queryErr_antitone_grindQuery` | `grindQuery` | More query-phase PoW bits ⇒ smaller query error. |
| `FRIConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error. |
| `FRIConfig.commitErr_antitone_grindCommit` | `grindCommit` | More commit-phase PoW bits ⇒ smaller (per-round) commit error. |
| `FRIConfig.queryErr_mono_rho` | `ρ` (pinned) | Higher rate ⇒ larger query error (`((1+ρ)/2)^q/2^g`); two configs agreeing on the other query inputs, at UDR. |

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
| `logInvRate μᵢ` (rate `= 2^−μ` falls) | — | — | — | ↑ |
| `logDegree mᵢ` (degree) | — | — | — | ↓ |

(Proof size has its own section above.)

`batch`/`gB` are the config knobs (`batch` semi-pinned); `δ` is cross-regime (`epsilonQuery` antitone
in the radius); the round-`i` rows are WHIR's rate-falls / degree-shrinks signature. The JBR
multiplicity `m` (a regime quantity, not a config field) is the catalog's one `∗` cell —
`whir_multiplicity_interior_optimum` (see the top-level table).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `WHIRConfig.epsilonQuery_antitone_radius` | regime | `epsilonQuery` is antitone in the decoding radius `δᵢ` (FRI analog). |
| `WHIRConfig.epsilonQuery_bits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (FRI analog). |
| `WHIRConfig.batchingErr_mono_batchSize` | `batchSize` | More batched polys ⇒ larger batching error (FRI analog of `batchingErr_mono_batchSize`). |
| `WHIRConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error (FRI analog). |
| `WHIRConfig.logInvRate_mono` | round `i` | The rate falls every iteration (`μᵢ ≤ μᵢ₊₁`) — WHIR's fixed-domain-shift signature (no FRI analog). |
| `WHIRConfig.logDegree_anti` | round `i` | The degree shrinks every iteration (`mᵢ₊₁ ≤ mᵢ`). |

## `Lookup.lean`

`errUB = (baseError + gkrError) / 2^grindBitsLookup` with `baseError = numLookupsM·H·R / |F|`
(`H = rowsL + rowsT`, `R = columnAggregFactor`). `LookupCfg` has no coherence invariant, so every
field is a record-update knob.

### Sensitivity (one cell, `errUB`)

| knob | `grindBitsLookup` | `rowsL`/`rowsT` (`H`) | `numLookupsM` | `numColumnsS` | `reductionErr` | `\|F\|` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|
| `errUB` | ↓ | ↑ | ↑ | ↑ | ↑ | ↓ |

(`H = rowsL + rowsT` — both halves proven; `numLookupsM`/`numColumnsS` are the two batch knobs;
`reductionErr` ↑ only in the multivariate branch.)

### Catalogue

| theorem | knob | description |
|---|---|---|
| `LookupCfg.errUB_antitone_grindBitsLookup` | `grindBitsLookup` | More PoW bits ⇒ smaller lookup error (needs `reductionErr ≥ 0`). |
| `LookupCfg.errUB_antitone_card` | `field` | Larger field ⇒ smaller lookup error (`|F|` column). |
| `LookupCfg.errUB_mono_rowsT` | `rowsT` | More table rows ⇒ larger lookup error (`H` column). |
| `LookupCfg.errUB_mono_rowsL` | `rowsL` | The other `H` half — more `rowsL` rows ⇒ larger lookup error. |
| `LookupCfg.errUB_mono_numLookupsM` | `numLookupsM` | More lookups ⇒ larger error (batch). |
| `LookupCfg.errUB_mono_numColumnsS` | `numColumnsS` | More columns ⇒ larger error (batch, via `R`; GKR is `S`-independent). |
| `LookupCfg.errUB_mono_reductionErr` | `reductionErr` | A larger auxiliary reduction error ⇒ larger lookup error (multivariate branch). |

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

---

The supporting lemmas (`Regime.lean` — Johnson-vs-unique, field ceiling, `errLinear`/`errPowers`
monotonicities; `Basic.lean` — query-cell shape, `scanl` steps, `secBits` grinding, division helpers)
are the proof toolkit behind the catalogue above; see the source files.
