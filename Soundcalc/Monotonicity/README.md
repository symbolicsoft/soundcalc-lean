# Monotonicity — theorem reference

Monotonicity / optimality theorems for the PCS soundness and proof-size formulas: the "more than a
point-wise calculator" layer.

This is the **catalogue** — config-level results that say how a *cell* (soundness error, security
bits, or proof size) moves when you turn one *knob*: a configuration field (`{c with numQueries := …}`)
or the decoding regime (UDR vs JBR).

## Shared quantities (referenced by several theorems)

- **Query cell** — FRI's `queryErr` and WHIR's `epsilonQuery` share the shape
  `ε = (1 − θ)ᵗ / 2ᵍ`, for a decoding radius `θ`, query count `t`, and query-phase grinding `g`.
- **FRI decoding radius** — UDR: `θ = (1 − ρ)/2`; JBR (Johnson): `θ ≈ (1 − η) − √ρ`.
- **WHIR per-iteration recurrence** — `mᵢ₊₁ = mᵢ − kᵢ` (log-degree) and `μᵢ₊₁ = μᵢ + (kᵢ − 1)`
  (log-inverse-rate), so the rate `ρᵢ = 2^(−μᵢ)` falls every iteration while the degree shrinks.
- **Linear (Schwartz–Zippel) error** — `errLinear = ((1−ρ)/2·(d/ρ) + 1) / |F|`; the powers-batching
  error is `errPowers = errLinear·(batch − 1)`.
- **Field ceiling** — `secBits(1/|F|) = ⌊log₂ |F|⌋`, the most bits an algebraic cell can report.
- **`Regime.Standard`** — the bundle that makes the catalogue regime-independent (see below): a
  regime `R` over field `F` at rate `ρ` is *standard* when `errPowers = errLinear·(b−1)`,
  `errMultilinear = errLinear·⌈log₂ b⌉`, `1/|F| ≤ errLinear`, and `errLinear` is monotone in the
  dimension. `UDR_standard` / `JBR_standard` are the **only** regime-specific proofs in the module.

---

## Sensitivity catalog

How each error term moves as a knob **grows** — `↓` error falls (security rises), `↑` error rises,
`—` the knob does not occur. **Every bound in this catalogue is backed at both decoding regimes.**
That is the entry criterion: a direction that holds only at UDR, or only at JBR, is not listed here
at all. `H` is the trace/dense length, `L` the decoder list size.

| Error term | `q` | grind | `ρ` | `H` | batch | `\|F\|` | `L` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| FRI query `(1−θ)^q·2^{−g}` | ↓ | ↓ | — | — | — | — | — |
| FRI commit / batching | — | ↓ | — | ↑ | ↑ | ↓ | — |
| ALI `L⁺·C/\|F\|` | — | — | — | — | — | ↓ | ↑ |
| DEEP | — | ↓ | ↓ | ↑ | — | ↓ | ↑ |
| LogUp / GKR | — | ↓ | — | ↑ | ↑ | ↓ | — |

Backing lemma per cell (`—` cells omitted):

| Error term | backing lemmas |
|---|---|
| FRI query | `queryErr_antitone_numQueries` (q), `queryErr_antitone_grindQuery` (grind) |
| FRI commit / batching | `batchingErr_antitone_grindBatch` / `commitErr_antitone_grindCommit` (grind), `errPowers_mono_dim` / `errMultilinear_mono_dim` (H), `batchingErr_mono_batchSize` (batch), `UDR_`/`JBR_err{Powers,Multilinear}_antitone_card` (`\|F\|`) |
| ALI | `\|F\|`: `aliErr_antitone_card`; `L`: `aliErr_mono_listSize`; also `aliErr_mono_numConstraints` (`C`, not a table column) |
| DEEP | grind: `deepErr_antitone_grindDeep`; ρ: `deepErr_antitone_rho`; H: `deepErr_mono_traceLen`; `\|F\|`: `deepErr_antitone_card`; `L`: `deepErr_mono_listSize`; also `deepErr_mono_airMaxDegree`, `deepErr_mono_maxCombo` (`deg`/`m_max`) |
| LogUp / GKR | grind: `errUB_antitone_grindBitsLookup`; H: `errUB_mono_rowsL`/`errUB_mono_rowsT`; batch: `errUB_mono_numLookupsM`, `errUB_mono_numColumnsS`; `\|F\|`: `errUB_antitone_card` |

(Proof **size** is a separate quantity — see its own section below; it is only carried for FRI/WHIR.)

Notes.
"pinned" — the cell cannot be moved by a **single-field record update** (FRI's `h_earlyStop`
couples `ρ`/`H`; DeepAli's field-coherence invariants couple `|F|`; `ρ`/`H` sit behind the `PCS`
inductive and its `FRIConfig.h_earlyStop`). These cells are still lemma-backed, in one of two ways:
 - FRI commit/batching `H`/`|F|` — by the regime-level batching lemmas (`errPowers_mono_dim` /
   `errMultilinear_mono_dim`, and `UDR_`/`JBR_err{Powers,Multilinear}_antitone_card`), since those
   cells *are* `errPowers`/`errMultilinear`-shaped. Both batching paths are covered, not just
   `powerBatch`.
 - ALI `|F|` and DEEP `ρ`/`H`/`|F|` — by **two-config** lemmas (`aliErr_antitone_card`,
   `deepErr_antitone_card` / `_antitone_rho` / `_mono_traceLen`) that compare two configs agreeing on
   the other projections (the "same circuit, bigger field / slower rate / longer trace" comparison).

**Regime independence.** Every cell in the catalogue is stated for an **arbitrary** regime — there
are no UDR-only or JBR-only cells, and no `_udr`/`_jbr` theorem pairs to keep in sync. Two mechanisms
achieve this:

 - *Query cells* (`queryErr`, `epsilonQuery`) take a bare `R : Regime`. Their shape `(1−θ)^t/2^g`
   mentions no regime formula except the radius `θLB`, so one theorem covers all regimes.
 - *Algebraic cells* (`batchingErr`, `commitErr`) take an `R` together with
   `hR : R.Standard c.field c.ρ`. Every step of their proofs goes through `Regime.Standard`, never
   through a `UDR`/`JBR` formula. Callers discharge `hR` with `UDR_standard` (no side conditions) or
   `JBR_standard` (the config's `sqrtLB`/`etaLB` conditions, met by every real config).

This matters because several FRI-based zkVMs (Airbender/OpenVM/Pico/ZisK) report at JBR while others
report at UDR: they read the *same* theorems. The circuit/lookup cells are regime-independent for a
different reason — `DeepAliCfg`'s cells are already quantified over `R` (the regime enters only
through `listSize`, which the lemmas take as a parameter), and `LookupCfg`/`JaggedCfg`'s cells
contain no regime quantity at all.

The one unavoidable exception is the **`|F|` knob**: changing the field turns `UDR F` into `UDR F'`,
so it *is* a change of regime and cannot be stated over a single `R`. It is given per regime family
(`UDR_`/`JBR_err{Powers,Multilinear}_antitone_card`), both of them thin corollaries of the one
regime-generic lemma `errPowers_le_of_errLinear_le` / `errMultilinear_le_of_errLinear_le`. The JBR
form carries a gap-agreement hypothesis (`etaLB` depends on `card` only through the `card > 2^150`
threshold, so two fields on the same side of it give the same `η`).

The rate `ρ` is deliberately **not** a catalogued FRI knob: it is pinned by `h_earlyStop`, and its
direction is genuinely regime-dependent (confounded at JBR through `√ρ`, `d/ρ`, and `η = etaLB(ρ)`),
so tracking it would break exactly the regime-independence above.

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

| cell | `q` | `gQ` | `gB` | `gC` | `H` | batch | `\|F\|` |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `queryErr` | ↓ | ↓ | — | — | — | — | — |
| `batchingErr` | — | — | ↓ | — | ↑ | ↑ | ↓ |
| `commitErr` | — | — | — | ↓ | ↑ | — | ↓ |

`H`/`\|F\|` on `batchingErr`/`commitErr` are proved at the regime level (`errPowers_mono_dim` /
`errMultilinear_mono_dim`, and the `_antitone_card` pair); `commitErr`'s batch arg is the folding
factor `kᵢ` (pinned), so the `batch` column is `—` there. (Proof size has its own section above.)
**Per round** (structural, not a knob): the folded dimension shrinks each round
(`friDimension_antitone`, the FRI analog of WHIR's `logDegree_anti`), hence so does the commit-cell
error at that dimension (`commitDimErr_antitone_round`).

### Catalogue

| theorem | knob | description |
|---|---|---|
| `FRIConfig.queryErr_antitone_radius` | regime | `queryErr` is antitone in the decoding radius `θLB` (larger radius ⇒ smaller error). |
| `FRIConfig.queryBits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (`UDR ≤ JBR` on the query cell). |
| `FRIConfig.queryErr_antitone_numQueries` | `numQueries` | More queries never raise the query-cell error. |
| `FRIConfig.queryBits_mono_numQueries` | `numQueries` | More queries never lower the query-cell security (benefit side). |
| `FRIConfig.batchingErr_mono_batchSize` | `batchSize` | **Batching soundness cost:** more batched polys ⇒ larger batching error — any regime, **both** paths (the `powerBatch` `errPowers` path and the multilinear `errMultilinear` path). |
| `FRIConfig.queryErr_antitone_grindQuery` | `grindQuery` | More query-phase PoW bits ⇒ smaller query error. |
| `FRIConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error (any regime, both paths). |
| `FRIConfig.commitErr_antitone_grindCommit` | `grindCommit` | More commit-phase PoW bits ⇒ smaller (per-round) commit error (any regime). |
| `FRIConfig.commitDimErr_antitone_round` | round `i` | The commit cell falls round over round: `friDimension_antitone` composed with `errPowers_mono_dim` (any regime). |

The three algebraic rows take `hR : R.Standard c.field c.ρ`; instantiate with `UDR_standard` or
`JBR_standard`. There are no separate `_jbr` theorems — the JBR regime *is* one of the `R`s these
cover.

## `WHIR.lean`

Query cell `epsilonQuery R i = (1 − δᵢ)^tᵢ / 2^gᵢ`; per-iteration recurrence `mᵢ₊₁ = mᵢ − kᵢ`,
`μᵢ₊₁ = μᵢ + (kᵢ − 1)`. The query counts `tᵢ` are a list (query-count sensitivity is the shared shape
lemma in `Basic.lean`), but `batchSize` **is** a record-update knob — a *semi-pinned* one, since
`h_batchSize : 1 ≤ batchSize` must be re-supplied. Its batching-error and proof-size monotonicities
mirror FRI exactly.

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
in the radius); the round-`i` rows are WHIR's rate-falls / degree-shrinks signature.

### Catalogue

| theorem | knob | description |
|---|---|---|
| `WHIRConfig.epsilonQuery_antitone_radius` | regime | `epsilonQuery` is antitone in the decoding radius `δᵢ` (FRI analog). |
| `WHIRConfig.epsilonQuery_bits_mono` | regime | Larger radius ⇒ at least as many query-cell bits (FRI analog). |
| `WHIRConfig.batchingErr_mono_batchSize` | `batchSize` | More batched polys ⇒ larger batching error (FRI analog of `batchingErr_mono_batchSize`) — any regime, both modes (the `errLinear` else-branch is batch-independent, so it holds with equality there). |
| `WHIRConfig.batchingErr_antitone_grindBatch` | `grindBatch` | More batch-phase PoW bits ⇒ smaller batching error (FRI analog) — any regime, both modes. |
| `WHIRConfig.logInvRate_mono` | round `i` | The rate falls every iteration (`μᵢ ≤ μᵢ₊₁`) — WHIR's fixed-domain-shift signature (no FRI analog). |
| `WHIRConfig.logDegree_anti` | round `i` | The degree shrinks every iteration (`mᵢ₊₁ ≤ mᵢ`). |

WHIR's remaining per-round cells — `epsilonFold`, `epsilonOut`, `epsilonShift` — are not individually
catalogued. `epsilonFinal = epsilonQuery` is covered by the query rows above; the other three have
list-valued per-round grinds (not scalar config knobs) and regime-confounded terms, so their moving
parts are covered only at the mechanism level (the shared `div_pow_two_antitone` grind lever and the
`errPowers`/query-shape lemmas), not as cell-level catalogue rows.

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
knobs. 

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

The supporting lemmas (`Regime.lean` — Johnson-vs-unique, the `Regime.Standard` bundle and its
`UDR`/`JBR` instances, the field ceiling, and the regime-generic `errPowers`/`errMultilinear`
monotonicities; `Basic.lean` — query-cell shape, `scanl` steps, `secBits` grinding, division helpers)
are the proof toolkit behind the catalogue above; see the source files.

Adding a regime later costs one theorem: prove `R.Standard F ρ` for it, and every algebraic cell in
this catalogue applies unchanged (plus one `errLinear`-antitone-in-`|F|` lemma if that regime's `|F|`
column is wanted).
