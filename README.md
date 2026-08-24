# soundcalc-lean

A Lean 4 restatement of [soundcalc](https://github.com/ethereum/soundcalc), the Ethereum Foundation's soundness calculator for hash-based zkVMs.

soundcalc takes a zkVM's parameters (field, rate, query count, grinding, circuit sizes) and instantiates published soundness bounds to produce a security level in bits, published as Markdown [reports](https://github.com/ethereum/soundcalc/tree/main/reports). It computes in Python floats, and nothing checks that the formulas it evaluates mean what the papers say. soundcalc-lean produces the same reports from a proof checker. Every number in a report is a theorem, every formula carries shape theorems (more queries help, a larger list size costs security), and the headline aggregation carries a theorem of its own. For example, the 100-bit FRI query cell of SP1 core:

```lean
example : secBits (sp1CoreFRI.queryErr (UDR koalaBear4)) = 100 := by decide +kernel
```

`secBits ε` is the largest `k` with `ε ≤ 2⁻ᵏ`. It is specified by the proved characterization `le_secBits_iff : k ≤ secBits ε ↔ ε ≤ 1 / 2 ^ k`, and "total security is the minimum over components" is the order lemma `secBits_min'`.

## What is proved

All arithmetic is exact, over `ℕ` and `ℚ`; there are no floats. Where a published bound is irrational, the calculator substitutes a rational enclosure and proves it conservative against the real-valued original: `sqrtLB`/`sqrtUB` bracket `Real.sqrt ρ` (`sqrtLB_le`, `le_sqrtUB`), `log2UB` is within `1/m` of `Real.logb 2` (`log2UB_approx_bound`), the Johnson-bound gap `η` (BCHKS25's default `max(ρ/20, √ρ/100)`) is enclosed by `etaLB`/`etaUB` and derived from the field and rate, and the rational Johnson-bound error upper-bounds the true BCHKS25 expression (`jbrErrLinear_conservative`). A reported security level is a bound on the published formula, never a rounding of it.

Invariants live in the types. `FieldParams` carries proofs of primality and exact 2-adicity; a rate is `Rate := {ρ : ℚ // 0 < ρ ∧ ρ < 1}`; a `FRIConfig` cannot be built unless its folding schedule reaches its early-stop degree (`h_earlyStop`); a circuit's commitment scheme and lookups must agree on its field (`h_densePCS_field`, `h_lookups_field`). The TOML parser decides each invariant at parse time and either threads the proof into the structure or exits.

The headline has a theorem. `ZkVM.bestSecurityAcrossCircuits` (`Soundcalc/Headline.lean`) is the number the renderer prints, computed the way soundcalc's `report_md.py` does it after the OpenVM 2.0 fix. `ZkVM.headline_le_bestSecBits` proves that on every branch of that aggregation the headline is at most each circuit's best applicable security, which is the invariant the pre-fix mixed-regime report violated (a 99-bit circuit under a 100-bit headline).

Formulas have shape theorems. `Soundcalc/Monotonicity/` is a catalogue of theorems stating how each error term moves when one parameter moves, with every other parameter held fixed: query count, grinding bits, trace length, batch size, field size, list size. The four SWIRL cells that consumed the list size in the wrong direction in soundcalc's April 2026 revision each carry a `*_mono_listSize` theorem here. `Soundcalc/Monotonicity/README.md` lists every entry with its backing lemma.

The catalogue composes with point values. `Soundcalc/Monotonicity/SP1.lean` proves that 124 is the least query count at which SP1 core's query cell reaches 100 bits (`sp1Core_queries_minimal`) and that no query count takes SP1 core's total above 100 bits (`sp1Core_total_le_100`). Both statements range over all `q : ℕ`; no number of calculator runs could establish them.

Reports are reproduced byte-for-byte. `SoundcalcIO` parses the same `.toml` files as the Python tool and re-renders its Markdown reports, including the cross-zkVM summary. CI fails unless all nine outputs are byte-identical to the references soundcalc generated.

## Verified zkVMs

Reference configurations and reports are copied unchanged from [ethereum/soundcalc](https://github.com/ethereum/soundcalc) at commit [`d9078d6`](https://github.com/ethereum/soundcalc/commit/d9078d64c9c3ae15b0931f6d249b2dc073194f15). For each zkVM, every numeric cell of the reference report (per-term security bits, totals, proof sizes) is a theorem, and the report is re-rendered byte-for-byte.

| zkVM | Version | Circuits | Proof system | Field | Regimes | Headline |
| --- | --- | --- | --- | --- | --- | --- |
| [SP1](https://github.com/succinctlabs/sp1) | 6.1.0 | core, compress, shrink | Jagged + FRI | KoalaBear⁴ | UDR | 100 |
| [Airbender](https://github.com/matter-labs/zksync-airbender) | | 1 | DEEP-ALI + FRI | Mersenne31⁴ | UDR, JBR | 67 |
| [OpenVM](https://github.com/openvm-org/openvm) | 1.5.0 | app, leaf, internal | DEEP-ALI + FRI | BabyBear⁴ | UDR, JBR | 100 |
| [Pico](https://github.com/brevis-network/pico) | | riscv, convert, combine, compress, embed | DEEP-ALI + FRI | KoalaBear⁴ | UDR, JBR | 53 |
| [ZisK](https://github.com/0xPolygonHermez/zisk) | 0.16.1 | 44 | DEEP-ALI + FRI | Goldilocks³ | UDR, JBR (pinned `gap_to_radius`) | 128 |
| [Venus](https://github.com/ethereum/soundcalc/blob/main/reports/venus.md) | 0.1.6 | 44 (same cells as ZisK) | DEEP-ALI + FRI | Goldilocks³ | UDR, JBR | 128 |
| [OpenVM 2.0](https://github.com/openvm-org/openvm) | 2.0.0 | app, leaf, internal ×2, hook, root | SWIRL + WHIR | BabyBear⁴ | unique and list (`m` = 1, 2), mixed per circuit | 100 |
| [zkDTVM](https://github.com/ethereum/soundcalc/blob/main/reports/zkdtvm.md) | 0.8.0 | core, compress, shrink, root_shrink | Jagged + FRI and SWIRL + WHIR | KoalaBear⁵ | mixed per circuit | 128 |

The decoding regimes are parameters of the soundness analysis, not of the prover or verifier. UDR (unique decoding) takes the radius `θ ≤ (1 − ρ)/2` and list size 1; JBR (Johnson bound) takes `θ` up to `1 − √ρ` with a list size above 1. soundcalc's [background section](https://github.com/ethereum/soundcalc#background) explains both.

## Build

```sh
lake exe cache get                       # prebuilt Mathlib oleans; run this first
LEAN_NUM_THREADS=1 lake build            # build the library and tools; this checks every theorem
lake env lean scripts/AxiomsGuard.lean   # confirm the axiom footprint (see below)
lake exe mdrenderer                      # re-render the Markdown reports into SoundcalcIO/ZkVM/Reports/
```

Pinned to Lean `v4.30.0` and Mathlib `v4.30.0`. There is no separate test suite: the tests are the theorems, and `lake build` checks all of them. CI additionally fails on any `sorry` and on any byte of difference between a re-rendered report and its reference.

## How a report becomes a theorem

1. Configs (`SoundcalcIO/ZkVM/Ref/`): each zkVM's `.toml` file and reference `.md` report are taken unchanged from soundcalc.
2. Parse (`SoundcalcIO/TomlParser/`): floats that denote rates are accepted only if they equal one of `2⁻¹, …, 2⁻⁵`, which binary floating point represents exactly; `gap_to_radius` is accepted only if it is the float rendering of some `i/3000`. Anything else is rejected. Every structure invariant (rate range, early-stop consistency, cross-config field agreement) is decided here, and a parsed config carries its proofs.
3. Render (`SoundcalcIO/MdRenderer/`): the same structures are rendered as Markdown and compared byte-for-byte against the reference.

The hand-written instances in `Soundcalc/ZkVM/*.lean` bundle each circuit's cells into one `ExitCriteria` proposition (every per-term bit count, the total, and the proof sizes) discharged by a single `decide +kernel`. A formula change that moves any cell fails the build until the bundle is revised.

## Repository layout

| Lean module | Contents | Mirrors (Python) |
| --- | --- | --- |
| `Soundcalc/SecBits.lean` | `secBits` with its characterization, antitonicity, and min/max lemmas | |
| `Soundcalc/Field/` | `FieldParams` with certified primality and 2-adicity (`Core.lean`); KoalaBear, BabyBear, Mersenne31 by `norm_num`; Goldilocks by a Pratt certificate (`Pratt.lean`, `Goldilocks.lean`) | `common/fields.py` |
| `Soundcalc/Regime.lean` | the `Regime` interface; `UDR`; `JBR` as a certified conservative envelope of BCHKS25 Theorem 4.2, with the gap `η` derived per field and rate | `proxgaps/` |
| `Soundcalc/Common/Sqrt.lean`, `Common/Log.lean` | rational `√·` and `log₂` enclosures, proved against `Real.sqrt` and `Real.logb` | floats in Python |
| `Soundcalc/Common/Utils.lean` | Merkle proof and multi-proof size accounting | `common/utils.py` |
| `Soundcalc/PCS/FRI.lean` | `FRIConfig`; batching, commit, and query errors; BCS proof sizes | `pcs/fri.py` |
| `Soundcalc/PCS/WHIR.lean` | `WHIRConfig` with shape invariants; per-iteration fold, OOD, shift, and query errors; proof sizes | `pcs/whir.py` |
| `Soundcalc/Circuit/Jagged.lean` | jagged reduction and zerocheck errors; per-circuit rows, totals, proof sizes | `circuits/jagged.py` |
| `Soundcalc/Circuit/DeepAli.lean` | ALI and DEEP errors, multi-point side condition, per-circuit rows and totals | `circuits/deep_ali.py` |
| `Soundcalc/Circuit/SWIRL/` | SWIRL circuit (LogUp-GKR, zerocheck, stacked reduction over WHIR): config, errors, proof size | `circuits/swirl/` |
| `Soundcalc/Circuit/Circuit.lean` | the heterogeneous `Circuit` type and per-regime totals | `zkvms/zkvm.py` |
| `Soundcalc/Lookup.lean` | LogUp (univariate and multivariate) and GKR error upper bounds | `lookups/` |
| `Soundcalc/ZkVM.lean`, `Soundcalc/ZkVM/*.lean` | the `ZkVM` structure; literal SP1, Airbender, OpenVM, OpenVM2, Pico, ZisK, and zkDTVM instances with their cell bundles | `zkvms/` |
| `Soundcalc/Headline.lean` | the headline aggregation and `headline_le_bestSecBits` | `report_md.py` |
| `Soundcalc/Monotonicity/` | the shape-theorem catalogue, one module per formula family, plus the SP1 corollaries | |
| `SoundcalcIO/` | TOML parser, Markdown renderer | `report_md.py` |
| `SoundcalcIO/ZkVM/` | reference TOML configs and reports (`Ref/`), re-rendered reports (`Reports/`) | `zkvms/`, `reports/` |
| `scripts/AxiomsGuard.lean` | pins the axiom footprint of representative theorems of each kind | |

## Trusted computing base

Every theorem in the development rests on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry` and no `native_decide`.

- Structural theory (the `secBits` characterization, the enclosures, JBR conservativity, the monotonicity catalogue, the headline theorem): ordinary proofs against Mathlib.
- Field primality: `norm_num` for the 31-bit primes; a kernel-checked `lucas_primality` Pratt certificate for Goldilocks' 64-bit prime. No compiled evaluation anywhere on this path.
- Numeric cells and bundles: `decide +kernel`. The kernel evaluates the decision procedure itself, using its built-in arbitrary-precision natural-number arithmetic; this covers the JBR cells with `2⁴⁰`-granularity enclosures and the SWIRL cells over `|F| ≈ 2¹²⁴`.
- `scripts/AxiomsGuard.lean` pins representative theorems of each kind with `#guard_msgs`, so a regression to `native_decide` or a `sorry` fails CI.

What stays trusted: the published bounds as formulas (if a theorem in BCHKS25 is wrong, the cells are wrong with it), the vendor parameter files, and the finite set of rationals the parser accepts for float-valued fields. Fiat–Shamir analyses and the provers and verifiers themselves are out of scope.

## References

The bounds formalized here come from:

- [BCIKS20](https://eprint.iacr.org/2020/654): proximity gaps for Reed–Solomon codes
- [Ha22](https://eprint.iacr.org/2022/1216): DEEP-ALI soundness (the ALI and DEEP error terms)
- [BCHKS25](https://eprint.iacr.org/2025/2055): improved unique-decoding and Johnson-bound mutual correlated agreement bounds
- [Jagged PCS](https://eprint.iacr.org/2025/917): SP1's polynomial commitment scheme
- [LogUp](https://eprint.iacr.org/2022/1530) and [LogUp-GKR](https://eprint.iacr.org/2023/1284): lookup arguments
- [Expected Merkle multi-proof sizes](https://xn--2-umb.com/25/merkle-multi-proof/)

See the [soundcalc README](https://github.com/ethereum/soundcalc#readme) for the broader literature and for background on regimes, round-by-round soundness, and proof-size estimates.
