# 📊 zkDTVM (v0.8.0)

How to read this report:
- Table rows correspond to security regimes
- Table columns correspond to proof system components
- Cells show bits of security per component
- Proof size estimates are indicative (1 KiB = 1024 bytes)

## zkVM Overview

| Metric | Value | Relevant circuit | Notes |
| --- | --- | --- | --- |
| Final bits of security | **128 bits** | [core](#core) | Regime: mixed |
| Final proof size (worst case) | **200 KiB** | [root_shrink](#root_shrink) | |

## Circuits

- [core](#core)
- [compress](#compress)
- [shrink](#shrink)
- [root_shrink](#root_shrink)

## core

**Parameters:**
- Proof system: Jagged
- PCS: FRI
- Hash size (bits): 248
- Number of queries: 261
- Grinding query phase (bits): 20
- Field: KoalaBear⁵
- Rate (ρ): 0.5
- Dense trace length: $2^{21}$
- Trace length: 4194304
- Trace width: 31209
- FRI rounds: 21
- FRI folding factors: [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
- FRI early stop degree: 2
- Dense batch size: 62928
- Batching: Powers
- Lookup (logup): lookup

**Proof Size:** 311725 KiB (expected) / 312976 KiB (worst case)

| regime | total | lookup | batching | commit round 1 | commit round 10 | commit round 11 | commit round 12 | commit round 13 | commit round 14 | commit round 15 | commit round 16 | commit round 17 | commit round 18 | commit round 19 | commit round 2 | commit round 20 | commit round 21 | commit round 3 | commit round 4 | commit round 5 | commit round 6 | commit round 7 | commit round 8 | commit round 9 | query phase | reduce to dense PCS | zerocheck |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| UDR | 128 | 136 | 129 | 135 | 144 | 145 | 146 | 147 | 148 | 149 | 150 | 151 | 152 | 153 | 136 | 153 | 154 | 137 | 138 | 139 | 140 | 141 | 142 | 143 | 128 | 147 | 140 |


## compress

**Parameters:**
- Proof system: Jagged
- PCS: FRI
- Hash size (bits): 248
- Number of queries: 160
- Grinding query phase (bits): 20
- Field: KoalaBear⁵
- Rate (ρ): 0.25
- Dense trace length: $2^{20}$
- Trace length: 2097152
- Trace width: 326
- FRI rounds: 20
- FRI folding factors: [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
- FRI early stop degree: 4
- Dense batch size: 128
- Batching: Powers
- Lookup (logup): lookup

**Proof Size:** 1022 KiB (expected) / 1736 KiB (worst case)

| regime | total | lookup | batching | commit round 1 | commit round 10 | commit round 11 | commit round 12 | commit round 13 | commit round 14 | commit round 15 | commit round 16 | commit round 17 | commit round 18 | commit round 19 | commit round 2 | commit round 20 | commit round 3 | commit round 4 | commit round 5 | commit round 6 | commit round 7 | commit round 8 | commit round 9 | query phase | reduce to dense PCS | zerocheck |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| UDR | 128 | 136 | 137 | 135 | 144 | 145 | 146 | 147 | 148 | 149 | 150 | 151 | 152 | 152 | 136 | 153 | 137 | 138 | 139 | 140 | 141 | 142 | 143 | 128 | 147 | 146 |


## shrink

**Parameters:**
- Proof system: Jagged
- PCS: FRI
- Hash size (bits): 248
- Number of queries: 131
- Grinding query phase (bits): 20
- Field: KoalaBear⁵
- Rate (ρ): 0.125
- Dense trace length: $2^{19}$
- Trace length: 1048576
- Trace width: 326
- FRI rounds: 20
- FRI folding factors: [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
- FRI early stop degree: 4
- Dense batch size: 128
- Batching: Powers
- Lookup (logup): lookup

**Proof Size:** 856 KiB (expected) / 1422 KiB (worst case)

| regime | total | lookup | batching | commit round 1 | commit round 10 | commit round 11 | commit round 12 | commit round 13 | commit round 14 | commit round 15 | commit round 16 | commit round 17 | commit round 18 | commit round 19 | commit round 2 | commit round 20 | commit round 3 | commit round 4 | commit round 5 | commit round 6 | commit round 7 | commit round 8 | commit round 9 | query phase | reduce to dense PCS | zerocheck |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| UDR | 128 | 137 | 137 | 135 | 144 | 145 | 146 | 147 | 148 | 149 | 150 | 151 | 151 | 152 | 136 | 153 | 137 | 138 | 139 | 140 | 141 | 142 | 143 | 128 | 147 | 146 |


## root_shrink

**Parameters:**
- Proof system: SWIRL
- PCS: WHIR
- Field: KoalaBear⁵
- Regime: JBR
- `m`: 2
- `l_skip`: 6
- `n_stack`: 12
- `w_stack`: 1
- Log blowup: 4
- WHIR queries per round: [77, 38, 26]
- WHIR folding PoW (bits): 20
- WHIR query-phase PoW (bits): 20
- WHIR μ PoW (bits): 20
- Max constraints per AIR: 204
- Number of AIRs: 50
- Max log trace height: 18
- Number of trace columns: 326
- Max interactions per AIR: 100
- Proof-size public values bound: 0

**Proof Size:** 200 KiB (expected) / 200 KiB (worst case)

| regime | total | constraint_batching | gkr_batching | gkr_sumcheck | logup | stacked_reduction | whir | whir_fold_rbr | whir_gamma_batching | whir_ood_rbr | whir_proximity_gaps | whir_query | whir_shift_rbr | whir_sumcheck | zerocheck_sumcheck |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| JBR | 128 | 143 | 154 | 153 | 128 | 142 | 132 | 134 | 142 | 132 | 134 | 140 | 140 | 167 | 143 |

