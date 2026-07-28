import Soundcalc.Field
import Soundcalc.Regime
import Soundcalc.SecBits
import Soundcalc.Common.Utils  -- getSizeOfMerkleMultiProofBits, KIB

/-!
# WHIR PCS — soundness error formulas

Port of `soundcalc/pcs/whir.py` (WHIR paper, Construction 5.1 / Theorem 5.2). WHIR is a
multi-round polynomial-commitment scheme: `M` iterations, each folding the multilinear by
`2^{k_i}` via a `k_i`-round sumcheck plus out-of-domain (OOD) sampling and a shift/query
step. Unlike FRI, **the rate decreases every iteration** (the degree shrinks by `2^{k_i}`
while the domain only halves).

Per-iteration state (fixed-domain-shift recurrence, `whir.py __init__`):
* `m_{i+1}   = m_i - k_i`         (log-degree; folding by `2^{k_i}`)
* `μ_{i+1}   = μ_i + (k_i - 1)`   (log-inverse-rate; domain halves, degree drops by `2^{k_i}`)

All error components call the shared `Regime` API (`listSize`, `errPowers`, `errLinear`,
`θLB`) — the same proximity-gaps machinery FRI uses — and grinding divides the error by
`2^bits` (`apply_grinding`). Errors are conservative upper bounds: `listSize`/`errPowers`
are the regime's largest values and `δ` uses `θLB` (a lower bound, so `(1-δ)^t` is an upper
bound).
-/

namespace Soundcalc

/-! ## WHIR configuration (mirrors `whir.py`'s `WHIRConfig`) -/

structure WHIRConfig where
  /-- Output length in bits of the hash used for the Merkle-tree commitments. -/
  hashBits         : ℕ
  /-- The field the protocol runs over. -/
  field            : FieldParams
  /-- `μ_0 = log₂(1/ρ_0)`, the base-2 log of the inverse of the *initial* rate. For a
      Reed–Solomon code of message size `2^m` over evaluation domain `L`, `ρ = 2^m/|L|`, so
      `log_inv_rate = log₂|L| - m` (e.g. `ρ = 1/2 → 1`, `1/4 → 2`, `1/16 → 4`). NOTE: the rate
      *decreases* every iteration; this field sets only `ρ_0`. -/
  logInvRate       : ℕ
  /-- `M`, the number of WHIR iterations (Construction 5.1). One iteration reduces the
      variable count `m` by `k` via a `k`-round sumcheck, then does OOD sampling and folding. -/
  numIterations    : ℕ
  /-- `k_0 … k_{M-1}`, the per-iteration logarithmic reduction factors. At iteration `i`:
      `m_{i+1} = m_i - k_i`, the domain halves (`|L_{i+1}| = |L_i|/2`), and because the degree
      shrinks faster than the domain the rate drops, `ρ_{i+1} = 2^{1-k_i}·ρ_i`. -/
  foldingFactors   : List ℕ
  /-- `m_0`, the initial number of variables of the multilinear polynomial (Definition 4.2:
      univariate degree `d = 2^m`). Defines the witness/message size; reduced by `k_i` each
      iteration until it reaches a small constant. -/
  logDegree        : ℕ
  /-- `t`, the number of polynomials verified simultaneously (Construction 5.5): instead of
      `t` separate checks, verify one linear combination `∑ cᵢ·fᵢ`. -/
  batchSize        : ℕ
  /-- Strategy for the batching coefficients `cᵢ`: `true` = powers (`cᵢ = c^i`),
      `false` = independent random `rᵢ`. -/
  powerBatch       : Bool
  /-- Proof-of-work (grinding) bits applied to the batching step; reduces the batching error
      by `2^{-bits}`. -/
  grindBatch       : ℕ
  /-- `d` (Construction 5.1: `d = max(d*, 3)`, so `d ≥ 3`), the degree of the constraint
      polynomials. Impacts the proof size (sumcheck polynomials have degree `d`) and the
      soundness term `d·ℓ/|F|`. -/
  constraintDegree : ℕ
  /-- Grinding bits for the folding sumcheck rounds, indexed `[iteration i (0…M-1)][round s
      (1…k_i)]`; directly reduces the round-by-round error `ε^fold_{i,s}` of Theorem 5.2. -/
  grindFolding     : List (List ℕ)
  /-- `t_0 … t_{M-1}`, the number of verification queries per iteration (Construction 5.1;
      length `M`). More queries lower the error `≈(1-δ)^t` but enlarge the proof (one Merkle
      path each). -/
  numQueries       : List ℕ
  /-- Grinding bits for the query phases (length `M`); reduces the shift error `ε^shift_i` and
      the final error `ε^fin`, trading fewer queries (smaller proof) for prover work. -/
  grindQueries     : List ℕ
  /-- `w_i`, the number of out-of-domain samples per main-loop iteration (`z_{i,0}` in
      Construction 5.1; length `M-1`). The verifier samples points outside the domain to force
      consistency between `f_i` and its multilinear extension. -/
  numOodSamples    : List ℕ
  /-- Grinding bits for the OOD sampling phases (length `M-1`); reduces the error `ε^out_i`
      (the risk that distinct polynomials collide on the sampled OOD point). -/
  grindOod         : List ℕ

  -- Certified invariants — the `assert`s in `whir.py`'s `WHIRConfig.__init__`, carried as
  -- proof fields so an ill-formed config cannot be constructed. The `by decide` defaults
  -- discharge for any concrete config. Two families of Python asserts have no field here:
  --   * `len(log_degrees) == M+1` / `len(log_inv_rates) == M+1` hold *by construction*:
  --     both are `List.scanl (·) c.logDegree c.foldingFactors`, and `scanl` always returns a
  --     list of length `foldingFactors.length + 1`; with `h_foldingFactors_len` that is
  --     `numIterations + 1`, so there is nothing left to assert.
  --   * the grinding-bits `≥ 0` checks (`grindBatch`, `grindQueries`, `grindOod`,
  --     `grindFolding[i]`) are needed in Python because `int` can be negative; here those
  --     fields are `ℕ` / `List ℕ`, so non-negativity is a type-level guarantee.
  /-- `d ≥ 3` (Construction 5.1: `d = max(d*, 3)`; below 3 is degenerate). -/
  h_constraintDegree   : 3 ≤ constraintDegree := by decide
  /-- At least one batched polynomial. -/
  h_batchSize          : 1 ≤ batchSize := by decide
  /-- Initial rate `< 1`, i.e. `μ_0 > 0`. -/
  h_logInvRate         : 0 < logInvRate := by decide
  /-- At least one iteration. -/
  h_numIterations      : 1 ≤ numIterations := by decide
  /-- One folding factor per iteration. -/
  h_foldingFactors_len : foldingFactors.length = numIterations := by decide
  /-- Every folding factor reduces the degree (`k_i ≥ 1`). -/
  h_foldingFactors_pos : ∀ k ∈ foldingFactors, 1 ≤ k := by decide
  /-- The final polynomial keeps a non-negative variable count: `Σ k_i ≤ m_0`. -/
  h_sumFolding         : foldingFactors.sum ≤ logDegree := by decide
  /-- The initial interleaved-RS domain fits the field's 2-adicity (Lemma 4.4):
      `log₂|L_0| − k_0 = (m_0 + μ_0) − k_0 ≤ two_adicity`. -/
  h_twoAdicity         : logDegree + logInvRate - foldingFactors.headD 0 ≤ field.twoAdicity := by decide
  /-- OOD samples: one per main-loop iteration (`i = 1 … M-1`). -/
  h_numOodSamples_len  : numOodSamples.length = numIterations - 1 := by decide
  /-- Query counts: one per iteration. -/
  h_numQueries_len     : numQueries.length = numIterations := by decide
  h_grindOod_len       : grindOod.length = numIterations - 1 := by decide
  h_grindQueries_len   : grindQueries.length = numIterations := by decide
  h_grindFolding_len   : grindFolding.length = numIterations := by decide
  /-- Each iteration's folding-grinding array has exactly `k_i` entries (one per sumcheck round). -/
  h_grindFolding_inner : ∀ i < numIterations, (grindFolding.getD i []).length = foldingFactors.getD i 0 := by decide


/-- Per-iteration log-degrees `m_i` (length `M+1`): `m_{i+1} = m_i - k_i`. -/
def WHIRConfig.logDegrees (c : WHIRConfig) : List ℕ :=
  List.scanl (fun m k => m - k) c.logDegree c.foldingFactors

/-- Per-iteration log-inverse-rates `μ_i` (length `M+1`): `μ_{i+1} = μ_i + (k_i - 1)`. -/
def WHIRConfig.logInvRates (c : WHIRConfig) : List ℕ :=
  List.scanl (fun μ k => μ + (k - 1)) c.logInvRate c.foldingFactors

def WHIRConfig.mi  (c : WHIRConfig) (i : ℕ) : ℕ := c.logDegrees.getD i 0
def WHIRConfig.mui (c : WHIRConfig) (i : ℕ) : ℕ := c.logInvRates.getD i 0
def WHIRConfig.ki  (c : WHIRConfig) (i : ℕ) : ℕ := c.foldingFactors.getD i 0

/-- Rate `2^{-μ}` as a `Rate`. Clamped at `μ ≥ 1` so it is total (WHIR always has `μ ≥ 1`);
    the `Regime` methods ignore the positivity proof, so the clamp is never observed. -/
def whirRate (μ : ℕ) : Rate :=
  ⟨1 / 2 ^ (max μ 1), by positivity, by
    rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)⟩

/-- The code `C_{RS}^{i,s}` has rate `2^{-μ_i}` (constant across rounds `s`) and dimension
    `2^{m_i - s}`. -/
def WHIRConfig.rate (c : WHIRConfig) (i : ℕ) : Rate := whirRate (c.mui i)
def WHIRConfig.dim  (c : WHIRConfig) (i s : ℕ) : ℕ := 2 ^ (c.mi i - s)

/-- `ℓ_{i,s}`: list size of `C_{RS}^{i,s}` in this regime. -/
def WHIRConfig.listSize (c : WHIRConfig) (R : Regime) (i s : ℕ) : ℚ :=
  R.listSize (c.rate i) (c.dim i s)

/-- `δ_i = min_{0 ≤ s ≤ k_i} θ(C_{RS}^{i,s})`, using `θLB` (conservative: smallest `δ`). -/
def WHIRConfig.deltaLB (c : WHIRConfig) (R : Regime) (i : ℕ) : ℚ :=
  ((List.range (c.ki i + 1)).map (fun s => R.θLB (c.rate i) (c.dim i s))).foldr min 1

/-! ## Error components (Theorem 5.2). `apply_grinding ε b = ε / 2^b`. -/

/-- Batching error (`whir.py _get_batching_error`): powers vs. linear combination, ground. -/
def WHIRConfig.batchingErr (c : WHIRConfig) (R : Regime) : ℚ :=
  let base := if c.powerBatch then R.errPowers (c.rate 0) (c.dim 0 0) c.batchSize
              else R.errLinear (c.rate 0) (c.dim 0 0)
  base / 2 ^ c.grindBatch

/-- Folding-round error `ε^fold_{i,s}` (`_epsilon_fold`): `d·ℓ_{i,s-1}/|F|` plus the
    proximity-gaps error `err(C^{i,s}, 2, δ_i)`, ground. -/
def WHIRConfig.epsilonFold (c : WHIRConfig) (R : Regime) (i s : ℕ) : ℚ :=
  let term1 := (c.constraintDegree : ℚ) * c.listSize R i (s - 1) / (c.field.card : ℚ)
  let term2 := R.errPowers (c.rate i) (c.dim i s) 2
  (term1 + term2) / 2 ^ ((c.grindFolding.getD i []).getD (s - 1) 0)

/-- Query-only error `(1 - δ_i)^{t_i}` (`_epsilon_query`), ground. -/
def WHIRConfig.epsilonQuery (c : WHIRConfig) (R : Regime) (i : ℕ) : ℚ :=
  (1 - c.deltaLB R i) ^ (c.numQueries.getD i 0) / 2 ^ (c.grindQueries.getD i 0)

/-- Out-of-domain error `ε^out_i` (`_epsilon_out`): `ℓ_{i,0}² · (2^{m_i}/(2|F|))^{w_i}`, ground. -/
def WHIRConfig.epsilonOut (c : WHIRConfig) (R : Regime) (i : ℕ) : ℚ :=
  let ℓ := c.listSize R i 0
  let w := c.numOodSamples.getD (i - 1) 0
  ℓ ^ 2 * ((2 : ℚ) ^ c.mi i / (2 * (c.field.card : ℚ))) ^ w / 2 ^ (c.grindOod.getD (i - 1) 0)

/-- Shift error `ε^shift_i` (`_epsilon_shift`): `(1-δ_{i-1})^{t_{i-1}} + ℓ_{i,0}·(t_{i-1}+1)/|F|`, ground. -/
def WHIRConfig.epsilonShift (c : WHIRConfig) (R : Regime) (i : ℕ) : ℚ :=
  let t := c.numQueries.getD (i - 1) 0
  let term1 := (1 - c.deltaLB R (i - 1)) ^ t
  let term2 := c.listSize R i 0 * ((t : ℚ) + 1) / (c.field.card : ℚ)
  (term1 + term2) / 2 ^ (c.grindQueries.getD (i - 1) 0)

/-- Final error `ε^fin = ε^query_{M-1}` (`_epsilon_final`). -/
def WHIRConfig.epsilonFinal (c : WHIRConfig) (R : Regime) : ℚ :=
  c.epsilonQuery R (c.numIterations - 1)

/-- All PCS soundness-error cells, mirroring `whir.py get_pcs_security_levels`: the batching
    error (only when `t > 1`), the iteration-0 fold rounds `s = 1 … k_0`, then for each
    main-loop iteration `i = 1 … M-1` its OOD, shift, and fold-round errors, and finally
    `ε^fin`. (Enumeration order matches the Python dict insertion order.) -/
def WHIRConfig.listErrs (c : WHIRConfig) (R : Regime) : List ℚ :=
  (if 1 < c.batchSize then [c.batchingErr R] else []) ++
  ((List.range' 1 (c.ki 0)).map (fun s => c.epsilonFold R 0 s)) ++
  ((List.range' 1 (c.numIterations - 1)).flatMap (fun i =>
      c.epsilonOut R i :: c.epsilonShift R i ::
      (List.range' 1 (c.ki i)).map (fun s => c.epsilonFold R i s))) ++
  [c.epsilonFinal R]

/-! ## Accessors (`whir.py get_rate` / `get_dimension` / `get_trace_length`) -/

/-- Initial rate `ρ_0 = 2^{-μ_0}`. -/
def WHIRConfig.rate0 (c : WHIRConfig) : Rate := c.rate 0
/-- `2^{m_0}` — the initial dimension, i.e. the trace length. -/
def WHIRConfig.dimension (c : WHIRConfig) : ℕ := 2 ^ c.mi 0

-- Intentionally not ported from `whir.py`: `_get_log_grinding_overhead` (an informational
-- *prover-cost* metric `round(log₂(Σ 2^grind), 2)`, a rounded float display value — not a
-- soundness error or proof-size quantity), and the string renderers `get_parameter_summary`
-- / `get_report_parameter_lines`.

/-! ## Proof size (`whir.py _get_proof_size_bits`)

Counts prover messages only (verifier messages come from Fiat–Shamir): field elements sent
directly, polynomials as coefficient vectors, functions as Merkle roots, evaluations as
Merkle paths. The initial trace `f_0` is over the base field; folded functions, sumcheck
polynomials, and OOD answers are over the extension field. Each sumcheck round sends only
`d-1` evaluations (Gruen 2024 optimisation: the verifier derives `h(1) = claim - h(0)`). -/
def getWHIRProofSizeBits (c : WHIRConfig) (expected : Bool) : ℕ :=
  let baseBits := c.field.baseElementSizeBits
  let extBits  := c.field.elementSizeBits
  -- initial commitment (Merkle root) + initial sumcheck (k_0 polys × (d-1) evaluations)
  let initial := c.hashBits + c.ki 0 * (c.constraintDegree - 1) * extBits
  -- main loop i = 1 … M-1: f_i commitment + OOD answers + sumcheck
  let mainLoop := (List.range' 1 (c.numIterations - 1)).foldl (fun acc i =>
      acc + c.hashBits + c.numOodSamples.getD (i - 1) 0 * extBits
          + c.ki i * (c.constraintDegree - 1) * extBits) 0
  -- final multilinear polynomial: 2^{m_M} coefficients over the extension field
  let finalPoly := 2 ^ c.mi c.numIterations * extBits
  -- decision phase: t_i Merkle multi-proofs per iteration i = 0 … M-1
  --   (leaf = one folding block of 2^{k_i} elements; iteration 0 also carries all batch polys)
  let queryPhase := (List.range c.numIterations).foldl (fun acc i =>
      let domainSize  := 2 ^ (c.mi i + c.mui i)
      let blockSize   := 2 ^ c.ki i
      let numLeafs    := domainSize / blockSize
      let elementBits := if i = 0 then baseBits else extBits
      let tupleSize   := if i = 0 then blockSize * c.batchSize else blockSize
      acc + getSizeOfMerkleMultiProofBits numLeafs (c.numQueries.getD i 0)
              tupleSize elementBits c.hashBits expected) 0
  initial + mainLoop + finalPoly + queryPhase

def WHIRConfig.proofSizeExp   (c : WHIRConfig) : ℕ := getWHIRProofSizeBits c true
def WHIRConfig.proofSizeWorst (c : WHIRConfig) : ℕ := getWHIRProofSizeBits c false

/-! ## Validation against `reports/dummywhir.md` (`riscv` circuit, all error types) -/

/-- DummyWHIR `riscv` circuit (generated from `dummy_whir.toml`). The TOML block's
`num_constraints` / `air_max_degree` / `opening_points` are intentionally absent: they
feed the enclosing DEEP-ALI proof system (the report's `ALI`/`DEEP` columns), not the WHIR
PCS, and `whir.py`'s `WHIRConfig` does not read them either. -/
def dwRiscvWHIR : WHIRConfig where
  hashBits         := 256
  field            := goldilocks3
  logInvRate       := 4
  numIterations    := 5
  foldingFactors   := [4, 4, 4, 4, 4]
  logDegree        := 22
  batchSize        := 200
  powerBatch       := true
  grindBatch       := 21
  constraintDegree := 8
  grindFolding     := [[16, 14, 12, 10], [14, 12, 10, 8], [17, 15, 13, 11],
                       [19, 17, 15, 13], [22, 20, 18, 16]]
  numQueries       := [55, 31, 22, 17, 14]
  grindQueries     := [22, 22, 20, 19, 17]
  numOodSamples    := [1, 1, 1, 1]
  grindOod         := [0, 0, 0, 0]

abbrev dwUDR : Regime := UDR goldilocks3
-- `g = 2^40` is the Johnson-bound proximity-gap parameter the report's JBR column was
-- computed with; the full JBR row below matches `reports/dummywhir.md` byte-for-byte.
abbrev dwJBR : Regime := JBR goldilocks3 (2 ^ 40)

-- The two `listErrs` rows below enumerate *every* WHIR error cell — batching, `fin`, and
-- all fold/OOD/shift rounds — so they already pin each individual `epsilonFold`/`epsilonOut`/
-- `epsilonShift`/`batchingErr`/`epsilonFinal` value; no separate per-cell examples are needed.

-- proof size (regime-independent): 1475 KiB expected / 1500 KiB worst case
example : dwRiscvWHIR.proofSizeExp   / KIB = 1475 := by native_decide
example : dwRiscvWHIR.proofSizeWorst / KIB = 1500 := by native_decide
-- full cell enumeration (get_pcs_security_levels): the entire WHIR row of reports/dummywhir.md
example : (dwRiscvWHIR.listErrs dwUDR).map secBits =
    [180, 184, 183, 182, 181, 174, 72, 183, 182, 181, 180, 178, 52, 187, 186, 185, 184,
     182, 41, 190, 189, 188, 187, 186, 35, 194, 192, 191, 190, 30] := by native_decide
example : (dwRiscvWHIR.listErrs dwJBR).map secBits =
    [145, 149, 148, 147, 146, 149, 131, 143, 142, 141, 140, 147, 130, 143, 142, 141, 140,
     145, 129, 141, 140, 139, 138, 143, 129, 141, 140, 139, 138, 128] := by native_decide

end Soundcalc
