import Soundcalc.Circuit.SWIRL.Circuit

open Soundcalc

/-!
# SWIRL circuit — proof size

Port of `soundcalc/circuits/swirl/proof_size.py`. `get_swirl_proof_size_bits` counts *encoded*
bytes of the transcript (`stark-backend/src/proof.rs`), split into five sections: preamble, GKR,
batch-constraint, stacking, and WHIR. Base-field elements are byte-padded to whole bytes
(`8·⌈bits/8⌉`) and extension elements are `degree` of those — so the codec width (`32`/`128` for
BabyBear⁴) differs from the field-capacity width (`31`/`124`). All bounds read are the
soundness/proof-size `.envelope` values (worst-case sizing).
-/

namespace Soundcalc

/-! ## Codec widths and constants (`proof_size.py` top matter) -/

/-- Base-field element as encoded in the proof: byte-padded to whole bytes,
`8·⌈base_field_element_size_bits / 8⌉` (BabyBear: `31 → 32`). -/
private def swBaseBits (F : FieldParams) : ℕ := 8 * ((F.baseElementSizeBits + 7) / 8)

/-- Extension-field element in the codec: `swBaseBits · field_extension_degree`
(BabyBear⁴: `32·4 = 128`, *not* the `124`-bit field-capacity width). -/
private def swExtBits (F : FieldParams) : ℕ := swBaseBits F * F.e

private def swU32 : ℕ := 32
private def swU8 : ℕ := 8
/-- `OPENVM_NUM_COMMITS`: common-main + one cached-trace commit. -/
private def swNumCommits : ℕ := 2
/-- `OPENVM_NUM_CACHED_COMMITMENTS`. -/
private def swNumCached : ℕ := 1

/-- `_vec_bits`: a length-prefixed vector is a `u32` length plus its payload. -/
private def swVecBits (length elementBits : ℕ) : ℕ := swU32 + length * elementBits

/-- `_round0_univariate_len`: a degree-`degree` univariate over the size-`2^l_skip` coset needs
`degree·(2^l_skip − 1) + 1` coefficients. -/
private def swRound0UnivariateLen (lSkip degree : ℕ) : ℕ := degree * (2 ^ lSkip - 1) + 1

/-! ## Proof-size sections (`proof_size.py`) -/

/-- `_preamble_bits`: codec version, common-main commit, per-AIR trace metadata, and public
values. -/
private def swPreambleBits (c : SWIRLCfg) : ℕ :=
  let baseBits := swBaseBits c.whir.field
  let digest   := c.whir.hashBits
  let numAirs  := c.airs.envelope
  swU32                                 -- CODEC_VERSION
  + digest                              -- common_main_commit
  + swU32                               -- num_airs
  + ((numAirs + 7) / 8) * swU8          -- trace_vdata bitmap: ⌈num_airs/8⌉ bytes
  + numAirs * (swU32 + swU32)           -- per present AIR: log_height + cached_commitments Vec len
  + swNumCached * digest                -- cached-commitment digest
  + swU32                               -- public_values outer Vec length
  + numAirs * swU32                     -- one base-field Vec length per AIR
  + c.numPublicValues * baseBits

/-- `_gkr_bits`: LogUp-GKR PoW witness, `q0` claim, and the sumcheck round polynomials over
`num_gkr_rounds = l_skip + n_logup` rounds. Note the LogUp bound here uses the field prime
`field.p` as the interaction-count cap (not the soundness config's value). -/
private def swGkrBits (c : SWIRLCfg) : ℕ :=
  let baseBits := swBaseBits c.whir.field
  let extBits  := swExtBits c.whir.field
  let bits0 := baseBits + extBits                      -- logup_pow_witness + q0_claim
  if c.airs.envelope = 0 ∨ c.interactions.envelope = 0 then
    bits0 + swVecBits 0 (4 * extBits)                  -- empty round Vec (= bits0 + swU32)
  else
    let nLogup := swNLogupBound c.lSkip c.airs.envelope c.interactions.envelope
                    c.logTraceHeight.envelope c.whir.field.p
    let numGkrRounds := c.lSkip + nLogup
    let numSumcheckArrays := numGkrRounds * (numGkrRounds - 1) / 2
    bits0 + swVecBits numGkrRounds (4 * extBits) + numSumcheckArrays * 3 * extBits

/-- `_batch_constraint_bits`: fused numerator/denominator terms, the round-0 univariate, the
`n_max` multilinear sumcheck rows, and the opening bookkeeping. -/
private def swBatchConstraintBits (c : SWIRLCfg) : ℕ :=
  let extBits        := swExtBits c.whir.field
  let numAirs        := c.airs.envelope
  let nMax           := c.logTraceHeight.envelope - c.lSkip
  let univariateLen  := swRound0UnivariateLen c.lSkip (c.maxConstraintDegree + 1)
  let sumcheckRowLen := c.maxConstraintDegree + 1
  swVecBits numAirs extBits                            -- numerator_term_per_air
  + numAirs * extBits                                  -- denominator_term_per_air (implicit len)
  + swVecBits univariateLen extBits
  + swU32                                              -- n_max
  + (if nMax > 0 then swU32 + nMax * sumcheckRowLen * extBits else 0)
  + numAirs * swU32                                    -- per-AIR part count
  + (numAirs + 1) * swU32                              -- _num_opening_parts = num_airs + 1
  + (2 * c.traceColumns.envelope) * extBits            -- _num_column_openings

/-- `_stacking_bits`: the round-0 univariate (degree 2), `n_stack` multilinear rows, and the
stacking openings. -/
private def swStackingBits (c : SWIRLCfg) : ℕ :=
  let extBits       := swExtBits c.whir.field
  let univariateLen := swRound0UnivariateLen c.lSkip 2
  swVecBits univariateLen extBits
  + swU32                                              -- sumcheck_round_polys length
  + c.nStack * 2 * extBits
  + swU32                                              -- stacking_openings outer length
  + swNumCommits * swU32                               -- per-commit lengths
  + c.wStack * extBits

/-- `_whir_bits`: the WHIR opening — μ PoW witness, folding sumcheck polynomials, per-round
codeword commitments + OOD answers, PoW witnesses, and the query phase (initial base-field
block with its Merkle paths, then per-round extension openings and paths), plus the final
multilinear polynomial. -/
private def swWhirBits (c : SWIRLCfg) : ℕ :=
  let baseBits         := swBaseBits c.whir.field
  let extBits          := swExtBits c.whir.field
  let digest           := c.whir.hashBits
  let numRounds        := c.whir.numIterations
  let k                := c.k
  let blockSize        := 2 ^ k
  let logStackedHeight := c.whir.logDegree
  let logFinalPolyLen  := logStackedHeight - numRounds * k
  let numSumcheckRounds := numRounds * k
  let header :=
    baseBits                                           -- mu_pow_witness
    + swVecBits numSumcheckRounds (2 * extBits)         -- sumcheck round polys
    + swVecBits (numRounds - 1) digest                 -- codeword_commits
    + (numRounds - 1) * extBits                         -- ood_values (implicit len)
    + numSumcheckRounds * baseBits                      -- folding_pow_witnesses
    + numRounds * baseBits                              -- query_phase_pow_witnesses
  let initialQueries := c.whir.numQueries.headD 0
  let initialBlock :=
    swU32 + swU32                                      -- num_commits + initial_num_whir_queries
    + (if initialQueries > 0 then
         let initialMerkleDepth := logStackedHeight + c.logBlowup - k
         swU32                                         -- initial Merkle depth
         + swNumCommits * swU32                        -- per-commit widths
         + initialQueries * blockSize * c.wStack * baseBits
         + swNumCommits * initialQueries * initialMerkleDepth * digest
       else 0)
  -- non-initial rounds i = 1 … M-1: sumcheck-poly openings, then (after a u32) Merkle paths
  let roundOpenings := (List.range' 1 (numRounds - 1)).foldl (fun acc i =>
      acc + swU32 + c.whir.numQueries.getD i 0 * blockSize * extBits) 0
  let roundMerkle := (List.range' 1 (numRounds - 1)).foldl (fun acc i =>
      let merkleDepth := logStackedHeight + c.logBlowup - k - i
      acc + c.whir.numQueries.getD i 0 * merkleDepth * digest) 0
  header + initialBlock + roundOpenings
    + swU32                                            -- first non-initial Merkle depth (u32)
    + roundMerkle
    + swVecBits (2 ^ logFinalPolyLen) extBits           -- final multilinear polynomial

/-- SWIRL proof size in bits (`get_proof_size_bits` = `get_expected_proof_size_bits` = the sum of
the five sections `_get_proof_size_bits` accumulates). -/
def SWIRLCfg.proofSizeBits (c : SWIRLCfg) : ℕ :=
  swPreambleBits c + swGkrBits c + swBatchConstraintBits c
  + swStackingBits c + swWhirBits c

end Soundcalc

