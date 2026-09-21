import Soundcalc.SecBits
import Soundcalc.Field.Core
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa

/-!
# ArkLib bridge

This module keeps the dependency direction explicit: it imports both Soundcalc and ArkLib, while
the core `Soundcalc` library remains independent of ArkLib.

The first bridge targets ArkLib's proved Reed--Solomon unique-decoding result. It deliberately
does not use ArkLib's admitted Johnson-range or Batched-FRI endpoints.
-/

namespace Soundcalc.ArkLibBridge

open Code CoreDefinitions ProximityGap

/-- The exact field-cardinality quotient used by ArkLib's unique-decoding bound, expressed in
ArkLib's nonnegative-real error carrier. -/
noncomputable def uniqueDecodingEnvelope (params : FieldParams) (domainSize : ℕ) : NNReal :=
  domainSize / params.card

/-- The same quotient in Soundcalc's computable rational error carrier. -/
def uniqueDecodingEnvelopeRat (params : FieldParams) (domainSize : ℕ) : ℚ :=
  domainSize / params.card

/-- The ArkLib and Soundcalc carriers denote the same real number. This is the conversion point
for feeding the transported bound into `Soundcalc.secBits` and report aggregation. -/
theorem uniqueDecodingEnvelope_coe_real (params : FieldParams) (domainSize : ℕ) :
    ((uniqueDecodingEnvelope params domainSize : NNReal) : ℝ) =
      (uniqueDecodingEnvelopeRat params domainSize : ℝ) := by
  simp [uniqueDecodingEnvelope, uniqueDecodingEnvelopeRat]

/-- A minimal agreement witness between a concrete finite field and Soundcalc's parameter model.

This first prototype only transports a theorem whose conclusion depends on field cardinality.
Later bridges should add characteristic, extension-degree, and code-parameter witnesses when
their source theorem requires them. -/
structure CardinalityAgreement (params : FieldParams) (F : Type*) [Fintype F] : Prop where
  card_eq : Fintype.card F = params.card

/-- Recover ArkLib's native cardinality quotient from a Soundcalc parameter agreement. -/
theorem uniqueDecodingEnvelope_eq_cardRatio
    {F : Type*} [Fintype F] (params : FieldParams)
    (agreement : CardinalityAgreement params F) (domainSize : ℕ) :
    uniqueDecodingEnvelope params domainSize =
      ((domainSize : NNReal) / Fintype.card F) := by
  simp [uniqueDecodingEnvelope, agreement.card_eq]

/-- Transport ArkLib's axiom-clean BCIKS20 Reed--Solomon MCA bound into a Soundcalc-labelled
field-cardinality envelope.

The hypotheses and error statement remain ArkLib's; the bridge only replaces the denominator
`Fintype.card F` with the cardinality certified by `FieldParams`. -/
theorem rs_mcaError_le_uniqueDecodingEnvelope
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (params : FieldParams) (agreement : CardinalityAgreement params F)
    {deg : ℕ} {domain : ι ↪ F} {δ : NNReal}
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ relativeUniqueDecodingRadius
      (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain deg) (δ : ℝ)
      ≤ ((uniqueDecodingEnvelope params (Fintype.card ι) : NNReal) : ENNReal) := by
  simpa [uniqueDecodingEnvelope, agreement.card_eq] using
    (ProximityGap.rs_mcaError_le_of_le_relUDR
      (deg := deg) (domain := domain) (δ := δ) hδ_pos hδ)

end Soundcalc.ArkLibBridge
