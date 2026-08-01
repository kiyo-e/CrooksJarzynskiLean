/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpLocalBalance

/-!
# Crooks and Jarzynski for segmentwise jump rates

This module connects the local rate-density identity to the measure-level
Crooks and Jarzynski statements.  Forward and reverse escape rates are supplied
in time-reversal-aligned segment coordinates; their equality is the exact
cancellation of the waiting-time survival factors.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace JumpPath

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

/-- Reverse-rate likelihood in the reverse experiment's own chronological
coordinates. -/
noncomputable def reverseRateDensity
    (finalWeight : Ω → ℝ≥0∞)
    (escapeRate : Fin (n + 1) → Ω → NNReal)
    (jumpRate : Fin n → Ω → Ω → NNReal) : JumpPath Ω n → ℝ≥0∞ :=
  alignedReverseRateDensity finalWeight escapeRate jumpRate ∘ reverse

omit [MeasurableSpace Ω] in
/-- Pulling the reverse-rate likelihood back by reversal recovers its aligned
forward-coordinate form. -/
@[simp]
theorem reverseRateDensity_reverse
    (finalWeight : Ω → ℝ≥0∞)
    (escapeRate : Fin (n + 1) → Ω → NNReal)
    (jumpRate : Fin n → Ω → Ω → NNReal)
    (γ : JumpPath Ω n) :
    reverseRateDensity finalWeight escapeRate jumpRate (reverse γ) =
      alignedReverseRateDensity finalWeight escapeRate jumpRate γ := by
  simp [reverseRateDensity]

/-- The pointwise local-balance identity, packaged almost everywhere for reuse
by both the Crooks and Jarzynski theorems. -/
theorem rateDensity_mul_rateWorkWeight_ae
    (reference : Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape : Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump : Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ i x, forwardEscape i x = reverseEscape i x)
    (hjump : ∀ i x y,
      jumpWeightOfRate forwardJump i x y * jumpWork i x y =
        jumpWeightOfRate reverseJump i y x) :
    ∀ᵐ γ ∂reference,
      rateDensity initialWeight forwardEscape forwardJump γ *
          rateWorkWeight boundaryWork jumpWork γ =
        freeEnergyWeight *
          reverseRateDensity finalWeight reverseEscape reverseJump
            (reverse γ) := by
  refine ae_of_all reference fun γ => ?_
  rw [reverseRateDensity_reverse]
  exact rateDensity_mul_rateWorkWeight initialWeight finalWeight
    forwardEscape reverseEscape forwardJump reverseJump
    boundaryWork jumpWork freeEnergyWeight
    hboundary hescape hjump γ

/-- Crooks' relation for the segmentwise constant-rate model. Equality of the
aligned escape rates cancels the waiting-time factors; endpoint reweighting and
local jump balance supply the remaining density ratio. -/
theorem crooks_of_rate_local_balance
    (reference : Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape : Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump : Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hreference : reference.map reverse = reference)
    (hforward :
      Measurable (rateDensity initialWeight forwardEscape forwardJump))
    (halignedReverse :
      Measurable
        (alignedReverseRateDensity finalWeight reverseEscape reverseJump))
    (hwork : Measurable (rateWorkWeight boundaryWork jumpWork))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ i x, forwardEscape i x = reverseEscape i x)
    (hjump : ∀ i x y,
      jumpWeightOfRate forwardJump i x y * jumpWork i x y =
        jumpWeightOfRate reverseJump i y x) :
    CrooksRelation
      (pathMeasure reference
        (rateDensity initialWeight forwardEscape forwardJump))
      (timeReversedMeasure
        (pathMeasure reference
          (reverseRateDensity finalWeight reverseEscape reverseJump)))
    (rateWorkWeight boundaryWork jumpWork) freeEnergyWeight := by
  apply crooks_of_density_identity reference
    (rateDensity initialWeight forwardEscape forwardJump)
    (reverseRateDensity finalWeight reverseEscape reverseJump)
    (rateWorkWeight boundaryWork jumpWork) freeEnergyWeight
    hreference hforward (halignedReverse.comp measurable_reverse) hwork
  exact rateDensity_mul_rateWorkWeight_ae reference initialWeight finalWeight
    forwardEscape reverseEscape forwardJump reverseJump
    boundaryWork jumpWork freeEnergyWeight
    hboundary hescape hjump

/-- Jarzynski's equality for the segmentwise constant-rate model. -/
theorem jarzynski_of_rate_local_balance
    (reference : Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape : Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump : Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure
      (pathMeasure reference
        (reverseRateDensity finalWeight reverseEscape reverseJump))]
    (hreference : reference.map reverse = reference)
    (hforward :
      Measurable (rateDensity initialWeight forwardEscape forwardJump))
    (halignedReverse :
      Measurable
        (alignedReverseRateDensity finalWeight reverseEscape reverseJump))
    (hwork : Measurable (rateWorkWeight boundaryWork jumpWork))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ i x, forwardEscape i x = reverseEscape i x)
    (hjump : ∀ i x y,
      jumpWeightOfRate forwardJump i x y * jumpWork i x y =
        jumpWeightOfRate reverseJump i y x) :
    ∫⁻ γ, rateWorkWeight boundaryWork jumpWork γ
        ∂(pathMeasure reference
          (rateDensity initialWeight forwardEscape forwardJump)) =
      freeEnergyWeight := by
  apply jarzynski_of_density_identity reference
    (rateDensity initialWeight forwardEscape forwardJump)
    (reverseRateDensity finalWeight reverseEscape reverseJump)
    (rateWorkWeight boundaryWork jumpWork) freeEnergyWeight
    hreference hforward (halignedReverse.comp measurable_reverse) hwork
  exact rateDensity_mul_rateWorkWeight_ae reference initialWeight finalWeight
    forwardEscape reverseEscape forwardJump reverseJump
    boundaryWork jumpWork freeEnergyWeight
    hboundary hescape hjump

end JumpPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
