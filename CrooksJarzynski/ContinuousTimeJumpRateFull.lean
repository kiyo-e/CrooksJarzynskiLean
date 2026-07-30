/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpRateCrooks

/-!
# Full path laws for segmentwise continuous-time jump rates

This module sums the rate-level fixed-jump-count Crooks relations over every
finite jump count.  It also provides the corresponding fixed-horizon and
Jarzynski statements.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FullPath

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Forward path measure in the `n`-jump sector for segmentwise constant rates. -/
noncomputable def forwardRateSectorMeasure
    (reference : (n : ℕ) → Measure (JumpPath Ω n))
    (initialWeight : Ω → ℝ≥0∞)
    (escapeRate : (n : ℕ) → Fin (n + 1) → Ω → NNReal)
    (jumpRate : (n : ℕ) → Fin n → Ω → Ω → NNReal)
    (n : ℕ) : Measure (JumpPath Ω n) :=
  pathMeasure (reference n)
    (JumpPath.rateDensity initialWeight (escapeRate n) (jumpRate n))

/-- Time-reversed reverse-experiment measure in the `n`-jump sector. -/
noncomputable def reversedRateSectorMeasure
    (reference : (n : ℕ) → Measure (JumpPath Ω n))
    (finalWeight : Ω → ℝ≥0∞)
    (escapeRate : (n : ℕ) → Fin (n + 1) → Ω → NNReal)
    (jumpRate : (n : ℕ) → Fin n → Ω → Ω → NNReal)
    (n : ℕ) : Measure (JumpPath Ω n) :=
  JumpPath.timeReversedMeasure
    (pathMeasure (reference n)
      (JumpPath.reverseRateDensity finalWeight (escapeRate n) (jumpRate n)))

/-- Work observable family on all jump-count sectors. -/
noncomputable def rateWorkWeightFamily
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : (n : ℕ) → Fin n → Ω → Ω → ℝ≥0∞)
    (n : ℕ) : JumpPath Ω n → ℝ≥0∞ :=
  JumpPath.rateWorkWeight boundaryWork (jumpWork n)

/-- The full finite-jump Crooks relation obtained by summing the rate-level
local-balance theorem over every jump-count sector. -/
theorem crooks_of_rate_local_balance
    (reference : (n : ℕ) → Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape :
      (n : ℕ) → Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump :
      (n : ℕ) → Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : (n : ℕ) → Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hreference : ∀ n, (reference n).map JumpPath.reverse = reference n)
    (hforward : ∀ n,
      Measurable
        (JumpPath.rateDensity initialWeight (forwardEscape n) (forwardJump n)))
    (halignedReverse : ∀ n,
      Measurable
        (JumpPath.alignedReverseRateDensity finalWeight
          (reverseEscape n) (reverseJump n)))
    (hwork : ∀ n,
      Measurable (JumpPath.rateWorkWeight boundaryWork (jumpWork n)))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ n i x,
      forwardEscape n i x = reverseEscape n i x)
    (hjump : ∀ n i x y,
      JumpPath.jumpWeightOfRate (forwardJump n) i x y *
          jumpWork n i x y =
        JumpPath.jumpWeightOfRate (reverseJump n) i y x) :
    CrooksRelation
      (measure
        (forwardRateSectorMeasure reference initialWeight
          forwardEscape forwardJump))
      (measure
        (reversedRateSectorMeasure reference finalWeight
          reverseEscape reverseJump))
      (weight (rateWorkWeightFamily boundaryWork jumpWork))
      freeEnergyWeight := by
  apply crooks_of_sector_relations
    (forwardRateSectorMeasure reference initialWeight
      forwardEscape forwardJump)
    (reversedRateSectorMeasure reference finalWeight
      reverseEscape reverseJump)
    (rateWorkWeightFamily boundaryWork jumpWork)
    freeEnergyWeight hwork
  intro n
  exact JumpPath.crooks_of_rate_local_balance
    (reference n) initialWeight finalWeight
    (forwardEscape n) (reverseEscape n)
    (forwardJump n) (reverseJump n)
    boundaryWork (jumpWork n) freeEnergyWeight
    (hreference n) (hforward n) (halignedReverse n) (hwork n)
    hboundary (hescape n) (hjump n)

/-- Full finite-jump Jarzynski equality for the segmentwise rate model. -/
theorem jarzynski_of_rate_local_balance
    (reference : (n : ℕ) → Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape :
      (n : ℕ) → Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump :
      (n : ℕ) → Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : (n : ℕ) → Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure
      (measure
        (reversedRateSectorMeasure reference finalWeight
          reverseEscape reverseJump))]
    (hreference : ∀ n, (reference n).map JumpPath.reverse = reference n)
    (hforward : ∀ n,
      Measurable
        (JumpPath.rateDensity initialWeight (forwardEscape n) (forwardJump n)))
    (halignedReverse : ∀ n,
      Measurable
        (JumpPath.alignedReverseRateDensity finalWeight
          (reverseEscape n) (reverseJump n)))
    (hwork : ∀ n,
      Measurable (JumpPath.rateWorkWeight boundaryWork (jumpWork n)))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ n i x,
      forwardEscape n i x = reverseEscape n i x)
    (hjump : ∀ n i x y,
      JumpPath.jumpWeightOfRate (forwardJump n) i x y *
          jumpWork n i x y =
        JumpPath.jumpWeightOfRate (reverseJump n) i y x) :
    ∫⁻ γ, weight (rateWorkWeightFamily boundaryWork jumpWork) γ
        ∂(measure
          (forwardRateSectorMeasure reference initialWeight
            forwardEscape forwardJump)) =
      freeEnergyWeight :=
  jarzynski_lintegral _ _ _ _
    (crooks_of_rate_local_balance reference initialWeight finalWeight
      forwardEscape reverseEscape forwardJump reverseJump
      boundaryWork jumpWork freeEnergyWeight hreference hforward
      halignedReverse hwork hboundary hescape hjump)

/-- The full rate-level Crooks relation after every sector is restricted to the
same physical time horizon. -/
theorem crooks_restrict_horizon_of_rate_local_balance
    (T : NNReal)
    (reference : (n : ℕ) → Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape :
      (n : ℕ) → Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump :
      (n : ℕ) → Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : (n : ℕ) → Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hreference : ∀ n, (reference n).map JumpPath.reverse = reference n)
    (hforward : ∀ n,
      Measurable
        (JumpPath.rateDensity initialWeight (forwardEscape n) (forwardJump n)))
    (halignedReverse : ∀ n,
      Measurable
        (JumpPath.alignedReverseRateDensity finalWeight
          (reverseEscape n) (reverseJump n)))
    (hwork : ∀ n,
      Measurable (JumpPath.rateWorkWeight boundaryWork (jumpWork n)))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ n i x,
      forwardEscape n i x = reverseEscape n i x)
    (hjump : ∀ n i x y,
      JumpPath.jumpWeightOfRate (forwardJump n) i x y *
          jumpWork n i x y =
        JumpPath.jumpWeightOfRate (reverseJump n) i y x) :
    CrooksRelation
      (measure fun n => JumpPath.horizonMeasure T
        (forwardRateSectorMeasure reference initialWeight
          forwardEscape forwardJump n))
      (measure fun n => JumpPath.horizonMeasure T
        (reversedRateSectorMeasure reference finalWeight
          reverseEscape reverseJump n))
      (weight (rateWorkWeightFamily boundaryWork jumpWork))
      freeEnergyWeight := by
  apply crooks_restrict_horizon_of_sector_relations T
    (forwardRateSectorMeasure reference initialWeight
      forwardEscape forwardJump)
    (reversedRateSectorMeasure reference finalWeight
      reverseEscape reverseJump)
    (rateWorkWeightFamily boundaryWork jumpWork)
    freeEnergyWeight hwork
  intro n
  exact JumpPath.crooks_of_rate_local_balance
    (reference n) initialWeight finalWeight
    (forwardEscape n) (reverseEscape n)
    (forwardJump n) (reverseJump n)
    boundaryWork (jumpWork n) freeEnergyWeight
    (hreference n) (hforward n) (halignedReverse n) (hwork n)
    hboundary (hescape n) (hjump n)

/-- Fixed-horizon Jarzynski equality for the full segmentwise rate model. -/
theorem jarzynski_restrict_horizon_of_rate_local_balance
    (T : NNReal)
    (reference : (n : ℕ) → Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape :
      (n : ℕ) → Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump :
      (n : ℕ) → Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : (n : ℕ) → Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure
      (measure fun n => JumpPath.horizonMeasure T
        (reversedRateSectorMeasure reference finalWeight
          reverseEscape reverseJump n))]
    (hreference : ∀ n, (reference n).map JumpPath.reverse = reference n)
    (hforward : ∀ n,
      Measurable
        (JumpPath.rateDensity initialWeight (forwardEscape n) (forwardJump n)))
    (halignedReverse : ∀ n,
      Measurable
        (JumpPath.alignedReverseRateDensity finalWeight
          (reverseEscape n) (reverseJump n)))
    (hwork : ∀ n,
      Measurable (JumpPath.rateWorkWeight boundaryWork (jumpWork n)))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ n i x,
      forwardEscape n i x = reverseEscape n i x)
    (hjump : ∀ n i x y,
      JumpPath.jumpWeightOfRate (forwardJump n) i x y *
          jumpWork n i x y =
        JumpPath.jumpWeightOfRate (reverseJump n) i y x) :
    ∫⁻ γ, weight (rateWorkWeightFamily boundaryWork jumpWork) γ
        ∂(measure fun n => JumpPath.horizonMeasure T
          (forwardRateSectorMeasure reference initialWeight
            forwardEscape forwardJump n)) =
      freeEnergyWeight :=
  jarzynski_lintegral _ _ _ _
    (crooks_restrict_horizon_of_rate_local_balance T reference
      initialWeight finalWeight forwardEscape reverseEscape
      forwardJump reverseJump boundaryWork jumpWork freeEnergyWeight
      hreference hforward halignedReverse hwork hboundary hescape hjump)

end FullPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
