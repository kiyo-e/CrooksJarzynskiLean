/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenWindowBalance
import CrooksJarzynski.ContinuousTimeJumpDrivenTwoState

/-!
# Stepwise driven fluctuation relations from Gibbs detailed balance

This module closes the generator-to-protocol bridge for finite state spaces.
Every protocol window uses the normalized fixed-initial law `pathLawFrom`, and
instantaneous Gibbs detailed balance is converted internally into the
measure-level `WindowBalance` required by the marked-path Crooks induction.
The public statements therefore concern the constructed driven path laws and
require no separately supplied path-measure balance hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Nonempty Ω]

/-- Every real-valued function on a finite counting space is integrable. -/
private theorem integrable_count_fintype (f : Ω → ℝ) :
    Integrable f (Measure.count : Measure Ω) := by
  classical
  apply Integrable.of_bound
    (Measurable.of_discrete : Measurable f).aestronglyMeasurable
    (∑ x : Ω, ‖f x‖)
  filter_upwards [] with x
  exact Finset.single_le_sum (f := fun y : Ω => ‖f y‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ x)

/-- The free-energy difference for counting measure is the difference of the
explicit finite-state Helmholtz free energies. -/
theorem deltaFreeEnergy_count_eq_finite
    {M : ℕ} (β : ℝ) (energy : Fin (M + 1) → Ω → ℝ) :
    deltaFreeEnergy (Measure.count : Measure Ω) β energy =
      FiniteJumpGenerator.finiteFreeEnergy β (energy (Fin.last M)) -
        FiniteJumpGenerator.finiteFreeEnergy β (energy 0) := by
  simp [deltaFreeEnergy, Gibbs.deltaFreeEnergy,
    FiniteJumpGenerator.freeEnergy_count_eq]

/-- **Crooks relation for the constructed stepwise driven laws, derived only
from instantaneous Gibbs detailed balance in every window.** -/
theorem crooks_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    CrooksRelation
      (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration)
      (reverseDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M)))
        generator duration)
      (fun γ => ENNReal.ofReal (Real.exp (-β * work energy γ)))
      (ENNReal.ofReal
        (Real.exp (-β *
          deltaFreeEnergy (Measure.count : Measure Ω) β energy))) := by
  exact crooks (Measure.count : Measure Ω) β hβ energy generator duration
    (fun _ => Measurable.of_discrete)
    (fun i => integrable_count_fintype (Ω := Ω)
      (fun x => Real.exp (-β * energy i x)))
    (fun i =>
      (generator i).windowBalance_of_gibbsDetailedBalance
        (duration i) β (energy i.castSucc) (hbalance i))

/-- **Jarzynski equality for the constructed stepwise driven forward law,
derived only from instantaneous Gibbs detailed balance.** -/
theorem jarzynski_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    ∫ γ, Real.exp (-β * work energy γ)
        ∂forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
          generator duration =
      Real.exp (-β *
        deltaFreeEnergy (Measure.count : Measure Ω) β energy) := by
  exact jarzynski (Measure.count : Measure Ω) β hβ energy generator duration
    (fun _ => Measurable.of_discrete)
    (fun i => integrable_count_fintype (Ω := Ω)
      (fun x => Real.exp (-β * energy i x)))
    (fun i =>
      (generator i).windowBalance_of_gibbsDetailedBalance
        (duration i) β (energy i.castSucc) (hbalance i))

/-- **Average-work second law for the constructed stepwise driven law, derived
only from instantaneous Gibbs detailed balance.** -/
theorem second_law_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : 0 < β)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc))
    (hworkInt : Integrable (work energy)
      (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration)) :
    deltaFreeEnergy (Measure.count : Measure Ω) β energy ≤
      ∫ γ, work energy γ
        ∂forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
          generator duration := by
  exact second_law (Measure.count : Measure Ω) β hβ energy
    generator duration
    (fun _ => Measurable.of_discrete)
    (fun i => integrable_count_fintype (Ω := Ω)
      (fun x => Real.exp (-β * energy i x)))
    (fun i =>
      (generator i).windowBalance_of_gibbsDetailedBalance
        (duration i) β (energy i.castSucc) (hbalance i))
    hworkInt

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
