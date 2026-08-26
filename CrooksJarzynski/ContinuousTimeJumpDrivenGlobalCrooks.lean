/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenGlobalLaw
import CrooksJarzynski.ContinuousTimeJumpDrivenPhysical
import CrooksJarzynski.ContinuousTimeJumpDrivenWorkDistribution

/-!
# Fluctuation relations on global driven charts

The marked driven Crooks, Jarzynski, and second-law theorems descend to the
single concatenated real-time chart because global trajectory work recovers
the marked endpoint work almost surely.
-/

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [DecidableEq Ω] [Nonempty Ω]

omit [DecidableEq Ω] [Nonempty Ω] in
private theorem integrable_count_fintype_global (f : Ω → ℝ) :
    Integrable f (Measure.count : Measure Ω) := by
  apply Integrable.of_bound
    (Measurable.of_discrete : Measurable f).aestronglyMeasurable
    (∑ x : Ω, ‖f x‖)
  filter_upwards [] with x
  exact Finset.single_le_sum (f := fun y : Ω => ‖f y‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ x)

omit [Nonempty Ω] in
/-- The global reverse-experiment work distribution is the intrinsic marked
reverse-work distribution. -/
theorem map_globalReverseWork_reverseGlobalLaw
    {M : ℕ} (final : Measure Ω)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    (reverseGlobalLaw final generator duration).map
        (globalReverseWork energy duration) =
      (reverseDrivenLaw final generator duration).map
        (reverseWork energy) := by
  unfold reverseGlobalLaw
  rw [Measure.map_map
    (measurable_globalReverseWork energy duration
      fun _ => Measurable.of_discrete)
    measurable_concatenateWindows]
  apply Measure.map_congr
  filter_upwards
    [work_comp_concatenateWindows_ae_reverse
      final energy generator duration] with γ hγ
  rw [Function.comp_apply, globalReverseWork, hγ,
    ← reverseWork_eq_neg]

/-- **Work-distribution Crooks relation for the forward and aligned-reverse
global work laws.** The reverse carrier is chronology-aligned with the forward
protocol, so `globalWork` evaluated under `reverseGlobalLaw` is the aligned
work coordinate; the intrinsic reverse-chronology reading is carried by
`reverseWork` and `reverseWork_eq_neg` on the marked layer. -/
theorem global_work_distribution_crooks_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    CrooksRelation
      ((forwardGlobalLaw (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).map (globalWork energy duration))
      ((reverseGlobalLaw (Gibbs.measure (Measure.count : Measure Ω) β (energy (Fin.last M)))
        generator duration).map (globalWork energy duration))
      (fun w => ENNReal.ofReal (Real.exp (-β * w)))
      (ENNReal.ofReal (Real.exp (-β *
        deltaFreeEnergy (Measure.count : Measure Ω) β energy))) := by
  rw [map_globalWork_forwardGlobalLaw, map_globalWork_reverseGlobalLaw]
  exact work_distribution_crooks_of_gibbsDetailedBalance
    β hβ energy generator duration hbalance

/-- **Global work-distribution Crooks relation in the reverse experiment's
own work coordinate.** The reverse distribution is reflected by `w ↦ -w`
before comparison with the forward distribution. -/
theorem global_work_distribution_crooks_reverseWork_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    CrooksRelation
      ((forwardGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).map (globalWork energy duration))
      (((reverseGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M)))
        generator duration).map (globalReverseWork energy duration)).map
          (fun w : ℝ => -w))
      (fun w => ENNReal.ofReal (Real.exp (-β * w)))
      (ENNReal.ofReal
        (Real.exp (-β *
          deltaFreeEnergy (Measure.count : Measure Ω) β energy))) := by
  rw [map_globalWork_forwardGlobalLaw,
    map_globalReverseWork_reverseGlobalLaw]
  exact work_distribution_crooks_reverseWork_of_gibbsDetailedBalance
    β hβ energy generator duration hbalance

/-- **The conventional atomwise Crooks ratio on global charts**:
`P_F(W = w) = exp (β (w - ΔF)) · P_R(W_R = -w)`. -/
theorem global_crooks_work_atom_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc))
    (w : ℝ) :
    (forwardGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).real
        {γ | globalWork energy duration γ = w} =
      Real.exp (β * (w -
          deltaFreeEnergy (Measure.count : Measure Ω) β energy)) *
        (reverseGlobalLaw
          (Gibbs.measure (Measure.count : Measure Ω) β
            (energy (Fin.last M)))
          generator duration).real
          {γ | globalReverseWork energy duration γ = -w} := by
  have hforward := congrArg (fun μ : Measure ℝ => μ {w})
    (map_globalWork_forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
      energy generator duration)
  have hreverse := congrArg (fun μ : Measure ℝ => μ {-w})
    (map_globalReverseWork_reverseGlobalLaw
      (Gibbs.measure (Measure.count : Measure Ω) β
        (energy (Fin.last M)))
      energy generator duration)
  rw [Measure.map_apply
      (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
      (measurableSet_singleton w),
    Measure.map_apply
      (measurable_work energy fun _ => Measurable.of_discrete)
      (measurableSet_singleton w)] at hforward
  rw [Measure.map_apply
      (measurable_globalReverseWork energy duration
        fun _ => Measurable.of_discrete)
      (measurableSet_singleton (-w)),
    Measure.map_apply
      (measurable_reverseWork energy fun _ => Measurable.of_discrete)
      (measurableSet_singleton (-w))] at hreverse
  have hforwardReal := congrArg ENNReal.toReal hforward
  have hreverseReal := congrArg ENNReal.toReal hreverse
  rw [← measureReal_def, ← measureReal_def] at hforwardReal hreverseReal
  rw [show {γ | globalWork energy duration γ = w} =
      globalWork energy duration ⁻¹' {w} by ext γ; simp,
    hforwardReal,
    show {γ | globalReverseWork energy duration γ = -w} =
      globalReverseWork energy duration ⁻¹' {-w} by ext γ; simp,
    hreverseReal]
  exact crooks_work_atom_of_gibbsDetailedBalance
    β hβ energy generator duration hbalance w

/-- **Crooks relation on concatenated global charts**, derived from Gibbs
detailed balance in every protocol window. -/
theorem global_crooks_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    CrooksRelation
      (forwardGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration)
      (reverseGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M)))
        generator duration)
      (fun γ => ENNReal.ofReal (Real.exp (-β * globalWork energy duration γ)))
      (ENNReal.ofReal (Real.exp (-β *
        deltaFreeEnergy (Measure.count : Measure Ω) β energy))) := by
  let forward := forwardDrivenLaw
    (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
    generator duration
  let reverse := reverseDrivenLaw
    (Gibbs.measure (Measure.count : Measure Ω) β (energy (Fin.last M)))
    generator duration
  let q : FullPath Ω → ℝ≥0∞ :=
    fun γ => ENNReal.ofReal (Real.exp (-β * globalWork energy duration γ))
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β *
    deltaFreeEnergy (Measure.count : Measure Ω) β energy))
  have hq : Measurable q := by
    dsimp [q]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_const.mul
          (measurable_globalWork energy duration
            fun _ => Measurable.of_discrete)))
  have hwork :
      (fun γ => ENNReal.ofReal (Real.exp (-β * work energy γ))) =ᵐ[forward]
        q ∘ concatenateWindows := by
    filter_upwards
      [work_comp_concatenateWindows_ae
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        energy generator duration] with γ hγ
    simp only [q, Function.comp_apply]
    rw [hγ]
  have hmarked : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work energy γ))) c := by
    simpa [forward, reverse, c] using
      crooks_of_gibbsDetailedBalance β hβ energy generator duration hbalance
  have htransport : CrooksRelation forward reverse
      (q ∘ concatenateWindows) c := by
    unfold CrooksRelation at hmarked ⊢
    calc
      forward.withDensity (q ∘ concatenateWindows) =
          forward.withDensity
            (fun γ => ENNReal.ofReal (Real.exp (-β * work energy γ))) :=
        MeasureTheory.withDensity_congr_ae hwork.symm
      _ = c • reverse := hmarked
  simpa [forwardGlobalLaw, reverseGlobalLaw, forward, reverse, q, c] using
    (CrooksRelation.map forward reverse concatenateWindows q c
      measurable_concatenateWindows hq htransport)

/-- **Jarzynski equality on concatenated global charts.** -/
theorem global_jarzynski_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    ∫ γ, Real.exp (-β * globalWork energy duration γ)
        ∂forwardGlobalLaw
          (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
          generator duration =
      Real.exp (-β *
        deltaFreeEnergy (Measure.count : Measure Ω) β energy) := by
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure Ω) β
        (energy (Fin.last M))) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure Ω) β (energy (Fin.last M))
      (integrable_count_fintype_global
        (fun x => Real.exp (-β * energy (Fin.last M) x)))
  exact jarzynski_integral _ _ β
    (deltaFreeEnergy (Measure.count : Measure Ω) β energy)
    (globalWork energy duration)
    (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
    (global_crooks_of_gibbsDetailedBalance
      β hβ energy generator duration hbalance)

/-- **Average-work second law on concatenated global charts.** -/
theorem global_second_law_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : 0 < β)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    deltaFreeEnergy (Measure.count : Measure Ω) β energy ≤
      ∫ γ, globalWork energy duration γ
        ∂forwardGlobalLaw
          (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
          generator duration := by
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure Ω) β (energy 0)) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure Ω) β (energy 0)
      (integrable_count_fintype_global
        (fun x => Real.exp (-β * energy 0 x)))
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure Ω) β
        (energy (Fin.last M))) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure Ω) β (energy (Fin.last M))
      (integrable_count_fintype_global
        (fun x => Real.exp (-β * energy (Fin.last M) x)))
  exact second_law_of_crooks
    (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
      generator duration)
    (reverseGlobalLaw
      (Gibbs.measure (Measure.count : Measure Ω) β
        (energy (Fin.last M)))
      generator duration)
    β (deltaFreeEnergy (Measure.count : Measure Ω) β energy)
    (globalWork energy duration) hβ
    (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
    (integrable_globalWork
      (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
      energy generator duration)
    (global_crooks_of_gibbsDetailedBalance
      β hβ.ne' energy generator duration hbalance)

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
