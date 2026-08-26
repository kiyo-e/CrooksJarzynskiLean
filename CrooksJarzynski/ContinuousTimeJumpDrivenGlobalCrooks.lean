/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenGlobalLaw
import CrooksJarzynski.ContinuousTimeJumpDrivenThreeStateTwoWindow

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
  let initial := Gibbs.measure (Measure.count : Measure Ω) β (energy 0)
  let forward := forwardDrivenLaw initial generator duration
  calc
    ∫ γ, Real.exp (-β * globalWork energy duration γ)
        ∂forwardGlobalLaw initial generator duration =
        ∫ γ, Real.exp (-β *
          globalWork energy duration (concatenateWindows γ)) ∂forward := by
      unfold forwardGlobalLaw
      exact MeasureTheory.integral_map measurable_concatenateWindows.aemeasurable
        ((Real.measurable_exp.comp
          (measurable_const.mul
            (measurable_globalWork energy duration
              fun _ => Measurable.of_discrete))).aestronglyMeasurable)
    _ = ∫ γ, Real.exp (-β * work energy γ) ∂forward := by
      apply integral_congr_ae
      filter_upwards
        [work_comp_concatenateWindows_ae initial energy generator duration] with γ hγ
      rw [hγ]
    _ = Real.exp (-β *
        deltaFreeEnergy (Measure.count : Measure Ω) β energy) := by
      simpa [initial, forward] using
        jarzynski_of_gibbsDetailedBalance β hβ energy generator duration hbalance

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
  let initial := Gibbs.measure (Measure.count : Measure Ω) β (energy 0)
  let forward := forwardDrivenLaw initial generator duration
  calc
    deltaFreeEnergy (Measure.count : Measure Ω) β energy ≤
        ∫ γ, work energy γ ∂forward := by
      simpa [initial, forward] using
        second_law_of_gibbsDetailedBalance β hβ energy generator duration hbalance
    _ = ∫ γ, globalWork energy duration (concatenateWindows γ) ∂forward := by
      apply integral_congr_ae
      filter_upwards
        [work_comp_concatenateWindows_ae
          initial energy generator duration] with γ hγ
      exact hγ.symm
    _ = ∫ γ, globalWork energy duration γ
        ∂forwardGlobalLaw initial generator duration := by
      unfold forwardGlobalLaw
      exact (MeasureTheory.integral_map
        measurable_concatenateWindows.aemeasurable
        (measurable_globalWork energy duration
          fun _ => Measurable.of_discrete).aestronglyMeasurable).symm

namespace ThreeStateTwoWindow

/-- The global-chart work distribution retains the positive atom at zero. -/
theorem global_work_zero_atom_pos (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    0 < (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration) {γ | globalWork energy duration γ = 0} := by
  have hmap := map_globalWork_forwardGlobalLaw
    (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
    energy generator duration
  have hmass := congrArg (fun μ : Measure ℝ => μ {0}) hmap
  rw [Measure.map_apply
      (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
      (measurableSet_singleton (0 : ℝ)),
    Measure.map_apply
      (measurable_work energy fun _ => Measurable.of_discrete)
      (measurableSet_singleton (0 : ℝ))] at hmass
  have hmass' : (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration) {γ | globalWork energy duration γ = 0} =
        (forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
          generator duration) {γ | work energy γ = 0} := by
    rw [show {γ | globalWork energy duration γ = 0} =
        globalWork energy duration ⁻¹' {0} by ext γ; simp,
      show {γ | work energy γ = 0} = work energy ⁻¹' {0} by ext γ; simp]
    exact hmass
  rw [hmass']
  exact work_zero_atom_pos duration hduration

/-- The global-chart work distribution retains the positive atom at
`log 2`. -/
theorem global_work_log_two_atom_pos (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    0 < (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration)
        {γ | globalWork energy duration γ = Real.log 2} := by
  have hmap := map_globalWork_forwardGlobalLaw
    (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
    energy generator duration
  have hmass := congrArg (fun μ : Measure ℝ => μ {Real.log 2}) hmap
  rw [Measure.map_apply
      (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
      (measurableSet_singleton (Real.log 2)),
    Measure.map_apply
      (measurable_work energy fun _ => Measurable.of_discrete)
      (measurableSet_singleton (Real.log 2))] at hmass
  have hmass' : (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration)
        {γ | globalWork energy duration γ = Real.log 2} =
        (forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
          generator duration) {γ | work energy γ = Real.log 2} := by
    rw [show {γ | globalWork energy duration γ = Real.log 2} =
        globalWork energy duration ⁻¹' {Real.log 2} by ext γ; simp,
      show {γ | work energy γ = Real.log 2} =
        work energy ⁻¹' {Real.log 2} by ext γ; simp]
    exact hmass
  rw [hmass']
  exact work_log_two_atom_pos duration hduration

end ThreeStateTwoWindow
end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
