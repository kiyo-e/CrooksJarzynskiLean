/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenGlobalCrooks
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Relative entropy of forward and reverse driven path laws

The global Crooks density identifies the log-likelihood ratio of the forward
law with the dissipated work.  Integrating that identity gives the equality
between mean entropy production and Kullback--Leibler divergence.
-/

open MeasureTheory ProbabilityTheory Function InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [DecidableEq Ω] [Nonempty Ω]

omit [DecidableEq Ω] [Nonempty Ω] in
private theorem integrable_count_fintype_kl (f : Ω → ℝ) :
    Integrable f (Measure.count : Measure Ω) := by
  apply Integrable.of_bound
    (Measurable.of_discrete : Measurable f).aestronglyMeasurable
    (∑ x : Ω, ‖f x‖)
  filter_upwards [] with x
  exact Finset.single_le_sum (f := fun y : Ω => ‖f y‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ x)

/-- A strictly positive exponential density has the expected
log-likelihood ratio against its base measure. -/
private theorem llr_withDensity_exp_neg_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (β : ℝ) (f : α → ℝ) (hf : Measurable f) :
    llr μ (μ.withDensity fun x => ENNReal.ofReal (Real.exp (-β * f x))) =ᵐ[μ]
      fun x => β * f x := by
  let q : α → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-β * f x))
  have hq : Measurable q :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hf))
  have hq0 : ∀ᵐ x ∂μ, q x ≠ 0 := ae_of_all _ fun x => by
    simp [q, Real.exp_pos]
  have hqtop : ∀ᵐ x ∂μ, q x ≠ ∞ := ae_of_all _ fun x => by simp [q]
  have hrn := Measure.rnDeriv_withDensity_right μ μ
    hq.aemeasurable hq0 hqtop
  filter_upwards [hrn, μ.rnDeriv_self] with x hrn hself
  rw [llr, hrn, hself]
  simp only [mul_one, q]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_inv, Real.log_exp]
  ring

/-- The aligned reverse global law is the forward law tilted by the negative
dissipated work. -/
theorem reverseGlobalLaw_eq_forwardGlobalLaw_withDensity
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    reverseGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M))) generator duration =
      (forwardGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).withDensity
          (fun γ => ENNReal.ofReal (Real.exp (-β *
            (globalWork energy duration γ -
              deltaFreeEnergy (Measure.count : Measure Ω) β energy)))) := by
  let forward := forwardGlobalLaw
    (Gibbs.measure (Measure.count : Measure Ω) β (energy 0)) generator duration
  let reverse := reverseGlobalLaw
    (Gibbs.measure (Measure.count : Measure Ω) β (energy (Fin.last M)))
      generator duration
  let q : FullPath Ω → ℝ≥0∞ := fun γ =>
    ENNReal.ofReal (Real.exp (-β * globalWork energy duration γ))
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β *
    deltaFreeEnergy (Measure.count : Measure Ω) β energy))
  let r : FullPath Ω → ℝ≥0∞ := fun γ => ENNReal.ofReal (Real.exp (-β *
    (globalWork energy duration γ -
      deltaFreeEnergy (Measure.count : Measure Ω) β energy)))
  have hq : Measurable q := by
    dsimp [q]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_const.mul
          (measurable_globalWork energy duration fun _ => Measurable.of_discrete)))
  have hc0 : c ≠ 0 := by simp [c, Real.exp_pos]
  have hctop : c ≠ ∞ := by simp [c]
  have hcrooks : forward.withDensity q = c • reverse := by
    simpa [CrooksRelation, forward, reverse, q, c] using
      global_crooks_of_gibbsDetailedBalance
        β hβ energy generator duration hbalance
  have hrq : c⁻¹ • q = r := by
    funext γ
    dsimp [q, c, r]
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_neg, ← Real.exp_add]
    congr 2
    ring
  change reverse = forward.withDensity r
  calc
    reverse = c⁻¹ • (c • reverse) := by
      rw [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
    _ = c⁻¹ • forward.withDensity q := by rw [hcrooks]
    _ = forward.withDensity (c⁻¹ • q) := by
      rw [MeasureTheory.withDensity_smul c⁻¹ hq]
    _ = forward.withDensity r := by rw [hrq]

/-- The forward-to-aligned-reverse log-likelihood ratio is the dimensionless
dissipated work. -/
theorem llr_forwardGlobalLaw_reverseGlobalLaw
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    llr
      (forwardGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration)
      (reverseGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M))) generator duration) =ᵐ[
        forwardGlobalLaw
          (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
          generator duration]
      fun γ => β * (globalWork energy duration γ -
        deltaFreeEnergy (Measure.count : Measure Ω) β energy) := by
  let initial := Gibbs.measure (Measure.count : Measure Ω) β (energy 0)
  letI : IsProbabilityMeasure initial :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure Ω) β (energy 0)
      (integrable_count_fintype_kl
        (fun x => Real.exp (-β * energy 0 x)))
  rw [reverseGlobalLaw_eq_forwardGlobalLaw_withDensity
    β hβ energy generator duration hbalance]
  apply llr_withDensity_exp_neg_mul
  exact (measurable_globalWork energy duration fun _ => Measurable.of_discrete).sub
    measurable_const

/-- **Mean entropy production equals path-space relative entropy.** -/
theorem klDiv_forwardGlobalLaw_reverseGlobalLaw
    {M : ℕ} (β : ℝ) (hβ : 0 < β)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    klDiv
      (forwardGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration)
      (reverseGlobalLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M))) generator duration) =
      ENNReal.ofReal (β *
        (∫ γ, globalWork energy duration γ
          ∂forwardGlobalLaw
            (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
            generator duration -
          deltaFreeEnergy (Measure.count : Measure Ω) β energy)) := by
  let initial := Gibbs.measure (Measure.count : Measure Ω) β (energy 0)
  let final := Gibbs.measure (Measure.count : Measure Ω) β (energy (Fin.last M))
  let forward := forwardGlobalLaw initial generator duration
  let reverse := reverseGlobalLaw final generator duration
  change klDiv forward reverse = ENNReal.ofReal (β *
    (∫ γ, globalWork energy duration γ ∂forward -
      deltaFreeEnergy (Measure.count : Measure Ω) β energy))
  letI : IsProbabilityMeasure initial :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure Ω) β (energy 0)
      (integrable_count_fintype_kl
        (fun x => Real.exp (-β * energy 0 x)))
  letI : IsProbabilityMeasure final :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure Ω) β (energy (Fin.last M))
      (integrable_count_fintype_kl
        (fun x => Real.exp (-β * energy (Fin.last M) x)))
  have hreverseDensity := reverseGlobalLaw_eq_forwardGlobalLaw_withDensity
    β hβ.ne' energy generator duration hbalance
  change reverse = forward.withDensity
    (fun γ => ENNReal.ofReal (Real.exp (-β *
      (globalWork energy duration γ -
        deltaFreeEnergy (Measure.count : Measure Ω) β energy)))) at hreverseDensity
  have hac : forward ≪ reverse := by
    rw [hreverseDensity]
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp
          (measurable_const.mul
            ((measurable_globalWork energy duration
              fun _ => Measurable.of_discrete).sub measurable_const)))).aemeasurable
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      intro γ
      positivity
  have hwork : Integrable (globalWork energy duration) forward :=
    integrable_globalWork initial energy generator duration
  have hllr := llr_forwardGlobalLaw_reverseGlobalLaw
    β hβ.ne' energy generator duration hbalance
  have hllrInt : Integrable (llr forward reverse) forward := by
    rw [integrable_congr hllr]
    exact (hwork.sub (integrable_const _)).const_mul β
  rw [klDiv_of_ac_of_integrable hac hllrInt]
  have hforwardMass : forward.real Set.univ = 1 := by simp
  have hreverseMass : reverse.real Set.univ = 1 := by simp
  rw [show ∫ γ, llr forward reverse γ ∂forward =
      β * (∫ γ, globalWork energy duration γ ∂forward -
        deltaFreeEnergy (Measure.count : Measure Ω) β energy) by
      rw [integral_congr_ae hllr, integral_const_mul,
        integral_sub hwork (integrable_const _), integral_const]
      simp]
  rw [hforwardMass, hreverseMass]
  ring_nf

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
