/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatLaw
import CrooksJarzynski.ContinuousTimeJumpDrivenConcat

/-!
# Global laws for driven continuous-time jump protocols

This module pushes the marked driven path laws through the chronological
concatenation of their window charts.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Concatenating all marked window charts is measurable. -/
@[fun_prop]
theorem measurable_concatenateWindows :
    ∀ {M : ℕ}, Measurable (concatenateWindows : Path Ω M → FullPath Ω)
  | 0 => by
      simp only [concatenateWindows]
      exact (FullPath.measurable_mk 0).comp (by fun_prop)
  | M + 1 => by
      simp only [concatenateWindows]
      exact FullPath.measurable_concat_prod.comp
        ((measurable_concatenateWindows.comp (by fun_prop)).prodMk (by fun_prop))

variable [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]

/-- The forward law of the single concatenated real-time chart. -/
noncomputable def forwardGlobalLaw {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) : Measure (FullPath Ω) :=
  (forwardDrivenLaw initial generator duration).map concatenateWindows

noncomputable instance instIsProbabilityMeasureForwardGlobalLaw
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (forwardGlobalLaw initial generator duration) := by
  unfold forwardGlobalLaw
  exact Measure.isProbabilityMeasure_map measurable_concatenateWindows.aemeasurable

/-- The reverse-experiment law on a forward-chronology concatenated chart. -/
noncomputable def reverseGlobalLaw {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) : Measure (FullPath Ω) :=
  (reverseDrivenLaw final generator duration).map concatenateWindows

noncomputable instance instIsProbabilityMeasureReverseGlobalLaw
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) [IsProbabilityMeasure final] :
    IsProbabilityMeasure (reverseGlobalLaw final generator duration) := by
  unfold reverseGlobalLaw
  exact Measure.isProbabilityMeasure_map measurable_concatenateWindows.aemeasurable

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
private theorem measurableSet_windowsTotal
    {M : ℕ} (duration : Fin M → NNReal) :
    MeasurableSet {γ : Path Ω M |
      ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i} := by
  rw [show {γ : Path Ω M |
      ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i} =
      ⋂ i, (fun γ => windowAt (Ω := Ω) (M := M) γ i) ⁻¹'
        {w | FullPath.totalHoldingTime w = duration i} by ext; simp]
  exact MeasurableSet.iInter fun i =>
    ((FullPath.measurable_totalHoldingTime.eq_const (duration i)).setOf).preimage
      (measurable_windowAt i)

private theorem forwardWindowKernel_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ p ∂G.forwardWindowKernel T x,
      FullPath.totalHoldingTime p.2 = T := by
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T x),
    FullPath.totalHoldingTime p.2 = T
  refine (ae_map_iff
    (FullPath.measurable_terminalState.prodMk measurable_id).aemeasurable
    ((FullPath.measurable_totalHoldingTime.comp measurable_snd).eq_const T).setOf).2 ?_
  filter_upwards [G.pathLawFrom_ae_totalHoldingTime T x] with γ hγ
  exact hγ

private theorem forwardDrivenLaw_ae_windowsTotal :
    ∀ {M : ℕ} (initial : Measure Ω)
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal),
      ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
        ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i
  | 0, initial, generator, duration => by simp
  | M + 1, initial, generator, duration => by
      have hpast := forwardDrivenLaw_ae_windowsTotal initial
        (fun i : Fin M => generator i.castSucc)
        (fun i : Fin M => duration i.castSucc)
      simp only [forwardDrivenLaw, Marked.reversedForwardPathMeasure]
      let prepend := Marked.prependEquiv (Ω := Ω) (Λ := FullPath Ω) M
      have hset := measurableSet_windowsTotal (Ω := Ω) duration
      refine (ae_map_iff prepend.measurable.aemeasurable hset).2 ?_
      apply Measure.ae_compProd_of_ae_ae
      · exact hset.preimage prepend.measurable
      · filter_upwards [hpast] with past hpast
        filter_upwards
          [forwardWindowKernel_ae_totalHoldingTime (generator (Fin.last M))
            (duration (Fin.last M)) past.1] with window hwindow
        change ∀ i, FullPath.totalHoldingTime
          (windowAt ((window.1,
            (((past.1, window.2), past.2) :
              Marked.MarkedContinuation Ω (FullPath Ω) (M + 1))) :
                Path Ω (M + 1)) i) = duration i
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hwindow
        · simpa using hpast j

/-- The forward global law is concentrated on valid concatenated charts. -/
theorem forwardGlobalLaw_ae_isValid
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardGlobalLaw initial generator duration,
      FullPath.IsValid (∑ i, duration i) γ := by
  unfold forwardGlobalLaw
  rw [ae_map_iff measurable_concatenateWindows.aemeasurable
    (FullPath.measurableSet_isValid (∑ i, duration i))]
  filter_upwards
    [forwardDrivenLaw_ae_isProtocolValid initial generator duration,
      forwardDrivenLaw_ae_windowsTotal initial generator duration] with γ hvalid htotal
  exact isValid_concatenateWindows duration γ hvalid.2
    (fun i => (htotal i).le)

/-- The forward global chart exactly fills the sum of all window durations. -/
theorem forwardGlobalLaw_ae_totalHoldingTime
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardGlobalLaw initial generator duration,
      FullPath.totalHoldingTime γ = ∑ i, duration i := by
  unfold forwardGlobalLaw
  rw [ae_map_iff measurable_concatenateWindows.aemeasurable
    (FullPath.measurable_totalHoldingTime.eq_const (∑ i, duration i)).setOf]
  filter_upwards
    [forwardDrivenLaw_ae_windowsTotal initial generator duration] with γ htotal
  rw [totalHoldingTime_concatenateWindows]
  exact Finset.sum_congr rfl fun i _ => htotal i

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
