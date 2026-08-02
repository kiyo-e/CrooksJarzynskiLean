/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDriven

/-!
# Explicit finite-sum form of driven endpoint work

The marked-path recursion stores protocol windows in reverse chronological
order. This module reads the endpoint reached in each window and identifies the
recursive endpoint work with the ordinary finite sum over protocol indices.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The endpoint reached by the window with index `i`. The last endpoint is at
the front of the reverse-oriented carrier, while earlier endpoints are read
recursively from its continuation. -/
def endpointAt : {M : ℕ} → Path Ω M → Fin M → Ω
  | 0, _, i => Fin.elim0 i
  | _ + 1, γ, i =>
      Fin.lastCases γ.1
        (fun j => endpointAt (γ.2.1.1, γ.2.2) j) i

@[simp]
theorem endpointAt_castSucc {M : ℕ} (γ : Path Ω (M + 1)) (i : Fin M) :
    endpointAt γ i.castSucc = endpointAt (γ.2.1.1, γ.2.2) i := by
  simp [endpointAt]

@[simp]
theorem endpointAt_last {M : ℕ} (γ : Path Ω (M + 1)) :
    endpointAt γ (Fin.last M) = γ.1 := by
  simp [endpointAt]

/-- The recursive endpoint sum used by the marked-path construction is the
ordinary finite sum over the endpoint reached in every window. -/
theorem reversedEndpointSum_eq_sum
    {M : ℕ} (q : Fin M → Ω → ℝ) (γ : Path Ω M) :
    Marked.reversedEndpointSum q γ =
      ∑ i : Fin M, q i (endpointAt γ i) := by
  induction M with
  | zero =>
      simp [Marked.reversedEndpointSum]
  | succ M ih =>
      rw [Fin.sum_univ_castSucc]
      change
        Marked.reversedEndpointSum (fun i => q i.castSucc)
              (γ.2.1.1, γ.2.2) +
            q (Fin.last M) γ.1 =
          (∑ i : Fin M, q i.castSucc (endpointAt γ i.castSucc)) +
            q (Fin.last M) (endpointAt γ (Fin.last M))
      rw [ih (fun i => q i.castSucc) (γ.2.1.1, γ.2.2)]
      simp

/-- The driven work observable has the explicit transition-then-quench finite
sum over the endpoints of the protocol windows. -/
theorem work_eq_sum
    {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ) (γ : Path Ω M) :
    work energy γ =
      ∑ i : Fin M,
        (energy i.succ (endpointAt γ i) -
          energy i.castSucc (endpointAt γ i)) := by
  simpa [work, Marked.endpointPathWork] using
    (reversedEndpointSum_eq_sum
      (q := fun i x => energy i.succ x - energy i.castSucc x) γ)

variable [Fintype Ω]

/-- A uniform finite bound for endpoint work over all driven paths. -/
noncomputable def workBound
    {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ x : Ω,
    ‖energy i.succ x - energy i.castSucc x‖

/-- Driven work is uniformly bounded because both the protocol and the state
space are finite. -/
theorem norm_work_le
    {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ) (γ : Path Ω M) :
    ‖work energy γ‖ ≤ workBound energy := by
  rw [work_eq_sum]
  calc
    ‖∑ i : Fin M,
        (energy i.succ (endpointAt γ i) -
          energy i.castSucc (endpointAt γ i))‖ ≤
        ∑ i : Fin M,
          ‖energy i.succ (endpointAt γ i) -
            energy i.castSucc (endpointAt γ i)‖ :=
      norm_sum_le _ _
    _ ≤ workBound energy := by
      unfold workBound
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum
        (f := fun x : Ω =>
          ‖energy i.succ x - energy i.castSucc x‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_univ (endpointAt γ i))

variable [DecidableEq Ω] [MeasurableSingletonClass Ω]

/-- Work is automatically integrable under every constructed finite-state
forward driven law with a probability initial state. -/
theorem integrable_work
    {M : ℕ} (initial : Measure Ω) [IsProbabilityMeasure initial]
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    Integrable (work energy)
      (forwardDrivenLaw initial generator duration) := by
  letI : IsProbabilityMeasure
      (forwardDrivenLaw initial generator duration) := by
    infer_instance
  apply Integrable.of_bound
    (measurable_work energy
      (fun _ => Measurable.of_discrete)).aestronglyMeasurable
    (workBound energy)
  exact ae_of_all _ fun γ => norm_work_le energy γ

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
