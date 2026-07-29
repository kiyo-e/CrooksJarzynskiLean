/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolPhysical
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# A non-atomic real-state-space example

This module instantiates the general measurable-state-space theorem on `ℝ`.
The reference law is a non-degenerate Gaussian measure. The energy has two
spatial levels separated at the origin, and every transition independently
resamples the post-quench Gibbs law. The reference and equilibrium state laws
are genuinely non-atomic, while the work observable depends on the sampled
state.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace GaussianExample

/-- Standard Gaussian reference law on `ℝ`. -/
noncomputable def base : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 1

noncomputable instance instIsProbabilityMeasureBase : IsProbabilityMeasure base := by
  unfold base
  infer_instance

noncomputable instance instNullSingletonClassBase : NullSingletonClass base := by
  unfold base
  exact ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)

/-- The reference law is genuinely non-atomic. -/
@[simp]
theorem base_singleton (x : ℝ) : base {x} = 0 :=
  measure_singleton x

/-- A spatially varying two-level energy schedule. -/
noncomputable def energy {n : ℕ} (left right : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ → ℝ :=
  fun i x => if x ≤ 0 then left i else right i

/-- The two-level energy is measurable at every protocol time. -/
theorem measurable_energy
    {n : ℕ} (left right : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Measurable (energy left right i) := by
  unfold energy
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- The Boltzmann factor of the two-level energy is integrable under the
Gaussian reference probability measure. -/
theorem integrable_boltzmann_energy
    {n : ℕ} (left right : Fin (n + 1) → ℝ)
    (β : ℝ) (i : Fin (n + 1)) :
    Integrable (fun x : ℝ => Real.exp (-β * energy left right i x)) base := by
  let s : Set ℝ := Set.Iic 0
  have hs : MeasurableSet s := measurableSet_Iic
  have hleft : Integrable
      (fun _ : ℝ => Real.exp (-β * left i)) base :=
    integrable_const (μ := base) _
  have hright : Integrable
      (fun _ : ℝ => Real.exp (-β * right i)) base :=
    integrable_const (μ := base) _
  have hsum := (hleft.indicator hs).add
    (hright.indicator hs.compl)
  have hfun :
      (fun x : ℝ => Real.exp (-β * energy left right i x)) =
        (s.indicator (fun _ : ℝ => Real.exp (-β * left i)) +
          sᶜ.indicator (fun _ : ℝ => Real.exp (-β * right i))) := by
    funext x
    by_cases hx : x ≤ 0 <;> simp [energy, s, hx, Set.indicator]
  rw [hfun]
  exact hsum

/-- Every Gibbs equilibrium in the example remains non-atomic. -/
noncomputable instance instNullSingletonClassEquilibrium
    {n : ℕ} (β : ℝ) (left right : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    NullSingletonClass (Gibbs.measure base β (energy left right i)) := by
  unfold Gibbs.measure Measure.tilted
  infer_instance

/-- No equilibrium state has positive singleton mass. -/
@[simp]
theorem equilibrium_singleton
    {n : ℕ} (β : ℝ) (left right : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (x : ℝ) :
    Gibbs.measure base β (energy left right i) {x} = 0 :=
  measure_singleton x

/-- Independently resample the Gibbs equilibrium associated with one time
slice. -/
noncomputable def equilibriumKernel
    {n : ℕ} (β : ℝ) (left right : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ProbabilityTheory.Kernel ℝ ℝ :=
  ProbabilityTheory.Kernel.const ℝ
    (Gibbs.measure base β (energy left right i))

/-- Independent equilibrium resampling is a Markov kernel. -/
theorem isMarkovKernel_equilibriumKernel
    {n : ℕ} (β : ℝ) (left right : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    IsMarkovKernel (equilibriumKernel β left right i) := by
  letI : IsProbabilityMeasure
      (Gibbs.measure base β (energy left right i)) :=
    Gibbs.isProbabilityMeasure_measure base β (energy left right i)
      (integrable_boltzmann_energy left right β i)
  unfold equilibriumKernel
  infer_instance

/-- Independent resampling from the post-quench Gibbs law satisfies the
measure-level local balance equation by symmetry of a product measure. -/
theorem localBalance
    {n : ℕ} (β : ℝ) (left right : Fin (n + 1) → ℝ) (i : Fin n) :
    Gibbs.measure base β (energy left right i.succ) ⊗ₘ
        equilibriumKernel β left right i.succ =
      (Gibbs.measure base β (energy left right i.succ) ⊗ₘ
        equilibriumKernel β left right i.succ).map Prod.swap := by
  letI : IsProbabilityMeasure
      (Gibbs.measure base β (energy left right i.succ)) :=
    Gibbs.isProbabilityMeasure_measure base β (energy left right i.succ)
      (integrable_boltzmann_energy left right β i.succ)
  simpa [equilibriumKernel] using
    (Measure.prod_swap
      (μ := Gibbs.measure base β (energy left right i.succ))
      (ν := Gibbs.measure base β (energy left right i.succ))).symm

/-- A concrete non-atomic specialization of the physical multi-step Crooks
relation. -/
theorem multiStep_crooks
    {n : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (left right : Fin (n + 1) → ℝ) :
    CrooksRelation
      (Markov.chronologicalForwardPathMeasure
        (Gibbs.measure base β (energy left right 0))
        (fun i : Fin n => equilibriumKernel β left right i.succ))
      (Markov.timeReversedReversePathMeasure
        (Gibbs.measure base β (energy left right (Fin.last n)))
        (fun i : Fin n => equilibriumKernel β left right i.succ))
      (fun γ => ENNReal.ofReal
        (Real.exp (-β * Gibbs.pathWork (energy left right) γ)))
      (ENNReal.ofReal
        (Real.exp (-β * Gibbs.deltaFreeEnergy base β (energy left right)))) := by
  let K : Fin n → ProbabilityTheory.Kernel ℝ ℝ :=
    fun i => equilibriumKernel β left right i.succ
  letI : ∀ i, IsMarkovKernel (K i) :=
    fun i => isMarkovKernel_equilibriumKernel β left right i.succ
  simpa [K] using
    (Gibbs.multiStep_crooks_physical base β hβ
      (energy left right) K K
      (fun i => measurable_energy left right i)
      (fun i => integrable_boltzmann_energy left right β i)
      (fun i => by simpa [K] using localBalance β left right i))

/-- The corresponding real-valued Jarzynski equality on the Gaussian state
space. -/
theorem multiStep_jarzynski
    {n : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (left right : Fin (n + 1) → ℝ) :
    ∫ γ, Real.exp (-β * Gibbs.pathWork (energy left right) γ)
        ∂Markov.chronologicalForwardPathMeasure
          (Gibbs.measure base β (energy left right 0))
          (fun i : Fin n => equilibriumKernel β left right i.succ) =
      Real.exp (-β * Gibbs.deltaFreeEnergy base β (energy left right)) := by
  let K : Fin n → ProbabilityTheory.Kernel ℝ ℝ :=
    fun i => equilibriumKernel β left right i.succ
  letI : ∀ i, IsMarkovKernel (K i) :=
    fun i => isMarkovKernel_equilibriumKernel β left right i.succ
  simpa [K] using
    (Gibbs.multiStep_jarzynski_integral base β hβ
      (energy left right) K K
      (fun i => measurable_energy left right i)
      (fun i => integrable_boltzmann_energy left right β i)
      (fun i => by simpa [K] using localBalance β left right i))

end GaussianExample
end MeasureProtocol
end CrooksJarzynski
