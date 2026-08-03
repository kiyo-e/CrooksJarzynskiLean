/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolMarkedMultiStep
import CrooksJarzynski.MeasureProtocolPhysical
import CrooksJarzynski.MeasureProtocolSecondLaw

/-!
# Physical Crooks relations for marked endpoint protocols

The endpoint work factors of a marked protocol telescope to the exponential of
the real work sum, while the free-energy factors telescope to the difference of
the endpoint Gibbs free energies.  The statements remain on the marked path
measures constructed by kernel composition.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Marked

universe u v

variable {Ω : Type u} {Λ : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Real work accumulated at the endpoints of all marked transitions. -/
noncomputable def endpointPathWork
    {n : ℕ} (energy : Fin (n + 1) → Ω → ℝ)
    (γ : MarkedPath Ω Λ n) : ℝ :=
  reversedEndpointSum
    (fun i x => energy i.succ x - energy i.castSucc x) γ

/-- The endpoint work observable is measurable. -/
theorem measurable_endpointPathWork
    {n : ℕ} (energy : Fin (n + 1) → Ω → ℝ)
    (henergy : ∀ i, Measurable (energy i)) :
    Measurable (endpointPathWork (Λ := Λ) energy) := by
  apply measurable_reversedEndpointSum
  intro i
  exact (henergy i.succ).sub (henergy i.castSucc)

/-- The product of Gibbs quench factors is exactly `exp (-β W)` for the
endpoint work sum. -/
theorem endpointWorkWeight_eq_exp_pathWork
    {n : ℕ} (β : ℝ) (energy : Fin (n + 1) → Ω → ℝ)
    (γ : MarkedPath Ω Λ n) :
    reversedEndpointWorkWeight
        (fun i => Gibbs.workWeight β
          (energy i.castSucc) (energy i.succ)) γ =
      ENNReal.ofReal
        (Real.exp (-β * endpointPathWork energy γ)) := by
  unfold Gibbs.workWeight endpointPathWork
  exact reversedEndpointWorkWeight_eq_exp_sum
    (Ω := Ω) (Λ := Λ) β
    (fun i x => energy i.succ x - energy i.castSucc x) γ

/-- Physical Crooks relation for a finite marked protocol with endpoint work.
The forward and reverse measures are the constructed marked path laws. -/
theorem multiStep_endpoint_crooks_physical
    {n : ℕ} (base : Measure Ω) [NeZero base]
    (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (n + 1) → Ω → ℝ)
    (forward reverse :
      Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [hForward : ∀ i, IsMarkovKernel (forward i)]
    [hReverse : ∀ i, IsMarkovKernel (reverse i)]
    (henergyMeas : ∀ i, Measurable (energy i))
    (henergyInt : ∀ i,
      Integrable (fun x => Real.exp (-β * energy i x)) base)
    (hbalance : ∀ i,
      Gibbs.measure base β (energy i.castSucc) ⊗ₘ forward i =
        (Gibbs.measure base β (energy i.castSucc) ⊗ₘ reverse i).map
          (swapEndpointsEquiv (Ω := Ω) (Λ := Λ))) :
    CrooksRelation
      (reversedForwardPathMeasure
        (Gibbs.measure base β (energy 0)) forward)
      (reversePathMeasure
        (Gibbs.measure base β (energy (Fin.last n))) reverse)
      (fun γ => ENNReal.ofReal
        (Real.exp (-β * endpointPathWork energy γ)))
      (ENNReal.ofReal
        (Real.exp (-β * Gibbs.deltaFreeEnergy base β energy))) := by
  let equilibrium : Fin (n + 1) → Measure Ω :=
    fun i => Gibbs.measure base β (energy i)
  letI : ∀ i, IsProbabilityMeasure (equilibrium i) :=
    fun i => Gibbs.isProbabilityMeasure_measure
      base β (energy i) (henergyInt i)
  have h := multiStep_endpoint_crooks
    (Ω := Ω) (Λ := Λ)
    equilibrium forward reverse
    (fun i => Gibbs.workWeight β
      (energy i.castSucc) (energy i.succ))
    (fun i => Gibbs.freeEnergyWeight base β
      (energy i.castSucc) (energy i.succ))
    (fun i => Gibbs.measurable_workWeight β
      (henergyMeas i.castSucc) (henergyMeas i.succ))
    (fun i => by simpa [equilibrium] using hbalance i)
    (fun i => Gibbs.reweight_freeEnergy base β hβ
      (energy i.castSucc) (energy i.succ)
      (henergyMeas i.castSucc) (henergyMeas i.succ)
      (henergyInt i.castSucc) (henergyInt i.succ))
  have hweight :
      reversedEndpointWorkWeight (Λ := Λ)
          (fun i => Gibbs.workWeight β
            (energy i.castSucc) (energy i.succ)) =
        (fun γ : MarkedPath Ω Λ n => ENNReal.ofReal
          (Real.exp (-β * endpointPathWork energy γ))) := by
    funext γ
    exact endpointWorkWeight_eq_exp_pathWork
      (Ω := Ω) (Λ := Λ) β energy γ
  rw [hweight,
    Gibbs.accumulatedFreeEnergyWeight_eq_exp_delta
      base β energy] at h
  simpa [equilibrium] using h

/-- Real-valued Jarzynski equality for the constructed marked forward law. -/
theorem multiStep_endpoint_jarzynski_integral
    {n : ℕ} (base : Measure Ω) [NeZero base]
    (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (n + 1) → Ω → ℝ)
    (forward reverse :
      Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [∀ i, IsMarkovKernel (forward i)]
    [∀ i, IsMarkovKernel (reverse i)]
    (henergyMeas : ∀ i, Measurable (energy i))
    (henergyInt : ∀ i,
      Integrable (fun x => Real.exp (-β * energy i x)) base)
    (hbalance : ∀ i,
      Gibbs.measure base β (energy i.castSucc) ⊗ₘ forward i =
        (Gibbs.measure base β (energy i.castSucc) ⊗ₘ reverse i).map
          (swapEndpointsEquiv (Ω := Ω) (Λ := Λ))) :
    ∫ γ, Real.exp (-β * endpointPathWork energy γ)
        ∂reversedForwardPathMeasure
          (Gibbs.measure base β (energy 0)) forward =
      Real.exp (-β * Gibbs.deltaFreeEnergy base β energy) := by
  letI : IsProbabilityMeasure
      (Gibbs.measure base β (energy (Fin.last n))) :=
    Gibbs.isProbabilityMeasure_measure
      base β (energy (Fin.last n)) (henergyInt (Fin.last n))
  exact jarzynski_integral _ _ β
    (Gibbs.deltaFreeEnergy base β energy)
    (endpointPathWork energy)
    (measurable_endpointPathWork energy henergyMeas)
    (multiStep_endpoint_crooks_physical
      (Ω := Ω) (Λ := Λ) base β hβ energy
      forward reverse henergyMeas henergyInt hbalance)

/-- Average-work second law for the constructed marked forward law. -/
theorem multiStep_endpoint_second_law
    {n : ℕ} (base : Measure Ω) [NeZero base]
    (β : ℝ) (hβ : 0 < β)
    (energy : Fin (n + 1) → Ω → ℝ)
    (forward reverse :
      Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [∀ i, IsMarkovKernel (forward i)]
    [∀ i, IsMarkovKernel (reverse i)]
    (henergyMeas : ∀ i, Measurable (energy i))
    (henergyInt : ∀ i,
      Integrable (fun x => Real.exp (-β * energy i x)) base)
    (hbalance : ∀ i,
      Gibbs.measure base β (energy i.castSucc) ⊗ₘ forward i =
        (Gibbs.measure base β (energy i.castSucc) ⊗ₘ reverse i).map
          (swapEndpointsEquiv (Ω := Ω) (Λ := Λ)))
    (hworkInt : Integrable (endpointPathWork energy)
      (reversedForwardPathMeasure
        (Gibbs.measure base β (energy 0)) forward)) :
    Gibbs.deltaFreeEnergy base β energy ≤
      ∫ γ, endpointPathWork energy γ
        ∂reversedForwardPathMeasure
          (Gibbs.measure base β (energy 0)) forward := by
  letI : IsProbabilityMeasure
      (Gibbs.measure base β (energy 0)) :=
    Gibbs.isProbabilityMeasure_measure base β (energy 0) (henergyInt 0)
  letI : IsProbabilityMeasure
      (Gibbs.measure base β (energy (Fin.last n))) :=
    Gibbs.isProbabilityMeasure_measure
      base β (energy (Fin.last n)) (henergyInt (Fin.last n))
  exact second_law_of_crooks
    (reversedForwardPathMeasure
      (Gibbs.measure base β (energy 0)) forward)
    (reversePathMeasure
      (Gibbs.measure base β (energy (Fin.last n))) reverse)
    β (Gibbs.deltaFreeEnergy base β energy)
    (endpointPathWork energy) hβ
    (measurable_endpointPathWork energy henergyMeas)
    hworkInt
    (multiStep_endpoint_crooks_physical
      (Ω := Ω) (Λ := Λ) base β hβ.ne' energy
      forward reverse henergyMeas henergyInt hbalance)

/-- For one window, the accumulated work is the terminal energy quench. -/
theorem endpointPathWork_one
    (energy : Fin 2 → Ω → ℝ)
    (γ : MarkedPath Ω Λ 1) :
    endpointPathWork energy γ = energy 1 γ.1 - energy 0 γ.1 := by
  simp [endpointPathWork, reversedEndpointSum]

end Marked
end MeasureProtocol
end CrooksJarzynski
