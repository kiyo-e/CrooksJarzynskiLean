/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolFiniteCrooks
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Gibbs specialization on general measurable state spaces

This module constructs canonical Gibbs measures from an arbitrary reference
measure and a measurable energy function. It proves the equilibrium
reweighting identity required by the general-state-space Crooks theorem, first
in terms of partition-function ratios and then in the usual free-energy form.
The result is subsequently substituted into the finite-horizon Crooks theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Gibbs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The partition function of an energy landscape relative to a reference
measure. -/
noncomputable def partitionFunction
    (base : Measure Ω) (β : ℝ) (energy : Ω → ℝ) : ℝ :=
  ∫ x, Real.exp (-β * energy x) ∂base

/-- The Helmholtz free energy associated with `partitionFunction`. -/
noncomputable def freeEnergy
    (base : Measure Ω) (β : ℝ) (energy : Ω → ℝ) : ℝ :=
  -Real.log (partitionFunction base β energy) / β

/-- The canonical Gibbs measure, implemented as Mathlib's exponential tilt of
the reference measure. -/
noncomputable def measure
    (base : Measure Ω) (β : ℝ) (energy : Ω → ℝ) : Measure Ω :=
  base.tilted (fun x => -β * energy x)

/-- The exponential work factor for an instantaneous energy quench. -/
noncomputable def workWeight
    (β : ℝ) (initial final : Ω → ℝ) (x : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * (final x - initial x)))

/-- The equilibrium factor written as a partition-function ratio. -/
noncomputable def partitionRatio
    (base : Measure Ω) (β : ℝ) (initial final : Ω → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (partitionFunction base β final / partitionFunction base β initial)

/-- The equilibrium factor written in the standard free-energy form. -/
noncomputable def freeEnergyWeight
    (base : Measure Ω) (β : ℝ) (initial final : Ω → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-β * (freeEnergy base β final - freeEnergy base β initial)))

/-- A Gibbs measure is a probability measure whenever the Boltzmann factor is
integrable and the reference measure is nonzero. -/
theorem isProbabilityMeasure_measure
    (base : Measure Ω) [NeZero base] (β : ℝ) (energy : Ω → ℝ)
    (henergy : Integrable (fun x => Real.exp (-β * energy x)) base) :
    IsProbabilityMeasure (measure base β energy) := by
  unfold measure
  exact isProbabilityMeasure_tilted henergy

/-- Measurability of the exponential work factor. -/
theorem measurable_workWeight
    (β : ℝ) {initial final : Ω → ℝ}
    (hinitial : Measurable initial) (hfinal : Measurable final) :
    Measurable (workWeight β initial final) := by
  unfold workWeight
  fun_prop

/-- Exponentiating a free-energy difference gives the corresponding
partition-function ratio. -/
theorem exp_neg_beta_mul_freeEnergy_sub
    (base : Measure Ω) [NeZero base] (β : ℝ) (hβ : β ≠ 0)
    (initial final : Ω → ℝ)
    (hinitial : Integrable (fun x => Real.exp (-β * initial x)) base)
    (hfinal : Integrable (fun x => Real.exp (-β * final x)) base) :
    Real.exp (-β * (freeEnergy base β final - freeEnergy base β initial)) =
      partitionFunction base β final / partitionFunction base β initial := by
  have hZinitial : 0 < partitionFunction base β initial := by
    exact integral_exp_pos hinitial
  have hZfinal : 0 < partitionFunction base β final := by
    exact integral_exp_pos hfinal
  have harg :
      -β * (freeEnergy base β final - freeEnergy base β initial) =
        Real.log (partitionFunction base β final) -
          Real.log (partitionFunction base β initial) := by
    unfold freeEnergy
    field_simp [hβ]
    ring
  rw [harg, Real.exp_sub, Real.exp_log hZfinal,
    Real.exp_log hZinitial]

/-- Gibbs reweighting under an energy quench, expressed using the ratio of
partition functions. -/
theorem reweight_partitionRatio
    (base : Measure Ω) [NeZero base] (β : ℝ)
    (initial final : Ω → ℝ)
    (hinitialMeas : Measurable initial) (hfinalMeas : Measurable final)
    (hinitial : Integrable (fun x => Real.exp (-β * initial x)) base)
    (hfinal : Integrable (fun x => Real.exp (-β * final x)) base) :
    (measure base β initial).withDensity (workWeight β initial final) =
      partitionRatio base β initial final • measure base β final := by
  have hZinitial : 0 < partitionFunction base β initial := by
    exact integral_exp_pos hinitial
  have hZfinal : 0 < partitionFunction base β final := by
    exact integral_exp_pos hfinal
  have hdinitial : Measurable
      (fun x => ENNReal.ofReal
        (Real.exp (-β * initial x) / partitionFunction base β initial)) := by
    fun_prop
  have hdfinal : Measurable
      (fun x => ENNReal.ofReal
        (Real.exp (-β * final x) / partitionFunction base β final)) := by
    fun_prop
  have hwork : Measurable (workWeight β initial final) :=
    measurable_workWeight β hinitialMeas hfinalMeas
  unfold measure Measure.tilted partitionRatio partitionFunction
  rw [← withDensity_mul base hdinitial hwork,
    ← withDensity_smul base
      (ENNReal.ofReal
        ((∫ x, Real.exp (-β * final x) ∂base) /
          ∫ x, Real.exp (-β * initial x) ∂base)) hdfinal]
  apply withDensity_congr_ae
  filter_upwards with x
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, workWeight]
  have hexp :
      Real.exp (-β * initial x) *
          Real.exp (-β * (final x - initial x)) =
        Real.exp (-β * final x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreal :
      (Real.exp (-β * initial x) /
          ∫ y, Real.exp (-β * initial y) ∂base) *
          Real.exp (-β * (final x - initial x)) =
        ((∫ y, Real.exp (-β * final y) ∂base) /
            ∫ y, Real.exp (-β * initial y) ∂base) *
          (Real.exp (-β * final x) /
            ∫ y, Real.exp (-β * final y) ∂base) := by
    rw [div_mul_eq_mul_div, hexp]
    field_simp [hZinitial.ne', hZfinal.ne']
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), hreal]

/-- Gibbs reweighting in the standard free-energy form. -/
theorem reweight_freeEnergy
    (base : Measure Ω) [NeZero base] (β : ℝ) (hβ : β ≠ 0)
    (initial final : Ω → ℝ)
    (hinitialMeas : Measurable initial) (hfinalMeas : Measurable final)
    (hinitial : Integrable (fun x => Real.exp (-β * initial x)) base)
    (hfinal : Integrable (fun x => Real.exp (-β * final x)) base) :
    (measure base β initial).withDensity (workWeight β initial final) =
      freeEnergyWeight base β initial final • measure base β final := by
  rw [freeEnergyWeight,
    exp_neg_beta_mul_freeEnergy_sub base β hβ initial final hinitial hfinal]
  exact reweight_partitionRatio base β initial final
    hinitialMeas hfinalMeas hinitial hfinal

/-- The finite-horizon Crooks relation specialized to Gibbs equilibrium
measures constructed from a common reference measure. -/
theorem multiStep_crooks
    {n : ℕ} (base : Measure Ω) [NeZero base]
    (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (n + 1) → Ω → ℝ)
    (forward reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [hForward : ∀ i, IsMarkovKernel (forward i)]
    [hReverse : ∀ i, IsMarkovKernel (reverse i)]
    (henergyMeas : ∀ i, Measurable (energy i))
    (henergyInt : ∀ i,
      Integrable (fun x => Real.exp (-β * energy i x)) base)
    (hbalance : ∀ i,
      measure base β (energy i.succ) ⊗ₘ forward i =
        (measure base β (energy i.succ) ⊗ₘ reverse i).map Prod.swap) :
    CrooksRelation
      (Markov.reversedForwardPathMeasure (measure base β (energy 0)) forward)
      (Markov.reversePathMeasure (measure base β (energy (Fin.last n))) reverse)
      (Markov.reversedWorkWeight
        (fun i => workWeight β (energy i.castSucc) (energy i.succ)))
      (Markov.accumulatedFreeEnergyWeight
        (fun i => freeEnergyWeight base β
          (energy i.castSucc) (energy i.succ))) := by
  let equilibrium : Fin (n + 1) → Measure Ω :=
    fun i => measure base β (energy i)
  letI : ∀ i, IsProbabilityMeasure (equilibrium i) :=
    fun i => isProbabilityMeasure_measure base β (energy i) (henergyInt i)
  simpa [equilibrium] using
    (Markov.multiStep_crooks equilibrium forward reverse
      (fun i => workWeight β (energy i.castSucc) (energy i.succ))
      (fun i => freeEnergyWeight base β
        (energy i.castSucc) (energy i.succ))
      (fun i => measurable_workWeight β
        (henergyMeas i.castSucc) (henergyMeas i.succ))
      (fun i => reweight_freeEnergy base β hβ
        (energy i.castSucc) (energy i.succ)
        (henergyMeas i.castSucc) (henergyMeas i.succ)
        (henergyInt i.castSucc) (henergyInt i.succ))
      (fun i => by simpa [equilibrium] using hbalance i))

/-- The finite-horizon Jarzynski equality for Gibbs equilibrium measures on an
arbitrary measurable state space. -/
theorem multiStep_jarzynski
    {n : ℕ} (base : Measure Ω) [NeZero base]
    (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (n + 1) → Ω → ℝ)
    (forward reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [∀ i, IsMarkovKernel (forward i)]
    [∀ i, IsMarkovKernel (reverse i)]
    (henergyMeas : ∀ i, Measurable (energy i))
    (henergyInt : ∀ i,
      Integrable (fun x => Real.exp (-β * energy i x)) base)
    (hbalance : ∀ i,
      measure base β (energy i.succ) ⊗ₘ forward i =
        (measure base β (energy i.succ) ⊗ₘ reverse i).map Prod.swap) :
    ∫⁻ γ,
        Markov.reversedWorkWeight
          (fun i => workWeight β (energy i.castSucc) (energy i.succ)) γ
      ∂Markov.reversedForwardPathMeasure (measure base β (energy 0)) forward =
      Markov.accumulatedFreeEnergyWeight
        (fun i => freeEnergyWeight base β
          (energy i.castSucc) (energy i.succ)) := by
  let equilibrium : Fin (n + 1) → Measure Ω :=
    fun i => measure base β (energy i)
  letI : ∀ i, IsProbabilityMeasure (equilibrium i) :=
    fun i => isProbabilityMeasure_measure base β (energy i) (henergyInt i)
  exact Markov.multiStep_jarzynski equilibrium forward reverse
    (fun i => workWeight β (energy i.castSucc) (energy i.succ))
    (fun i => freeEnergyWeight base β
      (energy i.castSucc) (energy i.succ))
    (fun i => measurable_workWeight β
      (henergyMeas i.castSucc) (henergyMeas i.succ))
    (fun i => reweight_freeEnergy base β hβ
      (energy i.castSucc) (energy i.succ)
      (henergyMeas i.castSucc) (henergyMeas i.succ)
      (henergyInt i.castSucc) (henergyInt i.succ))
    (fun i => by simpa [equilibrium] using hbalance i)

end Gibbs
end MeasureProtocol
end CrooksJarzynski
