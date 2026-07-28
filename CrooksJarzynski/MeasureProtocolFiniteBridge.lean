/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolPhysical
import CrooksJarzynski.MathlibBridge

/-!
# Finite-state specialization of the measure-theoretic theorem

This module proves that the original finite distributions, kernels, and local
balance equations instantiate the general measure-theoretic API. It therefore
connects the legacy finite protocol to the new finite-horizon theorem rather
than merely exposing an unrelated kernel conversion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski

universe u

namespace MathlibBridge

variable {Ω : Type u} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The singleton mass of a finite measure–kernel composition is the original
joint probability. -/
theorem compProd_toKernel_singleton
    (μ : FiniteDistribution Ω) (K : CrooksJarzynski.Kernel Ω)
    (x y : Ω) :
    (μ.toMeasure ⊗ₘ toKernel K) {(x, y)} =
      ENNReal.ofReal (μ x * K x y) := by
  rw [← singleton_prod_singleton]
  rw [Measure.compProd_apply_prod (measurableSet_singleton x)
    (measurableSet_singleton y)]
  rw [lintegral_singleton]
  rw [toKernel_singleton, FiniteDistribution.toMeasure_singleton]
  rw [← ENNReal.ofReal_mul ((K x).nonneg y)]
  congr 1
  ring

/-- A pointwise finite detailed-balance identity gives the measure-level local
balance equation used by the general theorem. -/
theorem localBalance_toMeasure
    (μ : FiniteDistribution Ω)
    (forward reverse : CrooksJarzynski.Kernel Ω)
    (hbalance : ∀ x y,
      μ x * forward x y = μ y * reverse y x) :
    μ.toMeasure ⊗ₘ toKernel forward =
      (μ.toMeasure ⊗ₘ toKernel reverse).map Prod.swap := by
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [compProd_toKernel_singleton]
  rw [Measure.map_apply measurable_swap (measurableSet_singleton (x, y))]
  have hpre : Prod.swap ⁻¹' ({(x, y)} : Set (Ω × Ω)) = {(y, x)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      Prod.swap_prod_mk, Prod.mk.injEq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩
  rw [hpre, compProd_toKernel_singleton, hbalance x y]

end MathlibBridge

namespace Protocol

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable {n : ℕ}

/-- The original pointwise local-balance equation also holds after normalizing
both Boltzmann weights to Gibbs probabilities. -/
theorem gibbsProbability_localBalance
    (P : Protocol Ω n) (t : Fin n) (x y : Ω) :
    gibbsProbability P.β (P.energy (t.val + 1)) x *
        P.forwardKernel t x y =
      gibbsProbability P.β (P.energy (t.val + 1)) y *
        P.reverseKernel t y x := by
  unfold gibbsProbability
  calc
    boltzmannWeight P.β (P.energy (t.val + 1)) x /
          partitionFunction P.β (P.energy (t.val + 1)) *
        P.forwardKernel t x y =
      (boltzmannWeight P.β (P.energy (t.val + 1)) x *
        P.forwardKernel t x y) /
          partitionFunction P.β (P.energy (t.val + 1)) := by ring
    _ = (boltzmannWeight P.β (P.energy (t.val + 1)) y *
        P.reverseKernel t y x) /
          partitionFunction P.β (P.energy (t.val + 1)) := by
      rw [P.localBalance t x y]
    _ = boltzmannWeight P.β (P.energy (t.val + 1)) y /
          partitionFunction P.β (P.energy (t.val + 1)) *
        P.reverseKernel t y x := by ring

/-- Every finite protocol local-balance assumption induces the exact
`Measure.compProd` equality used by the general-state theorem. -/
theorem measureLocalBalance
    (P : Protocol Ω n) (t : Fin n) :
    (gibbsDistribution P.β (P.energy (t.val + 1))).toMeasure ⊗ₘ
        P.forwardMathlibKernel t =
      ((gibbsDistribution P.β (P.energy (t.val + 1))).toMeasure ⊗ₘ
        P.reverseMathlibKernel t).map Prod.swap := by
  exact MathlibBridge.localBalance_toMeasure
    (gibbsDistribution P.β (P.energy (t.val + 1)))
    (P.forwardKernel t) (P.reverseKernel t)
    (P.gibbsProbability_localBalance t)

/-- Reweighting a finite Gibbs measure by a quench factor produces the next
finite Gibbs measure with the standard free-energy scalar. -/
theorem measureReweight
    (P : Protocol Ω n) (t : Fin n) :
    (gibbsDistribution P.β (P.energy t.val)).toMeasure.withDensity
        (MeasureProtocol.Gibbs.workWeight P.β
          (P.energy t.val) (P.energy (t.val + 1))) =
      ENNReal.ofReal (Real.exp (-P.β *
        (freeEnergy P.β (P.energy (t.val + 1)) -
          freeEnergy P.β (P.energy t.val)))) •
        (gibbsDistribution P.β (P.energy (t.val + 1))).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  rw [FiniteDistribution.toMeasure_singleton]
  simp only [Measure.smul_apply, smul_eq_mul,
    FiniteDistribution.toMeasure_singleton]
  have hZ0 : partitionFunction P.β (P.energy t.val) ≠ 0 :=
    partitionFunction_ne_zero P.β (P.energy t.val)
  have hZ1 : partitionFunction P.β (P.energy (t.val + 1)) ≠ 0 :=
    partitionFunction_ne_zero P.β (P.energy (t.val + 1))
  have hfactor := exp_neg_beta_mul_freeEnergy_sub P.β P.β_pos.ne'
    (P.energy t.val) (P.energy (t.val + 1))
  have hreal :
      Real.exp (-P.β *
          (P.energy (t.val + 1) x - P.energy t.val x)) *
          gibbsProbability P.β (P.energy t.val) x =
        Real.exp (-P.β *
          (freeEnergy P.β (P.energy (t.val + 1)) -
            freeEnergy P.β (P.energy t.val))) *
          gibbsProbability P.β (P.energy (t.val + 1)) x := by
    rw [hfactor]
    unfold gibbsProbability boltzmannWeight
    calc
      Real.exp (-P.β *
          (P.energy (t.val + 1) x - P.energy t.val x)) *
          (Real.exp (-P.β * P.energy t.val x) /
            partitionFunction P.β (P.energy t.val)) =
        Real.exp (-P.β * P.energy (t.val + 1) x) /
          partitionFunction P.β (P.energy t.val) := by
            field_simp [hZ0]
            rw [← Real.exp_add]
            congr 1
            ring
      _ = (partitionFunction P.β (P.energy (t.val + 1)) /
          partitionFunction P.β (P.energy t.val)) *
          (Real.exp (-P.β * P.energy (t.val + 1) x) /
            partitionFunction P.β (P.energy (t.val + 1))) := by
            field_simp [hZ0, hZ1]
  unfold MeasureProtocol.Gibbs.workWeight
  change
    ENNReal.ofReal (Real.exp (-P.β *
        (P.energy (t.val + 1) x - P.energy t.val x))) *
        ENNReal.ofReal (gibbsProbability P.β (P.energy t.val) x) =
      ENNReal.ofReal (Real.exp (-P.β *
        (freeEnergy P.β (P.energy (t.val + 1)) -
          freeEnergy P.β (P.energy t.val)))) *
        ENNReal.ofReal
          (gibbsProbability P.β (P.energy (t.val + 1)) x)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact congrArg ENNReal.ofReal hreal

/-- The original finite protocol is a concrete instance of the general
chronological finite-horizon Crooks theorem. -/
theorem measure_crooks
    (P : Protocol Ω n) :
    MeasureProtocol.CrooksRelation
      (MeasureProtocol.Markov.chronologicalForwardPathMeasure
        (gibbsDistribution P.β P.initialEnergy).toMeasure
        (fun i => P.forwardMathlibKernel i))
      (MeasureProtocol.Markov.timeReversedReversePathMeasure
        (gibbsDistribution P.β P.finalEnergy).toMeasure
        (fun i => P.reverseMathlibKernel i))
      (fun γ => ENNReal.ofReal (Real.exp (-P.β *
        MeasureProtocol.Gibbs.pathWork
          (fun i : Fin (n + 1) => P.energy i.val) γ)))
      (ENNReal.ofReal (Real.exp (-P.β * P.deltaFreeEnergy))) := by
  let equilibrium : Fin (n + 1) → Measure Ω :=
    fun i => (gibbsDistribution P.β (P.energy i.val)).toMeasure
  let forward : Fin n → ProbabilityTheory.Kernel Ω Ω :=
    fun i => P.forwardMathlibKernel i
  let reverse : Fin n → ProbabilityTheory.Kernel Ω Ω :=
    fun i => P.reverseMathlibKernel i
  let stepWork : Fin n → Ω → ℝ≥0∞ :=
    fun i => MeasureProtocol.Gibbs.workWeight P.β
      (P.energy i.val) (P.energy (i.val + 1))
  let stepFactor : Fin n → ℝ≥0∞ :=
    fun i => ENNReal.ofReal (Real.exp (-P.β *
      (freeEnergy P.β (P.energy (i.val + 1)) -
        freeEnergy P.β (P.energy i.val))))
  letI : ∀ i, IsProbabilityMeasure (equilibrium i) := by
    intro i
    dsimp [equilibrium]
    infer_instance
  letI : ∀ i, IsMarkovKernel (forward i) := by
    intro i
    dsimp [forward]
    infer_instance
  letI : ∀ i, IsMarkovKernel (reverse i) := by
    intro i
    dsimp [reverse]
    infer_instance
  have h := MeasureProtocol.Markov.multiStep_crooks_chronological
    equilibrium forward reverse stepWork stepFactor
    (fun i => MeasureProtocol.Gibbs.measurable_workWeight P.β
      (Measurable.of_discrete) (Measurable.of_discrete))
    (fun i => by
      dsimp [equilibrium, stepWork, stepFactor]
      simpa using P.measureReweight i)
    (fun i => by
      dsimp [equilibrium, forward, reverse]
      simpa using P.measureLocalBalance i)
  have hwork :
      MeasureProtocol.Markov.chronologicalWorkWeight stepWork =
        (fun γ => ENNReal.ofReal (Real.exp (-P.β *
          MeasureProtocol.Gibbs.pathWork
            (fun i : Fin (n + 1) => P.energy i.val) γ))) := by
    funext γ
    exact MeasureProtocol.Gibbs.chronologicalWorkWeight_eq_exp_pathWork
      P.β (fun i : Fin (n + 1) => P.energy i.val) γ
  have hfactor :
      MeasureProtocol.Markov.accumulatedFreeEnergyWeight stepFactor =
        ENNReal.ofReal (Real.exp (-P.β * P.deltaFreeEnergy)) := by
    dsimp [stepFactor]
    rw [MeasureProtocol.Markov.accumulatedFreeEnergyWeight_eq_exp_sum]
    have htel :
        MeasureProtocol.Markov.accumulatedStepSum
            (fun i : Fin n =>
              freeEnergy P.β (P.energy (i.val + 1)) -
                freeEnergy P.β (P.energy i.val)) =
          freeEnergy P.β (P.energy n) - freeEnergy P.β (P.energy 0) := by
      simpa using
        (MeasureProtocol.Markov.accumulatedStepSum_telescope
          (fun i : Fin (n + 1) => freeEnergy P.β (P.energy i.val)))
    rw [htel]
    rfl
  rw [hwork, hfactor] at h
  simpa [equilibrium, forward, reverse, Protocol.initialEnergy,
    Protocol.finalEnergy] using h

/-- The legacy finite protocol therefore satisfies the real-integral
Jarzynski equality through the general measure-theoretic theorem. -/
theorem measure_jarzynski_integral
    (P : Protocol Ω n) :
    ∫ γ, Real.exp (-P.β *
          MeasureProtocol.Gibbs.pathWork
            (fun i : Fin (n + 1) => P.energy i.val) γ)
        ∂MeasureProtocol.Markov.chronologicalForwardPathMeasure
          (gibbsDistribution P.β P.initialEnergy).toMeasure
          (fun i => P.forwardMathlibKernel i) =
      Real.exp (-P.β * P.deltaFreeEnergy) := by
  exact MeasureProtocol.jarzynski_integral _ _ P.β P.deltaFreeEnergy
    (MeasureProtocol.Gibbs.pathWork
      (fun i : Fin (n + 1) => P.energy i.val))
    (MeasureProtocol.Gibbs.measurable_pathWork
      (fun i : Fin (n + 1) => P.energy i.val)
      (fun _ => Measurable.of_discrete))
    P.measure_crooks

end Protocol
end CrooksJarzynski
