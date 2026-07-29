/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolPaths
import CrooksJarzynski.MeasureProtocolGibbs

/-!
# Physical finite-horizon Crooks and Jarzynski statements

This module packages the products of step weights as exponentials of total work
and telescopes the stepwise free-energy increments. The resulting theorems use
chronological paths and the standard physical factors `exp (-β W)` and
`exp (-β ΔF)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Accumulate a real-valued step observable along a reverse-oriented recursive
trajectory. -/
noncomputable def Markov.reversedAccumulatedWork :
    {n : ℕ} → (Fin n → Ω → ℝ) → Trajectory Ω n → ℝ
  | 0, _, _ => 0
  | n + 1, work, γ =>
      Markov.reversedAccumulatedWork (fun i => work i.castSucc) γ.2 +
        work (Fin.last n) γ.2.1

/-- Measurability of a real-valued accumulated path observable. -/
theorem Markov.measurable_reversedAccumulatedWork
    {n : ℕ} (work : Fin n → Ω → ℝ)
    (hwork : ∀ i, Measurable (work i)) :
    Measurable (Markov.reversedAccumulatedWork work) := by
  induction n with
  | zero =>
      simpa [Markov.reversedAccumulatedWork] using
        (measurable_const : Measurable (fun _ : Trajectory Ω 0 => (0 : ℝ)))
  | succ n ih =>
      change Measurable (fun γ : Ω × Trajectory Ω n =>
        Markov.reversedAccumulatedWork (fun i => work i.castSucc) γ.2 +
          work (Fin.last n) γ.2.1)
      exact
        ((ih (fun i => work i.castSucc) (fun i => hwork i.castSucc)).comp
          (measurable_snd :
            Measurable (fun γ : Ω × Trajectory Ω n => γ.2))).add
          ((hwork (Fin.last n)).comp
            ((measurable_fst : Measurable (fun γ : Trajectory Ω n => γ.1)).comp
              (measurable_snd :
                Measurable (fun γ : Ω × Trajectory Ω n => γ.2))))

/-- A product of exponential step weights is the exponential of the accumulated
step observable. -/
theorem Markov.reversedWorkWeight_eq_exp_accumulated
    {n : ℕ} (β : ℝ) (work : Fin n → Ω → ℝ)
    (γ : Trajectory Ω n) :
    Markov.reversedWorkWeight
        (fun i x => ENNReal.ofReal (Real.exp (-β * work i x))) γ =
      ENNReal.ofReal
        (Real.exp (-β * Markov.reversedAccumulatedWork work γ)) := by
  induction n with
  | zero =>
      simp [Markov.reversedWorkWeight, Markov.reversedAccumulatedWork]
  | succ n ih =>
      change
        Markov.reversedWorkWeight
            (fun i x => ENNReal.ofReal
              (Real.exp (-β * work i.castSucc x))) γ.2 *
          ENNReal.ofReal (Real.exp (-β * work (Fin.last n) γ.2.1)) =
        ENNReal.ofReal (Real.exp (-β *
          (Markov.reversedAccumulatedWork
              (fun i => work i.castSucc) γ.2 +
            work (Fin.last n) γ.2.1)))
      rw [ih (work := fun i => work i.castSucc) (γ := γ.2)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

/-- Recursive sum of a scalar attached to each protocol step. -/
def Markov.accumulatedStepSum : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, step =>
      Markov.accumulatedStepSum (fun i => step i.castSucc) +
        step (Fin.last n)

/-- Consecutive increments telescope to the endpoint difference. -/
theorem Markov.accumulatedStepSum_telescope
    {n : ℕ} (value : Fin (n + 1) → ℝ) :
    Markov.accumulatedStepSum
        (fun i => value i.succ - value i.castSucc) =
      value (Fin.last n) - value 0 := by
  induction n with
  | zero =>
      simp [Markov.accumulatedStepSum]
  | succ n ih =>
      simp only [Markov.accumulatedStepSum]
      have hprefix :
          (fun i : Fin n =>
            value i.castSucc.succ - value i.castSucc.castSucc) =
          (fun i : Fin n =>
            (fun j : Fin (n + 1) => value j.castSucc) i.succ -
              (fun j : Fin (n + 1) => value j.castSucc) i.castSucc) := by
        funext i
        apply congrArg₂ (· - ·)
        · apply congrArg value
          ext
          rfl
        · rfl
      rw [hprefix, ih (value := fun j => value j.castSucc)]
      rw [← Fin.succ_last]
      simp

/-- Scalar exponential step factors multiply to the exponential of their
recursive sum. -/
theorem Markov.accumulatedFreeEnergyWeight_eq_exp_sum
    {n : ℕ} (β : ℝ) (step : Fin n → ℝ) :
    Markov.accumulatedFreeEnergyWeight
        (fun i => ENNReal.ofReal (Real.exp (-β * step i))) =
      ENNReal.ofReal
        (Real.exp (-β * Markov.accumulatedStepSum step)) := by
  induction n with
  | zero =>
      simp [Markov.accumulatedFreeEnergyWeight, Markov.accumulatedStepSum]
  | succ n ih =>
      simp only [Markov.accumulatedFreeEnergyWeight,
        Markov.accumulatedStepSum]
      rw [ih (step := fun i => step i.castSucc)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

namespace Gibbs

/-- Total quench work on a chronological trajectory. -/
noncomputable def pathWork
    {n : ℕ} (energy : Fin (n + 1) → Ω → ℝ)
    (γ : Trajectory Ω n) : ℝ :=
  Markov.reversedAccumulatedWork
    (fun i x => energy i.succ x - energy i.castSucc x)
    (Trajectory.reverse γ)

/-- The endpoint equilibrium free-energy difference. -/
noncomputable def deltaFreeEnergy
    {n : ℕ} (base : Measure Ω) (β : ℝ)
    (energy : Fin (n + 1) → Ω → ℝ) : ℝ :=
  freeEnergy base β (energy (Fin.last n)) -
    freeEnergy base β (energy 0)

/-- Measurability of total chronological path work. -/
theorem measurable_pathWork
    {n : ℕ} (energy : Fin (n + 1) → Ω → ℝ)
    (henergy : ∀ i, Measurable (energy i)) :
    Measurable (pathWork energy) := by
  have hstep : ∀ i : Fin n, Measurable
      (fun x => energy i.succ x - energy i.castSucc x) := by
    intro i
    exact (henergy i.succ).sub (henergy i.castSucc)
  change Measurable (fun γ : Trajectory Ω n =>
    Markov.reversedAccumulatedWork
      (fun i x => energy i.succ x - energy i.castSucc x)
      (Trajectory.reverse γ))
  exact (Markov.measurable_reversedAccumulatedWork
    (fun i x => energy i.succ x - energy i.castSucc x) hstep).comp
      Trajectory.measurable_reverse

/-- Work performed in the reverse experiment on its chronological path.
Reversing the path and the protocol changes the sign of the forward work. -/
noncomputable def reversePathWork
    {n : ℕ} (energy : Fin (n + 1) → Ω → ℝ)
    (γ : Trajectory Ω n) : ℝ :=
  -pathWork energy (Trajectory.reverse γ)

/-- Measurability of reverse-protocol work. -/
theorem measurable_reversePathWork
    {n : ℕ} (energy : Fin (n + 1) → Ω → ℝ)
    (henergy : ∀ i, Measurable (energy i)) :
    Measurable (reversePathWork energy) := by
  exact ((measurable_pathWork energy henergy).comp
    Trajectory.measurable_reverse).neg

/-- The chronological work factor is exactly `exp (-β W)`. -/
theorem chronologicalWorkWeight_eq_exp_pathWork
    {n : ℕ} (β : ℝ) (energy : Fin (n + 1) → Ω → ℝ)
    (γ : Trajectory Ω n) :
    Markov.chronologicalWorkWeight
        (fun i => workWeight β (energy i.castSucc) (energy i.succ)) γ =
      ENNReal.ofReal (Real.exp (-β * pathWork energy γ)) := by
  unfold Markov.chronologicalWorkWeight pathWork workWeight
  simpa using
    (Markov.reversedWorkWeight_eq_exp_accumulated
      (Ω := Ω) β
      (fun i x => energy i.succ x - energy i.castSucc x)
      (Trajectory.reverse γ))

/-- The product of stepwise equilibrium factors telescopes to
`exp (-β ΔF)`. -/
theorem accumulatedFreeEnergyWeight_eq_exp_delta
    {n : ℕ} (base : Measure Ω) (β : ℝ)
    (energy : Fin (n + 1) → Ω → ℝ) :
    Markov.accumulatedFreeEnergyWeight
        (fun i => freeEnergyWeight base β
          (energy i.castSucc) (energy i.succ)) =
      ENNReal.ofReal (Real.exp (-β * deltaFreeEnergy base β energy)) := by
  unfold freeEnergyWeight deltaFreeEnergy
  rw [Markov.accumulatedFreeEnergyWeight_eq_exp_sum]
  have htel :
      Markov.accumulatedStepSum
          (fun i : Fin n =>
            freeEnergy base β (energy i.succ) -
              freeEnergy base β (energy i.castSucc)) =
        freeEnergy base β (energy (Fin.last n)) -
          freeEnergy base β (energy 0) :=
    Markov.accumulatedStepSum_telescope
      (fun i => freeEnergy base β (energy i))
  rw [htel]

/-- The standard physical finite-horizon Crooks relation on chronological paths
in an arbitrary measurable state space. -/
theorem multiStep_crooks_physical
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
      (Markov.chronologicalForwardPathMeasure
        (measure base β (energy 0)) forward)
      (Markov.timeReversedReversePathMeasure
        (measure base β (energy (Fin.last n))) reverse)
      (fun γ => ENNReal.ofReal (Real.exp (-β * pathWork energy γ)))
      (ENNReal.ofReal
        (Real.exp (-β * deltaFreeEnergy base β energy))) := by
  let equilibrium : Fin (n + 1) → Measure Ω :=
    fun i => measure base β (energy i)
  letI : ∀ i, IsProbabilityMeasure (equilibrium i) :=
    fun i => isProbabilityMeasure_measure base β (energy i) (henergyInt i)
  have h := Markov.multiStep_crooks_chronological
    equilibrium forward reverse
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
  have hweight :
      Markov.chronologicalWorkWeight
          (fun i => workWeight β (energy i.castSucc) (energy i.succ)) =
        (fun γ => ENNReal.ofReal
          (Real.exp (-β * pathWork energy γ))) := by
    funext γ
    exact chronologicalWorkWeight_eq_exp_pathWork β energy γ
  rw [hweight,
    accumulatedFreeEnergyWeight_eq_exp_delta base β energy] at h
  simpa [equilibrium] using h

/-- The usual real-valued Jarzynski equality on chronological paths. -/
theorem multiStep_jarzynski_integral
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
    ∫ γ, Real.exp (-β * pathWork energy γ)
        ∂Markov.chronologicalForwardPathMeasure
          (measure base β (energy 0)) forward =
      Real.exp (-β * deltaFreeEnergy base β energy) := by
  letI : IsProbabilityMeasure
      (measure base β (energy (Fin.last n))) :=
    isProbabilityMeasure_measure base β (energy (Fin.last n))
      (henergyInt (Fin.last n))
  exact jarzynski_integral _ _ β (deltaFreeEnergy base β energy)
    (pathWork energy) (measurable_pathWork energy henergyMeas)
    (multiStep_crooks_physical base β hβ energy forward reverse
      henergyMeas henergyInt hbalance)

/-- Crooks' relation for the pushforward law of total work, without an
assumption that the work law has a density or atoms. The reverse-hand measure
is explicitly the law of `-W_R`: reverse paths are first mapped to their
reverse-protocol work and then through negation. -/
theorem multiStep_work_distribution_crooks
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
    CrooksRelation
      ((Markov.chronologicalForwardPathMeasure
        (measure base β (energy 0)) forward).map (pathWork energy))
      (((Markov.reversePathMeasure
          (measure base β (energy (Fin.last n))) reverse).map
            (reversePathWork energy)).map fun w => -w)
      (fun w => ENNReal.ofReal (Real.exp (-β * w)))
      (ENNReal.ofReal
        (Real.exp (-β * deltaFreeEnergy base β energy))) := by
  have h := work_distribution_crooks _ _ β (deltaFreeEnergy base β energy)
    (pathWork energy) (measurable_pathWork energy henergyMeas)
    (multiStep_crooks_physical base β hβ energy forward reverse
      henergyMeas henergyInt hbalance)
  unfold Markov.timeReversedReversePathMeasure at h
  change CrooksRelation
    ((Markov.chronologicalForwardPathMeasure
      (measure base β (energy 0)) forward).map (pathWork energy))
    ((Markov.reversePathMeasure
      (measure base β (energy (Fin.last n))) reverse).map
        Trajectory.reverse |>.map (pathWork energy))
    _ _ at h
  rw [Measure.map_map (measurable_pathWork energy henergyMeas)
    Trajectory.measurable_reverse] at h
  rw [Measure.map_map measurable_neg
    (measurable_reversePathWork energy henergyMeas)]
  simpa [reversePathWork, Function.comp_def] using h

end Gibbs
end MeasureProtocol
end CrooksJarzynski
