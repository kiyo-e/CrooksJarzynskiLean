/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.TimeReversal
import CrooksJarzynski.MeasureProtocolFiniteCrooks

/-!
# Measurable reversal and chronological finite path measures

The finite-horizon measure construction is most convenient in reverse
chronological order. This module proves that the existing trajectory reversal
is measurable and transports the measure-level Crooks relation to the usual
chronological presentation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski

namespace Trajectory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Reading every vertex of a recursive trajectory is measurable. -/
theorem measurable_stateAt {n : ℕ} :
    Measurable (@stateAt Ω n) := by
  induction n with
  | zero =>
      refine measurable_pi_iff.2 ?_
      intro i
      fin_cases i
      simpa [stateAt] using
        (measurable_fst : Measurable (fun γ : Trajectory Ω 0 => γ.1))
  | succ n ih =>
      refine measurable_pi_iff.2 ?_
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [stateAt] using
          (measurable_fst :
            Measurable (fun γ : Trajectory Ω (n + 1) => γ.1))
      · change Measurable
          (fun γ : Trajectory Ω (n + 1) => stateAt γ.2 j)
        exact (measurable_pi_apply j).comp
          (ih.comp
            (measurable_snd :
              Measurable (fun γ : Trajectory Ω (n + 1) => γ.2)))

/-- Building a recursive trajectory from its vertex function is measurable. -/
theorem measurable_ofFn {n : ℕ} :
    Measurable (@ofFn Ω n) := by
  induction n with
  | zero =>
      change Measurable (fun f : Fin 1 → Ω =>
        (f 0, (PUnit.unit : Continuation Ω 0)))
      exact (measurable_pi_apply (0 : Fin 1)).prodMk measurable_const
  | succ n ih =>
      have htail : Measurable
          (fun f : Fin (n + 2) → Ω =>
            fun i : Fin (n + 1) => f i.succ) := by
        refine measurable_pi_iff.2 ?_
        intro i
        exact measurable_pi_apply i.succ
      change Measurable (fun f : Fin (n + 2) → Ω =>
        (f 0, ofFn (fun i : Fin (n + 1) => f i.succ)))
      exact (measurable_pi_apply (0 : Fin (n + 2))).prodMk
        (ih.comp htail)

/-- Recursive trajectories and vertex-indexed functions are measurably equivalent. -/
def stateAtMeasurableEquiv (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) :
    Trajectory Ω n ≃ᵐ (Fin (n + 1) → Ω) where
  toEquiv :=
    { toFun := stateAt
      invFun := ofFn
      left_inv := ofFn_stateAt
      right_inv := stateAt_ofFn }
  measurable_toFun := measurable_stateAt
  measurable_invFun := measurable_ofFn

/-- Reversing a finite trajectory is measurable. -/
@[fun_prop]
theorem measurable_reverse {n : ℕ} :
    Measurable (@reverse Ω n) := by
  unfold reverse
  apply measurable_ofFn.comp
  refine measurable_pi_iff.2 ?_
  intro i
  exact (measurable_pi_apply i.rev).comp measurable_stateAt

/-- Trajectory reversal as a measurable involutive equivalence. -/
def reverseMeasurableEquiv (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) :
    Trajectory Ω n ≃ᵐ Trajectory Ω n where
  toEquiv := reverseEquiv Ω n
  measurable_toFun := measurable_reverse
  measurable_invFun := measurable_reverse

end Trajectory

namespace MeasureProtocol

/-- A Crooks relation can be transported through finite trajectory reversal. -/
theorem CrooksRelation.reverse_paths
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (forward reverse : Measure (Trajectory Ω n))
    (workWeight : Trajectory Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hwork : Measurable workWeight)
    (h : CrooksRelation forward reverse workWeight freeEnergyWeight) :
    CrooksRelation
      (forward.map (Trajectory.reverseMeasurableEquiv Ω n))
      (reverse.map (Trajectory.reverseMeasurableEquiv Ω n))
      (fun γ => workWeight (Trajectory.reverse γ))
      freeEnergyWeight := by
  apply CrooksRelation.map forward reverse Trajectory.reverse
    (fun γ => workWeight (Trajectory.reverse γ)) freeEnergyWeight
    Trajectory.measurable_reverse
    (hwork.comp Trajectory.measurable_reverse)
  simpa [Function.comp_def] using h

namespace Markov

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The forward finite-path law in chronological order `(x₀, …, xₙ)`. -/
noncomputable def chronologicalForwardPathMeasure
    {n : ℕ} (initial : Measure Ω)
    (forward : Fin n → ProbabilityTheory.Kernel Ω Ω) :
    Measure (Trajectory Ω n) :=
  (reversedForwardPathMeasure initial forward).map
    (Trajectory.reverseMeasurableEquiv Ω n)

/-- The reverse-experiment law, reversed back into forward chronological
coordinates. -/
noncomputable def timeReversedReversePathMeasure
    {n : ℕ} (final : Measure Ω)
    (reverse : Fin n → ProbabilityTheory.Kernel Ω Ω) :
    Measure (Trajectory Ω n) :=
  (reversePathMeasure final reverse).map
    (Trajectory.reverseMeasurableEquiv Ω n)

noncomputable instance instIsProbabilityMeasureChronologicalForwardPathMeasure
    {n : ℕ} (initial : Measure Ω)
    (forward : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure initial] [∀ i, IsMarkovKernel (forward i)] :
    IsProbabilityMeasure (chronologicalForwardPathMeasure initial forward) := by
  unfold chronologicalForwardPathMeasure
  exact Measure.isProbabilityMeasure_map
    Trajectory.measurable_reverse.aemeasurable

noncomputable instance instIsProbabilityMeasureTimeReversedReversePathMeasure
    {n : ℕ} (final : Measure Ω)
    (reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure final] [∀ i, IsMarkovKernel (reverse i)] :
    IsProbabilityMeasure (timeReversedReversePathMeasure final reverse) := by
  unfold timeReversedReversePathMeasure
  exact Measure.isProbabilityMeasure_map
    Trajectory.measurable_reverse.aemeasurable

/-- A product of step work factors, read on a chronological trajectory. -/
noncomputable def chronologicalWorkWeight
    {n : ℕ} (workWeight : Fin n → Ω → ℝ≥0∞) :
    Trajectory Ω n → ℝ≥0∞ :=
  fun γ => reversedWorkWeight workWeight (Trajectory.reverse γ)

/-- Measurability of the chronological accumulated work factor. -/
theorem measurable_chronologicalWorkWeight
    {n : ℕ} (workWeight : Fin n → Ω → ℝ≥0∞)
    (hwork : ∀ i, Measurable (workWeight i)) :
    Measurable (chronologicalWorkWeight workWeight) :=
  (measurable_reversedWorkWeight workWeight hwork).comp
    Trajectory.measurable_reverse

/-- The finite-horizon Crooks relation in the conventional chronological path
coordinates. -/
theorem multiStep_crooks_chronological
    {n : ℕ}
    (equilibrium : Fin (n + 1) → Measure Ω)
    (forward reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    (workWeight : Fin n → Ω → ℝ≥0∞)
    (freeEnergyWeight : Fin n → ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (equilibrium i)]
    [∀ i, IsMarkovKernel (forward i)]
    [∀ i, IsMarkovKernel (reverse i)]
    (hwork : ∀ i, Measurable (workWeight i))
    (hreweight : ∀ i,
      (equilibrium i.castSucc).withDensity (workWeight i) =
        freeEnergyWeight i • equilibrium i.succ)
    (hbalance : ∀ i,
      equilibrium i.succ ⊗ₘ forward i =
        (equilibrium i.succ ⊗ₘ reverse i).map Prod.swap) :
    CrooksRelation
      (chronologicalForwardPathMeasure (equilibrium 0) forward)
      (timeReversedReversePathMeasure
        (equilibrium (Fin.last n)) reverse)
      (chronologicalWorkWeight workWeight)
      (accumulatedFreeEnergyWeight freeEnergyWeight) := by
  unfold chronologicalForwardPathMeasure timeReversedReversePathMeasure
    chronologicalWorkWeight
  exact CrooksRelation.reverse_paths _ _ _ _
    (measurable_reversedWorkWeight workWeight hwork)
    (multiStep_crooks equilibrium forward reverse workWeight freeEnergyWeight
      hwork hreweight hbalance)

end Markov
end MeasureProtocol
end CrooksJarzynski
