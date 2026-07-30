/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateFixedInitial
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# The two-state transition semigroup as a Mathlib Markov kernel

The terminal-state laws of the normalized fixed-initial path measures are
packaged as a genuine `ProbabilityTheory.Kernel`. Its singleton probabilities
are the entries of `exp (TQ)`. The kernel at time zero is the identity kernel,
and kernel composition satisfies the Chapman--Kolmogorov semigroup law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- The transition kernel obtained by pushing the normalized path law started
at `x` through its actual terminal-state coordinate. -/
noncomputable def transitionKernel (T : NNReal) : Kernel State State :=
  Kernel.ofFunOfCountable fun x =>
    (pathLawFrom T x).map FullPath.terminalState

@[simp]
theorem transitionKernel_apply (T : NNReal) (x : State) :
    transitionKernel T x =
      (pathLawFrom T x).map FullPath.terminalState :=
  rfl

noncomputable instance instIsMarkovKernelTransitionKernel (T : NNReal) :
    IsMarkovKernel (transitionKernel T) := by
  constructor
  intro x
  change IsProbabilityMeasure
    ((pathLawFrom T x).map FullPath.terminalState)
  exact Measure.isProbabilityMeasure_map
    FullPath.measurable_terminalState.aemeasurable

/-- Every transition-kernel row is the Poisson-flip terminal law. -/
theorem transitionKernel_apply_eq_conditionalTerminalLaw
    (T : NNReal) (x : State) :
    transitionKernel T x = conditionalTerminalLaw T x := by
  rw [transitionKernel_apply, map_pathLawFrom_terminalState]

/-- The real singleton probabilities of the transition kernel are the explicit
two-state transition probabilities. -/
theorem transitionKernel_real_singleton
    (T : NNReal) (x y : State) :
    (transitionKernel T x).real {y} =
      transitionProbability (T : ℝ) x y := by
  rw [transitionKernel_apply_eq_conditionalTerminalLaw,
    conditionalTerminalLaw_real_singleton_eq]
  rfl

/-- The real singleton probabilities are the corresponding entries of the
matrix exponential of the conservative generator. -/
theorem transitionKernel_real_singleton_eq_exp_generator
    (T : NNReal) (x y : State) :
    (transitionKernel T x).real {y} =
      NormedSpace.exp
        ((T : ℝ) •
          (show Matrix State State ℝ from fun x y => generator x y)) x y := by
  rw [transitionKernel_apply]
  exact pathLawFrom_terminalState_eq_exp_generator T x y

/-- The explicit transition probabilities are nonnegative at every
nonnegative time. -/
theorem transitionProbability_nonneg
    (T : NNReal) (x y : State) :
    0 ≤ transitionProbability (T : ℝ) x y := by
  have hnonpos : -2 * (T : ℝ) ≤ 0 := by
    nlinarith [T.2]
  have hle : Real.exp (-2 * (T : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 hnonpos
  unfold transitionProbability
  split_ifs
  · positivity
  · exact div_nonneg (sub_nonneg.mpr hle) (by norm_num)

/-- ENNReal-valued singleton form of the explicit transition probability. -/
theorem transitionKernel_singleton
    (T : NNReal) (x y : State) :
    transitionKernel T x {y} =
      ENNReal.ofReal (transitionProbability (T : ℝ) x y) := by
  rw [← MeasureTheory.ofReal_measureReal]
  congr 1
  exact transitionKernel_real_singleton T x y

/-- Entrywise Chapman--Kolmogorov for the path-law transition kernel. -/
theorem transitionKernel_chapman_kolmogorov
    (S T : NNReal) (x y : State) :
    (∑ z : State,
      (transitionKernel S x).real {z} *
        (transitionKernel T z).real {y}) =
      (transitionKernel (S + T) x).real {y} := by
  simpa only [transitionKernel_real_singleton] using
    transitionProbability_chapman_kolmogorov S T x y

/-- The transition kernel at time zero is the identity kernel. -/
theorem transitionKernel_zero :
    transitionKernel 0 = (Kernel.id : Kernel State State) := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [transitionKernel_singleton, transitionProbability_zero]
  by_cases hxy : x = y
  · subst y
    simp [Kernel.id_apply]
  · simp [Kernel.id_apply, hxy]

/-- The fixed-initial terminal laws form a Markov semigroup under Mathlib kernel
composition. The rightmost kernel acts first. -/
theorem transitionKernel_add (S T : NNReal) :
    transitionKernel (S + T) =
      transitionKernel T ∘ₖ transitionKernel S := by
  symm
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton y),
    MeasureTheory.lintegral_fintype]
  simp_rw [transitionKernel_singleton]
  calc
    (∑ z : State,
        ENNReal.ofReal (transitionProbability (T : ℝ) z y) *
          ENNReal.ofReal (transitionProbability (S : ℝ) x z)) =
      ∑ z : State,
        ENNReal.ofReal
          (transitionProbability (S : ℝ) x z *
            transitionProbability (T : ℝ) z y) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← ENNReal.ofReal_mul (transitionProbability_nonneg T z y)]
      congr 1
      ring
    _ = ENNReal.ofReal
        (∑ z : State,
          transitionProbability (S : ℝ) x z *
            transitionProbability (T : ℝ) z y) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ)
        (fun z _ => mul_nonneg
          (transitionProbability_nonneg S x z)
          (transitionProbability_nonneg T z y))).symm
    _ = ENNReal.ofReal
        (transitionProbability ((S + T : NNReal) : ℝ) x y) :=
      congrArg ENNReal.ofReal
        (transitionProbability_chapman_kolmogorov S T x y)

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
