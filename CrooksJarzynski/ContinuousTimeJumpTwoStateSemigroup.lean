/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateFixedInitial
import Mathlib.Probability.Kernel.Basic

/-!
# The two-state transition semigroup as a Mathlib Markov kernel

The terminal-state laws of the normalized fixed-initial path measures are
packaged as a genuine `ProbabilityTheory.Kernel`.  Its singleton probabilities
are the entries of `exp (TQ)`, and the previously proved explicit
Chapman--Kolmogorov identity becomes the entrywise semigroup law for this
kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix

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

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
