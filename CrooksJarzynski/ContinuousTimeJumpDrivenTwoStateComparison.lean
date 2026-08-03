/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenTwoState
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorBridge
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricParity

/-!
# Comparing the generic and legacy asymmetric one-window laws

The generic finite-generator path law and the earlier asymmetric two-state path
law use different simplex reference charts. Their terminal-state pushforwards
are nevertheless the same probability measure: both are identified with the
same row of the exponential of the same conservative generator.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- The generic and legacy fixed-initial laws assign the same real mass to each
terminal-state atom. -/
theorem physicalFiniteGenerator_terminalState_real_singleton_eq_legacy
    (T : NNReal) (x y : State) :
    ((physicalFiniteGenerator.pathLawFrom T x).map
        FullPath.terminalState).real {y} =
      ((asymmetricPathLawFrom T x).map FullPath.terminalState).real {y} := by
  calc
    ((physicalFiniteGenerator.pathLawFrom T x).map
        FullPath.terminalState).real {y} =
      NormedSpace.exp
        ((T : ℝ) • physicalFiniteGenerator.generator) x y :=
      physicalFiniteGenerator.pathLawFrom_terminalState_eq_exp_generator T x y
    _ = NormedSpace.exp
        ((T : ℝ) •
          (show Matrix State State ℝ from
            fun a b => physicalGenerator a b)) x y := by
      rw [physicalFiniteGenerator_generator_eq]
    _ = ((asymmetricPathLawFrom T x).map
        FullPath.terminalState).real {y} :=
      (asymmetricPathLawFrom_terminalState_eq_exp_generator T x y).symm

/-- The terminal-state pushforward of the generic finite-generator path law is
exactly the terminal-state pushforward of the earlier asymmetric path law. -/
theorem map_physicalFiniteGenerator_pathLawFrom_terminalState_eq_legacy
    (T : NNReal) (x : State) :
    (physicalFiniteGenerator.pathLawFrom T x).map FullPath.terminalState =
      (asymmetricPathLawFrom T x).map FullPath.terminalState := by
  letI : IsProbabilityMeasure
      ((physicalFiniteGenerator.pathLawFrom T x).map
        FullPath.terminalState) :=
    Measure.isProbabilityMeasure_map
      FullPath.measurable_terminalState.aemeasurable
  letI : IsProbabilityMeasure
      ((asymmetricPathLawFrom T x).map FullPath.terminalState) :=
    Measure.isProbabilityMeasure_map
      FullPath.measurable_terminalState.aemeasurable
  apply Measure.ext_of_singleton
  intro y
  exact (measureReal_eq_measureReal_iff).1
    (physicalFiniteGenerator_terminalState_real_singleton_eq_legacy T x y)

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
