/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenGlobalCrooks
import CrooksJarzynski.ContinuousTimeJumpDrivenThreeStateTwoWindow

/-!
# Global-chart regressions for the three-state two-window protocol

The nondegenerate work atoms of the three-state two-window protocol are
re-proved on the concatenated global chart, via the equality of the global and
marked work distributions. Keeping these regressions outside
`ContinuousTimeJumpDrivenGlobalCrooks` leaves the general global fluctuation
theorems free of any concrete-model import.
-/

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven
namespace ThreeStateTwoWindow

/-- The global-chart work distribution retains the positive atom at zero. -/
theorem global_work_zero_atom_pos (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    0 < (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration) {γ | globalWork energy duration γ = 0} := by
  have hmap := map_globalWork_forwardGlobalLaw
    (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
    energy generator duration
  have hmass := congrArg (fun μ : Measure ℝ => μ {0}) hmap
  rw [Measure.map_apply
      (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
      (measurableSet_singleton (0 : ℝ)),
    Measure.map_apply
      (measurable_work energy fun _ => Measurable.of_discrete)
      (measurableSet_singleton (0 : ℝ))] at hmass
  have hmass' : (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration) {γ | globalWork energy duration γ = 0} =
        (forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
          generator duration) {γ | work energy γ = 0} := by
    rw [show {γ | globalWork energy duration γ = 0} =
        globalWork energy duration ⁻¹' {0} by ext γ; simp,
      show {γ | work energy γ = 0} = work energy ⁻¹' {0} by ext γ; simp]
    exact hmass
  rw [hmass']
  exact work_zero_atom_pos duration hduration

/-- The global-chart work distribution retains the positive atom at
`log 2`. -/
theorem global_work_log_two_atom_pos (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    0 < (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration)
        {γ | globalWork energy duration γ = Real.log 2} := by
  have hmap := map_globalWork_forwardGlobalLaw
    (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
    energy generator duration
  have hmass := congrArg (fun μ : Measure ℝ => μ {Real.log 2}) hmap
  rw [Measure.map_apply
      (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
      (measurableSet_singleton (Real.log 2)),
    Measure.map_apply
      (measurable_work energy fun _ => Measurable.of_discrete)
      (measurableSet_singleton (Real.log 2))] at hmass
  have hmass' : (forwardGlobalLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration)
        {γ | globalWork energy duration γ = Real.log 2} =
        (forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
          generator duration) {γ | work energy γ = Real.log 2} := by
    rw [show {γ | globalWork energy duration γ = Real.log 2} =
        globalWork energy duration ⁻¹' {Real.log 2} by ext γ; simp,
      show {γ | work energy γ = Real.log 2} =
        work energy ⁻¹' {Real.log 2} by ext γ; simp]
    exact hmass
  rw [hmass']
  exact work_log_two_atom_pos duration hduration

end ThreeStateTwoWindow
end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
