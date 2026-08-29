/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteDimensional
import CrooksJarzynski.ContinuousTimeJumpTwoStateFiniteGenerator
import CrooksJarzynski.ContinuousTimeJumpTwoStateGenerator

/-!
# Interior-time non-determination for the two-state chain

This is the interior-time companion of the endpoint-nondetermination theorem
for driven work. It shows that a window's boundary pair does not determine the
real-time trajectory inside the window, so retaining complete window paths is
essential for path-level observables.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- Every explicit transition probability of the symmetric two-state chain is
strictly positive at a positive time. -/
theorem transitionProbability_pos (t : ℝ) (ht : 0 < t) (x y : State) :
    0 < transitionProbability t x y := by
  unfold transitionProbability
  split_ifs
  · positivity
  · have hexp : Real.exp (-2 * t) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    positivity

/-- Both possible states at the interior observation time have positive mass
when the path starts and ends at `State.zero`. -/
theorem interior_event_pos (T : NNReal) (hT : 0 < T) (y : State) :
    let time : Fin 3 → NNReal := ![0, T / 2, T]
    let γy : Trajectory State 2 :=
      Trajectory.ofFn ![State.zero, y, State.zero]
    0 < (finiteGenerator.pathLawFrom T State.zero)
      (FullPath.sampleAt time ⁻¹' {γy}) := by
  let time : Fin 3 → NNReal := ![0, T / 2, T]
  let γy : Trajectory State 2 :=
    Trajectory.ofFn ![State.zero, y, State.zero]
  have hhalf : 0 < T / 2 := div_pos hT (by norm_num)
  have hhalfReal : 0 < ((T / 2 : NNReal) : ℝ) := by
    exact_mod_cast hhalf
  have hhalfReal' : 0 < (T : ℝ) / 2 := by
    simpa using hhalfReal
  have hsecondHalf : (T : ℝ) - (T : ℝ) / 2 = (T : ℝ) / 2 := by
    ring
  have hmono : Monotone time := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [time]
  have hzero : time 0 = 0 := by simp [time]
  have hlast : time (Fin.last 2) ≤ T := by simp [time]
  have hreal :
      0 < ((finiteGenerator.pathLawFrom T State.zero).map
        (FullPath.sampleAt time)).real {γy} := by
    rw [FiniteJumpGenerator.pathLawFrom_sampleAt_real_singleton_eq_exp_product
      finiteGenerator T State.zero time hmono hzero hlast γy]
    simp [γy, time, Trajectory.ofFn, Fin.prod_univ_two,
      finiteGenerator_generator_eq, exp_smul_generator_apply]
    rw [hsecondHalf]
    exact mul_pos
      (transitionProbability_pos ((T : ℝ) / 2) hhalfReal' State.zero y)
      (transitionProbability_pos ((T : ℝ) / 2) hhalfReal' y State.zero)
  change 0 < (finiteGenerator.pathLawFrom T State.zero)
    (FullPath.sampleAt time ⁻¹' {γy})
  rw [← Measure.map_apply (FullPath.measurable_sampleAt time)
    (measurableSet_singleton γy)]
  exact pos_iff_ne_zero.mpr fun hzeroMeasure => by
    rw [Measure.real_def, hzeroMeasure] at hreal
    simp at hreal

/-- On a positive interior-state event, an almost-everywhere endpoint
representation must take the pinned endpoint pair to that interior state. -/
private theorem ae_endpoint_pair_value (T : NNReal) (hT : 0 < T) (y : State)
    (f : State → State → State)
    (hf : (fun γ => FullPath.trajectory γ ((T / 2 : NNReal) : ℝ))
      =ᵐ[finiteGenerator.pathLawFrom T State.zero]
      (fun γ => f (FullPath.initialState γ) (FullPath.terminalState γ))) :
    f State.zero State.zero = y := by
  let μ := finiteGenerator.pathLawFrom T State.zero
  let time : Fin 3 → NNReal := ![0, T / 2, T]
  let γy : Trajectory State 2 :=
    Trajectory.ofFn ![State.zero, y, State.zero]
  let event : Set (FullPath State) := FullPath.sampleAt time ⁻¹' {γy}
  let good : FullPath State → Prop := fun γ =>
    FullPath.trajectory γ ((T / 2 : NNReal) : ℝ) =
        f (FullPath.initialState γ) (FullPath.terminalState γ) ∧
      FullPath.initialState γ = State.zero ∧
      FullPath.trajectory γ (T : ℝ) = FullPath.terminalState γ
  have hgoodAE : ∀ᵐ γ ∂μ, good γ := by
    filter_upwards [hf,
      finiteGenerator.pathLawFrom_ae_initialState T State.zero,
      finiteGenerator.pathLawFrom_ae_trajectory_horizon T State.zero] with
        γ hfunction hinitial hterminal
    exact ⟨hfunction, hinitial, hterminal⟩
  have hnull : μ {γ | ¬ good γ} = 0 := by
    rw [← ae_iff]
    exact hgoodAE
  have hevent : 0 < μ event := by
    exact interior_event_pos T hT y
  have hnonempty : (event \ {γ | ¬ good γ}).Nonempty := by
    exact MeasureTheory.nonempty_of_measure_ne_zero
      (by
        rw [show μ (event \ {γ | ¬ good γ}) = μ event by
          apply measure_sdiff_null'
          exact measure_mono_null Set.inter_subset_right hnull]
        exact ne_of_gt hevent)
  rcases hnonempty with ⟨γ, hγevent, hγgood⟩
  have hgood : good γ := by
    by_contra h
    exact hγgood (by simpa using h)
  change
    FullPath.trajectory γ ((T / 2 : NNReal) : ℝ) =
        f (FullPath.initialState γ) (FullPath.terminalState γ) ∧
      FullPath.initialState γ = State.zero ∧
      FullPath.trajectory γ (T : ℝ) = FullPath.terminalState γ at hgood
  have hsample : FullPath.sampleAt time γ = γy := by
    simpa [event] using hγevent
  have hsampleAt (i : Fin 3) :
      FullPath.trajectory γ (time i) = Trajectory.stateAt γy i := by
    have h := congrFun (congrArg Trajectory.stateAt hsample) i
    simpa only [FullPath.sampleAt, Trajectory.stateAt_ofFn] using h
  have hmiddle :
      FullPath.trajectory γ ((T / 2 : NNReal) : ℝ) = y := by
    simpa [time, γy] using hsampleAt (1 : Fin 3)
  have hend : FullPath.trajectory γ (T : ℝ) = State.zero := by
    simpa [time, γy] using hsampleAt (2 : Fin 3)
  have hterminal : FullPath.terminalState γ = State.zero :=
    hgood.2.2.symm.trans hend
  rw [hgood.2.1, hterminal] at hgood
  exact hgood.1.symm.trans hmiddle

/-- **The real-time state at the window interior is not almost surely a
function of the path's initial and terminal states.** -/
theorem trajectory_interior_not_ae_endpointFunction
    (T : NNReal) (hT : 0 < T) :
    ¬ ∃ f : State → State → State,
      (fun γ => FullPath.trajectory γ ((T / 2 : NNReal) : ℝ))
        =ᵐ[finiteGenerator.pathLawFrom T State.zero]
        (fun γ => f (FullPath.initialState γ) (FullPath.terminalState γ)) := by
  rintro ⟨f, hf⟩
  have hzero : f State.zero State.zero = State.zero :=
    ae_endpoint_pair_value T hT State.zero f hf
  have hone : f State.zero State.zero = State.one :=
    ae_endpoint_pair_value T hT State.one f hf
  have : State.zero = State.one := hzero.symm.trans hone
  cases this

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
