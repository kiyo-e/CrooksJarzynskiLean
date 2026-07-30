/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateNormalization
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Generator and time-`T` marginals of the two-state chain

The jump-count marginal of the normalized path law is Poisson.  Starting from
a fixed state, the terminal state is therefore obtained by applying the
deterministic flip once for every Poisson jump.  Its two transition
probabilities are `(1 ± exp (-2T)) / 2`.

The same formula is derived independently by diagonalizing the conservative
generator and computing its matrix exponential.  This identifies the path-law
marginal with `exp (TQ)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- Encode the two states as the two real signs. -/
def stateSign : State → ℝ
  | .zero => 1
  | .one => -1

@[simp]
theorem stateSign_flip (x : State) :
    stateSign (flip x) = -stateSign x := by
  cases x <;> norm_num [stateSign, flip]

theorem stateSign_iterateFlip (n : ℕ) (x : State) :
    stateSign (iterateFlip n x) = (-1 : ℝ) ^ n * stateSign x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterateFlip_succ, stateSign_flip, ih, pow_succ]
      ring

private theorem indicator_iterateFlip_eq (n : ℕ) (x y : State) :
    (if iterateFlip n x = y then (1 : ℝ) else 0) =
      (1 + stateSign x * stateSign y * (-1 : ℝ) ^ n) / 2 := by
  have hsign := stateSign_iterateFlip n x
  by_cases hxy : iterateFlip n x = y
  · subst y
    rw [if_pos rfl]
    have hprod : stateSign x * stateSign (iterateFlip n x) *
        (-1 : ℝ) ^ n = 1 := by
      rw [hsign]
      have hx2 : stateSign x ^ 2 = 1 := by
        cases x <;> norm_num [stateSign]
      have hp : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
        rw [← pow_mul]
        norm_num
      calc
        stateSign x * ((-1 : ℝ) ^ n * stateSign x) * (-1 : ℝ) ^ n =
            stateSign x ^ 2 * (((-1 : ℝ) ^ n) ^ 2) := by ring
        _ = 1 := by rw [hx2, hp]; norm_num
    rw [hprod]
    norm_num
  · rw [if_neg hxy]
    have hne : y = flip (iterateFlip n x) := by
      cases x' : iterateFlip n x <;> cases y <;> simp_all [flip]
    rw [hne, stateSign_flip, hsign]
    have hx2 : stateSign x ^ 2 = 1 := by
      cases x <;> norm_num [stateSign]
    have hp : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
    nlinarith

private theorem integrable_paritySign (T : NNReal) :
    Integrable (fun n : ℕ => (-1 : ℝ) ^ n) (poissonMeasure T) := by
  apply Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
  filter_upwards [] with n
  rw [Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow]

/-- The parity expectation of a Poisson jump count is `exp (-2T)`. -/
theorem integral_paritySign_poisson (T : NNReal) :
    ∫ n : ℕ, (-1 : ℝ) ^ n ∂poissonMeasure T =
      Real.exp (-2 * (T : ℝ)) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  calc
    (∑' n : ℕ,
        (Real.exp (-(T : ℝ)) * (T : ℝ) ^ n / (n.factorial : ℝ)) •
          ((-1 : ℝ) ^ n)) =
        Real.exp (-(T : ℝ)) *
          ∑' n : ℕ, (-(T : ℝ)) ^ n / (n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      simp only [smul_eq_mul, mul_div_assoc]
      rw [show -(T : ℝ) = (-1 : ℝ) * (T : ℝ) by ring, mul_pow]
      ring
    _ = Real.exp (-(T : ℝ)) * Real.exp (-(T : ℝ)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (-(T : ℝ))).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp (-2 * (T : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The conditional time-`T` state law obtained by flipping the initial state
once per Poisson jump. -/
noncomputable def conditionalTerminalLaw (T : NNReal) (x : State) :
    Measure State :=
  (poissonMeasure T).map (fun n => iterateFlip n x)

noncomputable instance instIsProbabilityMeasureConditionalTerminalLaw
    (T : NNReal) (x : State) :
    IsProbabilityMeasure (conditionalTerminalLaw T x) := by
  unfold conditionalTerminalLaw
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- The number of jumps in a full finite-jump path. -/
def FullPath.jumpCount : FullPath State → ℕ
  | ⟨n, _⟩ => n

@[fun_prop]
theorem FullPath.measurable_jumpCount : Measurable FullPath.jumpCount := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun _ : JumpPath State n => n) ⁻¹' s)
  by_cases hn : n ∈ s <;> simp [hn]

/-- The jump-count marginal of the constructed full path law is Poisson. -/
theorem map_pathLaw_jumpCount (T : NNReal) :
    (pathLaw T).map FullPath.jumpCount = poissonMeasure T := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply FullPath.measurable_jumpCount
    (MeasurableSet.singleton n)]
  unfold pathLaw FullPath.measure
  rw [Measure.sum_apply _ (MeasurableSet.preimage
    (MeasurableSet.singleton n) FullPath.measurable_jumpCount)]
  have hlift : ∀ i : ℕ,
      FullPath.liftMeasure i (sectorLaw T i)
          (FullPath.jumpCount ⁻¹' ({n} : Set ℕ)) =
        if i = n then sectorLaw T i Set.univ else 0 := by
    intro i
    unfold FullPath.liftMeasure
    rw [Measure.map_apply (FullPath.measurable_mk i)
      (MeasurableSet.preimage (MeasurableSet.singleton n)
        FullPath.measurable_jumpCount)]
    have hpre :
        Sigma.mk i ⁻¹' FullPath.jumpCount ⁻¹' ({n} : Set ℕ) =
          if i = n then Set.univ else ∅ := by
      ext γ
      simp [FullPath.jumpCount]
    rw [hpre]
    by_cases hin : i = n
    · simp [hin]
    · simp [hin]
  simp_rw [hlift]
  rw [tsum_ite_eq n, sectorLaw_univ_eq_poisson]

/-- Reading the deterministic alternating state from the jump count turns the
full path law into the conditional time-`T` state marginal. -/
theorem map_pathLaw_iterateFlip_jumpCount (T : NNReal) (x : State) :
    (pathLaw T).map
        (fun γ => iterateFlip (FullPath.jumpCount γ) x) =
      conditionalTerminalLaw T x := by
  unfold conditionalTerminalLaw
  rw [← map_pathLaw_jumpCount T]
  simpa [Function.comp_def] using
    (Measure.map_map
      (μ := pathLaw T)
      (g := fun n : ℕ => iterateFlip n x)
      (f := FullPath.jumpCount)
      Measurable.of_discrete FullPath.measurable_jumpCount).symm

/-- The fixed-initial-state time-`T` marginal in a sign-symmetric form. -/
theorem conditionalTerminalLaw_real_singleton (T : NNReal) (x y : State) :
    (conditionalTerminalLaw T x).real {y} =
      (1 + stateSign x * stateSign y *
        Real.exp (-2 * (T : ℝ))) / 2 := by
  classical
  unfold conditionalTerminalLaw
  rw [measureReal_def, Measure.map_apply Measurable.of_discrete
    (MeasurableSet.singleton y)]
  change (poissonMeasure T).real
      ((fun n => iterateFlip n x) ⁻¹' ({y} : Set State)) = _
  rw [← integral_indicator_one (MeasurableSet.preimage
    (MeasurableSet.singleton y) Measurable.of_discrete)]
  have hindicator :
      ((fun n => iterateFlip n x) ⁻¹' ({y} : Set State)).indicator
          (1 : ℕ → ℝ) =
        fun n => (1 + stateSign x * stateSign y * (-1 : ℝ) ^ n) / 2 := by
    funext n
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact indicator_iterateFlip_eq n x y
  rw [hindicator]
  have hparity := integrable_paritySign T
  have hscaled :
      Integrable
        (fun n : ℕ => stateSign x * stateSign y * (-1 : ℝ) ^ n)
        (poissonMeasure T) :=
    hparity.const_mul _
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_add (integrable_const 1) hscaled,
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_paritySign_poisson]

/-- Explicit stay/switch form of the time-`T` marginal. -/
theorem conditionalTerminalLaw_real_singleton_eq (T : NNReal) (x y : State) :
    (conditionalTerminalLaw T x).real {y} =
      if x = y then (1 + Real.exp (-2 * (T : ℝ))) / 2
      else (1 - Real.exp (-2 * (T : ℝ))) / 2 := by
  rw [conditionalTerminalLaw_real_singleton]
  cases x <;> cases y <;> simp [stateSign] <;> ring

private theorem state_univ :
    (Finset.univ : Finset State) = {.zero, .one} := by decide

/-- Eigenvector matrix for the conservative generator. -/
def eigenbasisMatrix : Matrix State State ℝ
  | .zero, .zero => 1
  | .zero, .one => 1
  | .one, .zero => 1
  | .one, .one => -1

noncomputable def eigenbasisInverse : Matrix State State ℝ
  | .zero, .zero => 1 / 2
  | .zero, .one => 1 / 2
  | .one, .zero => 1 / 2
  | .one, .one => -1 / 2

theorem eigenbasis_mul_inverse :
    eigenbasisMatrix * eigenbasisInverse = 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.mul_apply, state_univ, eigenbasisMatrix,
      eigenbasisInverse] <;>
    norm_num

noncomputable def eigenbasisUnit : (Matrix State State ℝ)ˣ :=
  Units.mkOfMulEqOne eigenbasisMatrix eigenbasisInverse
    eigenbasis_mul_inverse

@[simp]
theorem coe_eigenbasisUnit :
    (eigenbasisUnit : Matrix State State ℝ) = eigenbasisMatrix :=
  rfl

@[simp]
theorem coe_eigenbasisUnit_inv :
    (↑(eigenbasisUnit⁻¹) : Matrix State State ℝ) = eigenbasisInverse :=
  rfl

def generatorEigenvalue (t : ℝ) : State → ℝ
  | .zero => 0
  | .one => -2 * t

theorem smul_generator_diagonalization (t : ℝ) :
    t • (show Matrix State State ℝ from fun x y => generator x y) =
      eigenbasisMatrix * Matrix.diagonal (generatorEigenvalue t) *
        eigenbasisInverse := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.mul_apply, state_univ, eigenbasisMatrix,
      eigenbasisInverse, generatorEigenvalue, generator, generatorRate, flip] <;>
    ring

noncomputable def transitionProbability (t : ℝ) (x y : State) : ℝ :=
  if x = y then (1 + Real.exp (-2 * t)) / 2
  else (1 - Real.exp (-2 * t)) / 2

/-- The exponential of the conservative generator has the expected explicit
two-state transition probabilities. -/
theorem exp_smul_generator_apply (t : ℝ) (x y : State) :
    NormedSpace.exp
        (t • (show Matrix State State ℝ from fun x y => generator x y)) x y =
      transitionProbability t x y := by
  rw [smul_generator_diagonalization]
  change NormedSpace.exp
      ((↑eigenbasisUnit : Matrix State State ℝ) *
        Matrix.diagonal (generatorEigenvalue t) *
        (↑(eigenbasisUnit⁻¹) : Matrix State State ℝ)) x y =
    transitionProbability t x y
  rw [Matrix.exp_units_conj eigenbasisUnit
    (Matrix.diagonal (generatorEigenvalue t))]
  rw [Matrix.exp_diagonal]
  simp only [coe_eigenbasisUnit, coe_eigenbasisUnit_inv]
  cases x <;> cases y <;>
    simp [Matrix.mul_apply, state_univ, eigenbasisMatrix,
      eigenbasisInverse, generatorEigenvalue, transitionProbability] <;>
    rw [Real.exp_eq_exp_ℝ] <;>
    ring

/-- The fixed-initial-state marginal extracted from the path construction is
exactly the corresponding entry of `exp (TQ)`. -/
theorem conditionalTerminalLaw_eq_exp_generator
    (T : NNReal) (x y : State) :
    (conditionalTerminalLaw T x).real {y} =
      NormedSpace.exp
        ((T : ℝ) •
          (show Matrix State State ℝ from fun x y => generator x y)) x y := by
  rw [conditionalTerminalLaw_real_singleton_eq,
    exp_smul_generator_apply]
  rfl

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
