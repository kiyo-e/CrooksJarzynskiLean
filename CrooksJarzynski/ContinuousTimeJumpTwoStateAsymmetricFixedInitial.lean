/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricJarzynski
import CrooksJarzynski.ContinuousTimeJumpTwoStateFixedInitial
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Fixed-initial laws for the asymmetric two-state chain

This module constructs the normalized path law of the asymmetric two-state
chain from a prescribed initial state. It also records the explicit transition
matrix and identifies it with the exponential of the physical generator.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- Density relative to the uniform initial-state reference that fixes the
initial state to `x`. The factor two cancels the reference mass `1 / 2`. -/
noncomputable def fixedInitialWeight (x : State) : State → ℝ≥0∞ :=
  fun s => if s = x then 2 else 0

/-- The asymmetric CTMC law in one jump-count sector, started from `x`. -/
noncomputable def asymmetricSectorLawFrom
    (T : NNReal) (x : State) (n : ℕ) : Measure (JumpPath State n) :=
  pathMeasure (rawSectorReference T n)
    (JumpPath.rateDensity (fixedInitialWeight x) escapeRate jumpRate)

/-- The mass of a fixed-initial asymmetric sector is its analytic sector
mass. -/
theorem asymmetricSectorLawFrom_univ
    (T : NNReal) (x : State) (n : ℕ) :
    asymmetricSectorLawFrom T x n Set.univ = sectorMass T x n := by
  unfold asymmetricSectorLawFrom pathMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_rateDensity_rawSectorReference (fixedInitialWeight x) T n]
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases x <;> simp [fixedInitialWeight]
  all_goals
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- The fixed-initial asymmetric sector law is concentrated on paths starting
at the prescribed state. -/
theorem asymmetricSectorLawFrom_ae_initialState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂asymmetricSectorLawFrom T x n, γ.1 0 = x := by
  have hdensity :
      Measurable
        (JumpPath.rateDensity (fixedInitialWeight x)
          (escapeRate (n := n)) (jumpRate (n := n))) := by
    have hweight : Measurable (fixedInitialWeight x) :=
      Measurable.of_discrete
    unfold JumpPath.rateDensity JumpPath.density
      JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
      escapeRate jumpRate
    fun_prop
  unfold asymmetricSectorLawFrom pathMeasure
  rw [ae_withDensity_iff hdensity]
  filter_upwards [] with γ hγ
  by_contra hne
  apply hγ
  unfold JumpPath.rateDensity JumpPath.density fixedInitialWeight
  simp [hne]

/-- The fixed-initial asymmetric sector law has terminal state obtained by
flipping once for every jump. -/
theorem asymmetricSectorLawFrom_ae_terminalState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂asymmetricSectorLawFrom T x n,
      γ.1 (Fin.last n) = iterateFlip n x := by
  have halternates :
      ∀ᵐ γ ∂asymmetricSectorLawFrom T x n, Alternates γ.1 := by
    unfold asymmetricSectorLawFrom pathMeasure
    apply ae_iff.mpr
    exact
      (MeasureTheory.withDensity_absolutelyContinuous
        (rawSectorReference T n)
        (JumpPath.rateDensity (fixedInitialWeight x) escapeRate jumpRate))
        (ae_iff.mp (by
          rw [← sectorReference_eq_rawSectorReference]
          exact TwoState.sectorReference_ae_alternates T n))
  filter_upwards [asymmetricSectorLawFrom_ae_initialState T x n,
    halternates] with γ hinitial halternates
  rw [Alternates.apply_eq_iterateFlip halternates (Fin.last n), hinitial]
  rfl

/-- The normalized full asymmetric path law started from `x`. -/
noncomputable def asymmetricPathLawFrom
    (T : NNReal) (x : State) : Measure (FullPath State) :=
  FullPath.measure (asymmetricSectorLawFrom T x)

/-- The fixed-initial asymmetric sector masses sum to one. -/
theorem tsum_asymmetricSectorLawFrom_univ (T : NNReal) (x : State) :
    ∑' n, asymmetricSectorLawFrom T x n Set.univ = 1 := by
  simp_rw [asymmetricSectorLawFrom_univ]
  exact tsum_sectorMass T x

noncomputable instance instIsProbabilityMeasureAsymmetricPathLawFrom
    (T : NNReal) (x : State) :
    IsProbabilityMeasure (asymmetricPathLawFrom T x) := by
  unfold asymmetricPathLawFrom
  exact FullPath.isProbabilityMeasure_measure
    (asymmetricSectorLawFrom T x)
    (tsum_asymmetricSectorLawFrom_univ T x)

private theorem asymmetricLiftMeasure_ae_terminalState
    (T : NNReal) (x : State) (n : ℕ) :
    FullPath.terminalState =ᵐ[
      FullPath.liftMeasure n (asymmetricSectorLawFrom T x n)]
      fun γ => iterateFlip (FullPath.jumpCount γ) x := by
  have heq : MeasurableSet {γ : FullPath State |
      FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x} :=
    (FullPath.measurable_terminalState.eq
      (((Measurable.of_discrete :
          Measurable (fun n : ℕ => iterateFlip n x)).comp
        FullPath.measurable_jumpCount))).setOf
  change ∀ᵐ γ ∂Measure.map (Sigma.mk n)
      (asymmetricSectorLawFrom T x n),
    FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable heq]
  exact
    (asymmetricSectorLawFrom_ae_terminalState T x n).mono fun γ hγ => by
      simpa [FullPath.terminalState, FullPath.jumpCount] using hγ

/-- Under the full fixed-initial asymmetric path law, the terminal state is
the initial state flipped once per recorded jump. -/
theorem asymmetricPathLawFrom_ae_terminalState
    (T : NNReal) (x : State) :
    FullPath.terminalState =ᵐ[asymmetricPathLawFrom T x]
      fun γ => iterateFlip (FullPath.jumpCount γ) x := by
  have heq : MeasurableSet {γ : FullPath State |
      FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x} :=
    (FullPath.measurable_terminalState.eq
      (((Measurable.of_discrete :
          Measurable (fun n : ℕ => iterateFlip n x)).comp
        FullPath.measurable_jumpCount))).setOf
  have hbad : MeasurableSet {γ : FullPath State |
      ¬ FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x} := by
    change MeasurableSet ({γ : FullPath State |
      FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x}ᶜ)
    exact heq.compl
  apply ae_iff.mpr
  unfold asymmetricPathLawFrom FullPath.measure
  rw [Measure.sum_apply _ hbad, ENNReal.tsum_eq_zero]
  intro n
  exact ae_iff.mp (asymmetricLiftMeasure_ae_terminalState T x n)

/-- The terminal-state marginal is the sum of exactly those sector masses
whose jump parity carries `x` to `y`. -/
theorem map_asymmetricPathLawFrom_terminalState_apply
    (T : NNReal) (x y : State) :
    (asymmetricPathLawFrom T x).map FullPath.terminalState {y} =
      ∑' n, if iterateFlip n x = y then sectorMass T x n else 0 := by
  rw [Measure.map_apply FullPath.measurable_terminalState
    (MeasurableSet.singleton y)]
  unfold asymmetricPathLawFrom FullPath.measure
  rw [Measure.sum_apply _ (MeasurableSet.preimage
    (MeasurableSet.singleton y) FullPath.measurable_terminalState)]
  apply tsum_congr
  intro n
  unfold FullPath.liftMeasure
  rw [Measure.map_apply (FullPath.measurable_mk n)
    (MeasurableSet.preimage (MeasurableSet.singleton y)
      FullPath.measurable_terminalState)]
  by_cases hxy : iterateFlip n x = y
  · have hset :
        (Sigma.mk n ⁻¹' FullPath.terminalState ⁻¹' ({y} : Set State)) =ᵐ[
          asymmetricSectorLawFrom T x n] Set.univ := by
      filter_upwards
        [asymmetricSectorLawFrom_ae_terminalState T x n] with γ hγ
      apply propext
      change γ.1 (Fin.last n) = y ↔ True
      simp [hγ, hxy]
    rw [measure_congr hset, asymmetricSectorLawFrom_univ, if_pos hxy]
  · have hset :
        (Sigma.mk n ⁻¹' FullPath.terminalState ⁻¹' ({y} : Set State)) =ᵐ[
          asymmetricSectorLawFrom T x n] (∅ : Set (JumpPath State n)) := by
      filter_upwards
        [asymmetricSectorLawFrom_ae_terminalState T x n] with γ hγ
      apply propext
      change γ.1 (Fin.last n) = y ↔ False
      simp [hγ, hxy]
    rw [measure_congr hset, if_neg hxy]
    simp

/-! ### Explicit transition matrix -/

/-- The explicit transition probabilities of the asymmetric chain. -/
noncomputable def asymmetricTransitionProbability
    (t : ℝ) : State → State → ℝ
  | .zero, .zero => 1 / 3 + 2 / 3 * Real.exp (-3 * t)
  | .zero, .one => 2 / 3 - 2 / 3 * Real.exp (-3 * t)
  | .one, .zero => 1 / 3 - 1 / 3 * Real.exp (-3 * t)
  | .one, .one => 2 / 3 + 1 / 3 * Real.exp (-3 * t)

/-- Each row of the explicit transition matrix sums to one. -/
theorem asymmetricTransitionProbability_row_sum (t : ℝ) (x : State) :
    ∑ y : State, asymmetricTransitionProbability t x y = 1 := by
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases x <;> simp [asymmetricTransitionProbability] <;> ring

/-- At time zero the explicit transition matrix is the identity. -/
theorem asymmetricTransitionProbability_zero (x y : State) :
    asymmetricTransitionProbability 0 x y = if x = y then 1 else 0 := by
  cases x <;> cases y <;>
    simp [asymmetricTransitionProbability] <;> norm_num

/-- The explicit transition probabilities are nonnegative at nonnegative
times. -/
theorem asymmetricTransitionProbability_nonneg
    (T : NNReal) (x y : State) :
    0 ≤ asymmetricTransitionProbability (T : ℝ) x y := by
  have hexp0 : 0 < Real.exp (-3 * (T : ℝ)) := Real.exp_pos _
  have hexp1 : Real.exp (-3 * (T : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hT : 0 ≤ (T : ℝ) := T.2
    linarith
  cases x <;> cases y <;>
    simp only [asymmetricTransitionProbability] <;> nlinarith

/-- The explicit transition probabilities satisfy Chapman--Kolmogorov. -/
theorem asymmetricTransitionProbability_chapman_kolmogorov
    (S T : NNReal) (x y : State) :
    (∑ z : State,
      asymmetricTransitionProbability (S : ℝ) x z *
        asymmetricTransitionProbability (T : ℝ) z y) =
      asymmetricTransitionProbability ((S + T : NNReal) : ℝ) x y := by
  have hmul :
      Real.exp (-(3 * (S : ℝ))) * Real.exp (-(3 * (T : ℝ))) =
        Real.exp (-(3 * ((S : ℝ) + (T : ℝ)))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases x <;> cases y <;>
    norm_num [asymmetricTransitionProbability] <;> nlinarith [hmul]

/-- The physical conservative generator of the asymmetric chain. -/
def physicalGenerator : Matrix State State ℝ
  | .zero, .zero => -2
  | .zero, .one => 2
  | .one, .zero => 1
  | .one, .one => -1

def asymmetricEigenbasisMatrix : Matrix State State ℝ
  | .zero, .zero => 1
  | .zero, .one => 2
  | .one, .zero => 1
  | .one, .one => -1

noncomputable def asymmetricEigenbasisInverse : Matrix State State ℝ
  | .zero, .zero => 1 / 3
  | .zero, .one => 2 / 3
  | .one, .zero => 1 / 3
  | .one, .one => -1 / 3

theorem asymmetricEigenbasis_mul_inverse :
    asymmetricEigenbasisMatrix * asymmetricEigenbasisInverse = 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.mul_apply,
      show (Finset.univ : Finset State) = {.zero, .one} by decide,
      asymmetricEigenbasisMatrix,
      asymmetricEigenbasisInverse] <;>
    norm_num

noncomputable def asymmetricEigenbasisUnit :
    (Matrix State State ℝ)ˣ :=
  Units.mkOfMulEqOne asymmetricEigenbasisMatrix
    asymmetricEigenbasisInverse asymmetricEigenbasis_mul_inverse

@[simp]
theorem coe_asymmetricEigenbasisUnit :
    (asymmetricEigenbasisUnit : Matrix State State ℝ) =
      asymmetricEigenbasisMatrix :=
  rfl

@[simp]
theorem coe_asymmetricEigenbasisUnit_inv :
    (↑(asymmetricEigenbasisUnit⁻¹) : Matrix State State ℝ) =
      asymmetricEigenbasisInverse :=
  rfl

def asymmetricGeneratorEigenvalue (t : ℝ) : State → ℝ
  | .zero => 0
  | .one => -3 * t

theorem smul_physicalGenerator_diagonalization (t : ℝ) :
    t • physicalGenerator =
      asymmetricEigenbasisMatrix *
        Matrix.diagonal (asymmetricGeneratorEigenvalue t) *
          asymmetricEigenbasisInverse := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.mul_apply,
      show (Finset.univ : Finset State) = {.zero, .one} by decide,
      asymmetricEigenbasisMatrix,
      asymmetricEigenbasisInverse, asymmetricGeneratorEigenvalue,
      physicalGenerator] <;>
    ring

/-- The exponential of the physical generator agrees with the explicit
transition matrix. -/
theorem exp_smul_physicalGenerator_apply (t : ℝ) (x y : State) :
    NormedSpace.exp (t • physicalGenerator) x y =
      asymmetricTransitionProbability t x y := by
  rw [smul_physicalGenerator_diagonalization]
  change NormedSpace.exp
      ((↑asymmetricEigenbasisUnit : Matrix State State ℝ) *
        Matrix.diagonal (asymmetricGeneratorEigenvalue t) *
        (↑(asymmetricEigenbasisUnit⁻¹) : Matrix State State ℝ)) x y =
    asymmetricTransitionProbability t x y
  rw [Matrix.exp_units_conj asymmetricEigenbasisUnit
    (Matrix.diagonal (asymmetricGeneratorEigenvalue t))]
  rw [Matrix.exp_diagonal]
  simp only [coe_asymmetricEigenbasisUnit,
    coe_asymmetricEigenbasisUnit_inv]
  cases x <;> cases y <;>
    simp [Matrix.mul_apply,
      show (Finset.univ : Finset State) = {.zero, .one} by decide,
      asymmetricEigenbasisMatrix,
      asymmetricEigenbasisInverse, asymmetricGeneratorEigenvalue,
      asymmetricTransitionProbability] <;>
    rw [Real.exp_eq_exp_ℝ] <;>
    ring

/-- Once the parity-filtered sector sum is evaluated, the terminal-law
identity follows without any further measure-theoretic argument. -/
private theorem asymmetric_terminal_law_of_parity_tsum
    (T : NNReal) (x y : State)
    (hparity :
      (∑' n, if iterateFlip n x = y then sectorMass T x n else 0) =
        ENNReal.ofReal (asymmetricTransitionProbability (T : ℝ) x y)) :
    ((asymmetricPathLawFrom T x).map FullPath.terminalState).real {y} =
      asymmetricTransitionProbability (T : ℝ) x y := by
  change
    (((asymmetricPathLawFrom T x).map FullPath.terminalState {y}).toReal) =
      asymmetricTransitionProbability (T : ℝ) x y
  rw [map_asymmetricPathLawFrom_terminalState_apply, hparity,
    ENNReal.toReal_ofReal (asymmetricTransitionProbability_nonneg T x y)]

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
