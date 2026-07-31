/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricJarzynski
import CrooksJarzynski.ContinuousTimeJumpTwoStateFixedInitial
import CrooksJarzynski.MeasureProtocolSecondLaw

/-!
# Thermodynamic interpretation of the asymmetric two-state chain

This module identifies the asymmetric normalized jump example with an explicit
finite-state equilibrium/quench model.  It supplies a conservative generator,
its reversible Gibbs distribution, energy landscapes, partition functions, and
the resulting free-energy difference.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- The time-homogeneous off-diagonal rates of the asymmetric chain, viewed as
real numbers. -/
def physicalJumpRate : State → State → ℝ
  | .zero, .one => 2
  | .one, .zero => 1
  | _, _ => 0

/-- The state-dependent escape rate of the asymmetric chain. -/
def physicalEscapeRate : State → ℝ
  | .zero => 2
  | .one => 1

/-- The conservative generator associated with `physicalJumpRate`. -/
def physicalGenerator (x y : State) : ℝ :=
  if y = x then -physicalEscapeRate x else physicalJumpRate x y

/-- The segmentwise rates used by the path-density construction are exactly the
rates of the time-homogeneous generator. -/
theorem jumpRate_eq_physicalJumpRate {n : ℕ} (i : Fin n) (x y : State) :
    (jumpRate i x y : ℝ) = physicalJumpRate x y := by
  cases x <;> cases y <;> rfl

/-- The segmentwise escape rates are exactly the diagonal escape rates of the
time-homogeneous generator. -/
theorem escapeRate_eq_physicalEscapeRate {n : ℕ} (i : Fin (n + 1))
    (x : State) :
    (escapeRate i x : ℝ) = physicalEscapeRate x := by
  cases x <;> rfl

/-- Every row of the asymmetric generator sums to zero. -/
theorem physicalGenerator_row_sum (x : State) :
    ∑ y : State, physicalGenerator x y = 0 := by
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases x <;>
    simp [physicalGenerator, physicalEscapeRate, physicalJumpRate]

/-- The equilibrium probabilities selected by the asymmetric rates. -/
noncomputable def equilibriumProbability : State → ℝ
  | .zero => 1 / 3
  | .one => 2 / 3

/-- The equilibrium probabilities are normalized. -/
theorem sum_equilibriumProbability :
    ∑ x : State, equilibriumProbability x = 1 := by
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  norm_num [equilibriumProbability]

/-- The asymmetric rates satisfy detailed balance with respect to the explicit
equilibrium distribution. -/
theorem physical_detailedBalance (x y : State) :
    equilibriumProbability x * physicalJumpRate x y =
      equilibriumProbability y * physicalJumpRate y x := by
  cases x <;> cases y <;>
    norm_num [equilibriumProbability, physicalJumpRate]

/-- Detailed balance implies stationarity for the conservative generator. -/
theorem equilibriumProbability_stationary (y : State) :
    ∑ x : State, equilibriumProbability x * physicalGenerator x y = 0 := by
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases y <;>
    simp [equilibriumProbability, physicalGenerator, physicalEscapeRate,
      physicalJumpRate] <;>
    norm_num

/-- The inverse temperature used by the explicit thermodynamic model. -/
def thermodynamicBeta : ℝ := 1

/-- Initial energy landscape.  Its Boltzmann weights are `1` and `2`. -/
noncomputable def initialEnergy : State → ℝ
  | .zero => 0
  | .one => -Real.log 2

/-- Final energy landscape after the quench.  Both Boltzmann weights are `3`. -/
noncomputable def finalEnergy : State → ℝ :=
  fun _ => -Real.log 3

/-- Finite-state canonical partition function at `β = 1`. -/
noncomputable def finitePartitionFunction (energy : State → ℝ) : ℝ :=
  ∑ x : State, Real.exp (-energy x)

/-- The initial partition function is three. -/
theorem initial_partitionFunction :
    finitePartitionFunction initialEnergy = 3 := by
  unfold finitePartitionFunction
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  norm_num [initialEnergy,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The final partition function is six. -/
theorem final_partitionFunction :
    finitePartitionFunction finalEnergy = 6 := by
  unfold finitePartitionFunction
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  norm_num [finalEnergy,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- The explicit equilibrium probabilities are the normalized initial
Boltzmann weights. -/
theorem equilibriumProbability_eq_gibbs (x : State) :
    equilibriumProbability x =
      Real.exp (-initialEnergy x) /
        finitePartitionFunction initialEnergy := by
  rw [initial_partitionFunction]
  cases x <;>
    norm_num [equilibriumProbability, initialEnergy,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The final Gibbs distribution is uniform. -/
theorem final_gibbs_probability (x : State) :
    Real.exp (-finalEnergy x) / finitePartitionFunction finalEnergy = 1 / 2 := by
  rw [final_partitionFunction]
  cases x <;>
    norm_num [finalEnergy, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- Helmholtz free energy at the fixed inverse temperature `β = 1`. -/
noncomputable def finiteFreeEnergy (energy : State → ℝ) : ℝ :=
  -Real.log (finitePartitionFunction energy)

/-- The free-energy change of the final quench. -/
noncomputable def physicalDeltaFreeEnergy : ℝ :=
  finiteFreeEnergy finalEnergy - finiteFreeEnergy initialEnergy

/-- The explicit free-energy change is `-log 2`. -/
theorem physicalDeltaFreeEnergy_eq :
    physicalDeltaFreeEnergy = -Real.log 2 := by
  unfold physicalDeltaFreeEnergy finiteFreeEnergy
  rw [initial_partitionFunction, final_partitionFunction,
    show (6 : ℝ) = 3 * 2 by norm_num,
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Exponentiating the negative free-energy change gives the factor two used by
the Crooks relation. -/
theorem exp_neg_physicalDeltaFreeEnergy :
    Real.exp (-physicalDeltaFreeEnergy) = 2 := by
  rw [physicalDeltaFreeEnergy_eq]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The ENNReal free-energy factor in the path theorem is exactly
`exp (-β ΔF)` for the explicit thermodynamic model. -/
theorem freeEnergyWeight_eq_exp_delta :
    freeEnergyWeight =
      ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * physicalDeltaFreeEnergy)) := by
  rw [thermodynamicBeta]
  rw [show (-(1 : ℝ) * physicalDeltaFreeEnergy) =
      -physicalDeltaFreeEnergy by ring,
    exp_neg_physicalDeltaFreeEnergy]
  norm_num [freeEnergyWeight]

/-- The endpoint density used in the path law is twice the Gibbs probability,
because the state-sequence reference starts from the uniform law. -/
theorem gibbsInitialWeight_eq_probability_density (x : State) :
    gibbsInitialWeight x =
      ENNReal.ofReal (2 * equilibriumProbability x) := by
  cases x
  · simp only [gibbsInitialWeight, equilibriumProbability]
    rw [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num [ENNReal.ofReal_ofNat]
  · simp only [gibbsInitialWeight, equilibriumProbability]
    rw [show (2 : ℝ) * (2 / 3) = 4 / 3 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num [ENNReal.ofReal_ofNat]

/-- The final endpoint density is twice the final uniform Gibbs probability,
again relative to the uniform state reference. -/
theorem gibbsFinalWeight_eq_probability_density (x : State) :
    gibbsFinalWeight x = ENNReal.ofReal (2 * (1 / 2 : ℝ)) := by
  cases x <;> norm_num [gibbsFinalWeight]

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
