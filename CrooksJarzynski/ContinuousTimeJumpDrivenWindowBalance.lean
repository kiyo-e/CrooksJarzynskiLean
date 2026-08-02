/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenBoundary

/-!
# Window balance from finite-state Gibbs detailed balance

This module normalizes the equilibrium path measure, identifies it with the
Gibbs mixture of the fixed-initial `pathLawFrom` laws, and prepares the final
transport to endpoint-marked window measures.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Normalized finite-state Gibbs weight relative to counting measure. -/
noncomputable def finiteGibbsWeight
    (β : ℝ) (energy : Ω → ℝ) (x : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-β * energy x) / finitePartitionFunction β energy)

/-- The finite-state partition function is strictly positive on a nonempty
state space. -/
theorem finitePartitionFunction_pos [Nonempty Ω]
    (β : ℝ) (energy : Ω → ℝ) :
    0 < finitePartitionFunction β energy := by
  classical
  unfold finitePartitionFunction
  apply Finset.sum_pos'
  · intro x _
    exact (Real.exp_pos (-β * energy x)).le
  · let x : Ω := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, Real.exp_pos (-β * energy x)⟩

/-- The normalized Gibbs weights satisfy the same division-free detailed
balance identity as the unnormalized Boltzmann weights. -/
theorem finiteGibbsWeight_detailedBalance [Nonempty Ω]
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    G.IsDetailedBalanceWeight (finiteGibbsWeight β energy) := by
  intro x y
  have hZ : 0 < finitePartitionFunction β energy :=
    finitePartitionFunction_pos β energy
  rw [finiteGibbsWeight, finiteGibbsWeight,
    ENNReal.ofReal_div_of_pos hZ,
    ENNReal.ofReal_div_of_pos hZ,
    ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  calc
    (ENNReal.ofReal (finitePartitionFunction β energy))⁻¹ *
          ENNReal.ofReal (Real.exp (-β * energy x)) *
        (G.jumpRate x y : ℝ≥0∞) =
      (ENNReal.ofReal (finitePartitionFunction β energy))⁻¹ *
        (ENNReal.ofReal (Real.exp (-β * energy x)) *
          (G.jumpRate x y : ℝ≥0∞)) := by ac_rfl
    _ = (ENNReal.ofReal (finitePartitionFunction β energy))⁻¹ *
        (ENNReal.ofReal (Real.exp (-β * energy y)) *
          (G.jumpRate y x : ℝ≥0∞)) := by
      rw [hbalance x y]
    _ = (ENNReal.ofReal (finitePartitionFunction β energy))⁻¹ *
          ENNReal.ofReal (Real.exp (-β * energy y)) *
        (G.jumpRate y x : ℝ≥0∞) := by ac_rfl

/-- The counting-measure Gibbs state is the finite sum of its normalized
singleton masses. -/
theorem gibbsMeasure_count_eq_sum_smul_dirac
    (β : ℝ) (energy : Ω → ℝ) :
    Gibbs.measure (Measure.count : Measure Ω) β energy =
      Measure.sum (fun x : Ω =>
        finiteGibbsWeight β energy x • Measure.dirac x) := by
  unfold Gibbs.measure Measure.tilted finiteGibbsWeight
  rw [Measure.count_withDensity]
  congr 1
  funext x
  congr 1
  change
    (∫ y, Real.exp (-β * energy y) ∂(Measure.count : Measure Ω)) =
      finitePartitionFunction β energy
  exact partitionFunction_count_eq β energy

/-- Normalized equilibrium full-path law constructed as a mixture of the actual
fixed-initial path laws. -/
noncomputable def gibbsPathLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) : Measure (FullPath Ω) :=
  Measure.sum (fun x : Ω =>
    finiteGibbsWeight β energy x • G.pathLawFrom T x)

/-- The Gibbs mixture of `pathLawFrom` laws is exactly the normalized weighted
all-sector law. -/
theorem gibbsPathLaw_eq_weightedFullPathLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) :
    G.gibbsPathLaw T β energy =
      G.weightedFullPathLaw T (finiteGibbsWeight β energy) := by
  simpa [gibbsPathLaw, weightedFullPathLaw, weightedSectorLaw] using
    G.sum_smul_pathLawFrom T (finiteGibbsWeight β energy)

/-- Instantaneous Gibbs detailed balance makes the normalized Gibbs path law
invariant under complete-path reversal. -/
theorem map_gibbsPathLaw_reverse [Nonempty Ω]
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    (G.gibbsPathLaw T β energy).map FullPath.reverse =
      G.gibbsPathLaw T β energy := by
  rw [G.gibbsPathLaw_eq_weightedFullPathLaw T β energy]
  exact G.map_weightedFullPathLaw_reverse T
    (finiteGibbsWeight β energy)
    (G.finiteGibbsWeight_detailedBalance β energy hbalance)

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
