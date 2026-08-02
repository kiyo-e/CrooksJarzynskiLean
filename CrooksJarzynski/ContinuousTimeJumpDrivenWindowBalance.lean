/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenStationary

/-!
# Window balance from finite-state Gibbs detailed balance

This module normalizes the equilibrium path measure, identifies it with the
Gibbs mixture of the fixed-initial `pathLawFrom` laws, and transports complete
path reversal to the endpoint-marked window measures used by the driven
protocol.
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

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
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

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
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

omit [DecidableEq Ω] in
/-- The counting-measure Gibbs state is the finite sum of its normalized
singleton masses. -/
theorem gibbsMeasure_count_eq_sum_smul_dirac
    (β : ℝ) (energy : Ω → ℝ) :
    Gibbs.measure (Measure.count : Measure Ω) β energy =
      Measure.sum (fun x : Ω =>
        finiteGibbsWeight β energy x • Measure.dirac x) := by
  unfold Gibbs.measure Measure.tilted finiteGibbsWeight
  rw [count_withDensity]
  congr 1
  funext x
  have hZ :
      (∫ y, Real.exp (-β * energy y) ∂(Measure.count : Measure Ω)) =
        finitePartitionFunction β energy := by
    simpa [Gibbs.partitionFunction] using
      (partitionFunction_count_eq (Ω := Ω) β energy)
  rw [hZ]

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

/-- Record a complete path together with its forward initial and terminal
endpoints. -/
def forwardWindowRecord (γ : FullPath Ω) :
    Ω × (Ω × FullPath Ω) :=
  (FullPath.initialState γ, (FullPath.terminalState γ, γ))

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
@[fun_prop]
theorem measurable_forwardWindowRecord :
    Measurable (forwardWindowRecord :
      FullPath Ω → Ω × (Ω × FullPath Ω)) :=
  FullPath.measurable_initialState.prodMk
    (FullPath.measurable_terminalState.prodMk measurable_id)

/-- Record the reverse-experiment output before its endpoint coordinates are
swapped into forward order. -/
def preReverseWindowRecord (γ : FullPath Ω) :
    Ω × (Ω × FullPath Ω) :=
  (FullPath.initialState γ,
    (FullPath.terminalState γ, FullPath.reverse γ))

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
@[fun_prop]
theorem measurable_preReverseWindowRecord :
    Measurable (preReverseWindowRecord :
      FullPath Ω → Ω × (Ω × FullPath Ω)) :=
  FullPath.measurable_initialState.prodMk
    (FullPath.measurable_terminalState.prodMk FullPath.measurable_reverse)

/-- Record the reverse experiment after swapping its two endpoint coordinates
into the forward orientation. -/
def reverseWindowRecord (γ : FullPath Ω) :
    Ω × (Ω × FullPath Ω) :=
  (FullPath.terminalState γ,
    (FullPath.initialState γ, FullPath.reverse γ))

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
@[fun_prop]
theorem measurable_reverseWindowRecord :
    Measurable (reverseWindowRecord :
      FullPath Ω → Ω × (Ω × FullPath Ω)) :=
  FullPath.measurable_terminalState.prodMk
    (FullPath.measurable_initialState.prodMk FullPath.measurable_reverse)

/-- The forward endpoint-marked joint law is the Gibbs full-path law pushed
through its endpoint record. -/
theorem compProd_forwardWindowKernel_eq_map_gibbsPathLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) :
    Gibbs.measure (Measure.count : Measure Ω) β energy ⊗ₘ
        G.forwardWindowKernel T =
      (G.gibbsPathLaw T β energy).map forwardWindowRecord := by
  ext s hs
  rw [gibbsMeasure_count_eq_sum_smul_dirac]
  rw [Measure.compProd_sum_left]
  rw [Measure.sum_apply _ hs]
  unfold gibbsPathLaw
  rw [Measure.map_apply measurable_forwardWindowRecord hs,
    Measure.sum_apply _ (hs.preimage measurable_forwardWindowRecord)]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply tsum_congr
  intro x
  rw [Measure.compProd_smul_left]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.dirac_compProd_apply hs, forwardWindowKernel_apply]
  rw [Measure.map_apply
    (μ := G.pathLawFrom T x)
    (f := fun γ => (FullPath.terminalState γ, γ))
    (FullPath.measurable_terminalState.prodMk measurable_id)
    (measurable_prodMk_left hs)]
  apply measure_congr
  filter_upwards [G.pathLawFrom_ae_initialState T x] with γ hγ
  change
    ((x, (FullPath.terminalState γ, γ)) ∈ s) =
      ((FullPath.initialState γ, (FullPath.terminalState γ, γ)) ∈ s)
  rw [hγ]

/-- Before endpoint swapping, the reverse-window joint law is the same Gibbs
full-path law pushed through the reverse-experiment record. -/
theorem compProd_reverseWindowKernel_eq_map_gibbsPathLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) :
    Gibbs.measure (Measure.count : Measure Ω) β energy ⊗ₘ
        G.reverseWindowKernel T =
      (G.gibbsPathLaw T β energy).map preReverseWindowRecord := by
  ext s hs
  rw [gibbsMeasure_count_eq_sum_smul_dirac]
  rw [Measure.compProd_sum_left]
  rw [Measure.sum_apply _ hs]
  unfold gibbsPathLaw
  rw [Measure.map_apply measurable_preReverseWindowRecord hs,
    Measure.sum_apply _ (hs.preimage measurable_preReverseWindowRecord)]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply tsum_congr
  intro x
  rw [Measure.compProd_smul_left]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.dirac_compProd_apply hs, reverseWindowKernel_apply]
  rw [Measure.map_apply
    (μ := G.pathLawFrom T x)
    (f := fun γ =>
      (FullPath.terminalState γ, FullPath.reverse γ))
    (FullPath.measurable_terminalState.prodMk FullPath.measurable_reverse)
    (measurable_prodMk_left hs)]
  apply measure_congr
  filter_upwards [G.pathLawFrom_ae_initialState T x] with γ hγ
  change
    ((x, (FullPath.terminalState γ, FullPath.reverse γ)) ∈ s) =
      ((FullPath.initialState γ,
        (FullPath.terminalState γ, FullPath.reverse γ)) ∈ s)
  rw [hγ]

/-- Swapping the reverse-experiment endpoints yields the reversed forward
endpoint record. -/
theorem map_compProd_reverseWindowKernel_swap
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) :
    (Gibbs.measure (Measure.count : Measure Ω) β energy ⊗ₘ
        G.reverseWindowKernel T).map
          (Marked.swapEndpointsEquiv
            (Ω := Ω) (Λ := FullPath Ω)) =
      (G.gibbsPathLaw T β energy).map reverseWindowRecord := by
  rw [G.compProd_reverseWindowKernel_eq_map_gibbsPathLaw T β energy]
  rw [Measure.map_map
    (Marked.swapEndpointsEquiv
      (Ω := Ω) (Λ := FullPath Ω)).measurable
    measurable_preReverseWindowRecord]
  congr 1

/-- Reversal invariance of the Gibbs full-path law identifies its forward and
reverse endpoint records. -/
theorem map_forwardWindowRecord_eq_map_reverseWindowRecord [Nonempty Ω]
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    (G.gibbsPathLaw T β energy).map forwardWindowRecord =
      (G.gibbsPathLaw T β energy).map reverseWindowRecord := by
  have hrecord :
      reverseWindowRecord (Ω := Ω) =
        forwardWindowRecord ∘ FullPath.reverse := by
    funext γ
    simp [reverseWindowRecord, forwardWindowRecord]
  rw [hrecord]
  calc
    (G.gibbsPathLaw T β energy).map forwardWindowRecord =
        ((G.gibbsPathLaw T β energy).map FullPath.reverse).map
          forwardWindowRecord := by
      rw [G.map_gibbsPathLaw_reverse T β energy hbalance]
    _ = (G.gibbsPathLaw T β energy).map
          (forwardWindowRecord ∘ FullPath.reverse) := by
      rw [Measure.map_map measurable_forwardWindowRecord
        FullPath.measurable_reverse]

/-- **One-window path-level detailed balance from instantaneous Gibbs detailed
balance.** -/
theorem windowBalance_of_gibbsDetailedBalance [Nonempty Ω]
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    G.WindowBalance
      (Gibbs.measure (Measure.count : Measure Ω) β energy) T := by
  unfold WindowBalance
  calc
    Gibbs.measure (Measure.count : Measure Ω) β energy ⊗ₘ
          G.forwardWindowKernel T =
        (G.gibbsPathLaw T β energy).map forwardWindowRecord :=
      G.compProd_forwardWindowKernel_eq_map_gibbsPathLaw T β energy
    _ = (G.gibbsPathLaw T β energy).map reverseWindowRecord :=
      G.map_forwardWindowRecord_eq_map_reverseWindowRecord
        T β energy hbalance
    _ = (Gibbs.measure (Measure.count : Measure Ω) β energy ⊗ₘ
          G.reverseWindowKernel T).map
            (Marked.swapEndpointsEquiv
              (Ω := Ω) (Λ := FullPath Ω)) :=
      (G.map_compProd_reverseWindowKernel_swap T β energy).symm

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
