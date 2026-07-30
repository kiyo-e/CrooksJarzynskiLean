/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpHorizon
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.ConditionalProbability

/-!
# Nontrivial fixed-horizon simplex reference measures

The equality slice `sum τ = T` has zero mass under an ambient product Lebesgue
measure.  This module instead builds the horizon constraint into the path law.
It starts with `n` free holding-time coordinates in the unit cube, conditions
on their sum being at most one, scales them by `T`, and fills the final holding
interval with the residual time.

The resulting probability measure is supported on the horizon by construction.
Averaging it with its time reversal gives an explicitly reversal-invariant,
nonzero reference measure on the fixed-horizon path space.
-/

open MeasureTheory
open scoped ENNReal BigOperators ProbabilityTheory unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Simplex

universe u

/-- Regard a point of the unit interval as a nonnegative real. -/
def unitNNReal (x : I) : NNReal :=
  ⟨x, x.2.1⟩

@[simp, norm_cast]
theorem coe_unitNNReal (x : I) : (unitNNReal x : ℝ) = x :=
  rfl

@[fun_prop]
theorem measurable_unitNNReal : Measurable unitNNReal :=
  measurable_subtype_coe.subtype_mk

/-- The standard `n`-simplex in the unit cube, expressed using `n` free
holding-time coordinates. -/
def freeSimplexSet (n : ℕ) : Set (Fin n → I) :=
  {u | ∑ i, (unitNNReal (u i) : ℝ) ≤ 1}

/-- The free-coordinate simplex is measurable. -/
theorem measurableSet_freeSimplexSet (n : ℕ) :
    MeasurableSet (freeSimplexSet n) := by
  unfold freeSimplexSet
  exact measurableSet_le (by fun_prop) measurable_const

/-- A positive coordinate bound whose product box lies inside the simplex. -/
noncomputable def interiorRadius (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 1), by
    constructor
    · positivity
    · have hpos : 0 < (n : ℝ) + 1 := by positivity
      apply (div_le_iff₀ hpos).2
      norm_num⟩

@[simp]
theorem coe_interiorRadius (n : ℕ) :
    ((interiorRadius n : I) : ℝ) = 1 / ((n : ℝ) + 1) :=
  rfl

/-- The small positive box with side length `1 / (n + 1)` lies inside the
free-coordinate simplex. -/
theorem smallBox_subset_freeSimplexSet (n : ℕ) :
    Set.univ.pi (fun _ : Fin n => Set.Iic (interiorRadius n)) ⊆
      freeSimplexSet n := by
  intro u hu
  rw [Set.mem_univ_pi] at hu
  change (∑ i, (unitNNReal (u i) : ℝ)) ≤ 1
  calc
    (∑ i, (unitNNReal (u i) : ℝ)) ≤
        ∑ _ : Fin n, ((interiorRadius n : I) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa using hu i
    _ = (n : ℝ) / ((n : ℝ) + 1) := by
      simp [div_eq_mul_inv]
    _ ≤ 1 := by
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      apply (div_le_iff₀ hpos).2
      norm_num

/-- The simplex event has strictly positive product volume, so conditioning on
it is nondegenerate for every jump count, including `n = 0`. -/
theorem volume_freeSimplexSet_pos (n : ℕ) :
    0 < (volume : Measure (Fin n → I)) (freeSimplexSet n) := by
  let B : Set (Fin n → I) :=
    Set.univ.pi (fun _ : Fin n => Set.Iic (interiorRadius n))
  have hB : B ⊆ freeSimplexSet n :=
    smallBox_subset_freeSimplexSet n
  have hBmass :
      (volume : Measure (Fin n → I)) B =
        ∏ _ : Fin n, ENNReal.ofReal ((interiorRadius n : I) : ℝ) := by
    change (Measure.pi fun _ : Fin n => (volume : Measure I)) B = _
    rw [Measure.pi_pi]
    simp [B, unitInterval.volume_Iic]
  have hBpos : 0 < (volume : Measure (Fin n → I)) B := by
    rw [hBmass]
    positivity
  exact hBpos.trans_le (measure_mono hB)

/-- The uniform probability law on the free-coordinate simplex.  It is the
finite product of unit-interval Lebesgue measures conditioned on `sum u ≤ 1`. -/
noncomputable def freeSimplexProbability (n : ℕ) : Measure (Fin n → I) :=
  (volume : Measure (Fin n → I))[|freeSimplexSet n]

noncomputable instance instIsProbabilityMeasureFreeSimplexProbability (n : ℕ) :
    IsProbabilityMeasure (freeSimplexProbability n) := by
  unfold freeSimplexProbability
  exact ProbabilityTheory.cond_isProbabilityMeasure
    (ne_of_gt (volume_freeSimplexSet_pos n))

/-- Fill the last holding interval with the residual time after scaling the
`n` free simplex coordinates by the physical horizon `T`. -/
def holdingTimesOfFree {n : ℕ} (T : NNReal) (u : Fin n → I) :
    Fin (n + 1) → NNReal :=
  Fin.snoc (fun i => T * unitNNReal (u i))
    (T - ∑ i, T * unitNNReal (u i))

@[fun_prop]
theorem measurable_holdingTimesOfFree {n : ℕ} (T : NNReal) :
    Measurable (holdingTimesOfFree (n := n) T) := by
  unfold holdingTimesOfFree
  fun_prop

/-- On the simplex event, the completed holding-time vector has total duration
exactly `T`. -/
theorem sum_holdingTimesOfFree {n : ℕ} (T : NNReal) (u : Fin n → I)
    (hu : u ∈ freeSimplexSet n) :
    ∑ i, holdingTimesOfFree T u i = T := by
  have hsum : (∑ i, unitNNReal (u i)) ≤ (1 : NNReal) := by
    exact_mod_cast hu
  have hscaled : (∑ i, T * unitNNReal (u i)) ≤ T := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_left' hsum T
  rw [Fin.sum_univ_castSucc]
  simp only [holdingTimesOfFree, Fin.snoc_castSucc, Fin.snoc_last]
  exact add_tsub_of_le hscaled

/-- Assemble a state sequence and free simplex coordinates into a fixed-horizon
jump path. -/
def assemblePath {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal) :
    (Fin (n + 1) → Ω) × (Fin n → I) → JumpPath Ω n :=
  fun p => (p.1, holdingTimesOfFree T p.2)

@[fun_prop]
theorem measurable_assemblePath {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) : Measurable (assemblePath (Ω := Ω) (n := n) T) := by
  unfold assemblePath
  fun_prop

/-- A raw fixed-horizon path probability obtained from an arbitrary probability
law on state sequences and the uniform free-coordinate simplex law. -/
noncomputable def rawPathProbability {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    Measure (JumpPath Ω n) :=
  (stateLaw.prod (freeSimplexProbability n)).map
    (assemblePath (Ω := Ω) (n := n) T)

noncomputable instance instIsProbabilityMeasureRawPathProbability
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal)
    (stateLaw : Measure (Fin (n + 1) → Ω)) [IsProbabilityMeasure stateLaw] :
    IsProbabilityMeasure (rawPathProbability T stateLaw) := by
  unfold rawPathProbability
  exact Measure.isProbabilityMeasure_map
    (measurable_assemblePath (Ω := Ω) (n := n) T).aemeasurable

/-- Average a path measure with its time reversal.  This construction is useful
when the underlying simplex volume is known mathematically to be symmetric but
one wants reversal invariance to be definitional at the measure level. -/
noncomputable def symmetrizePathMeasure {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure (JumpPath Ω n)) : Measure (JumpPath Ω n) :=
  (2 : ℝ≥0∞)⁻¹ • (μ + μ.map JumpPath.reverse)

/-- Symmetrization is invariant under path reversal. -/
theorem map_symmetrizePathMeasure_reverse
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure (JumpPath Ω n)) :
    (symmetrizePathMeasure μ).map JumpPath.reverse =
      symmetrizePathMeasure μ := by
  simp [symmetrizePathMeasure, Measure.map_add, Measure.map_map,
    Function.comp_def, add_comm]

/-- Symmetrizing a probability measure preserves normalization. -/
theorem isProbabilityMeasure_symmetrizePathMeasure
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure (JumpPath Ω n)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetrizePathMeasure μ) := by
  letI : IsProbabilityMeasure (μ.map JumpPath.reverse) :=
    Measure.isProbabilityMeasure_map JumpPath.measurable_reverse.aemeasurable
  constructor
  simp [symmetrizePathMeasure]

/-- The nontrivial, reversal-invariant fixed-horizon path probability used as a
canonical simplex reference. -/
noncomputable def pathProbability {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    Measure (JumpPath Ω n) :=
  symmetrizePathMeasure (rawPathProbability T stateLaw)

noncomputable instance instIsProbabilityMeasurePathProbability
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal)
    (stateLaw : Measure (Fin (n + 1) → Ω)) [IsProbabilityMeasure stateLaw] :
    IsProbabilityMeasure (pathProbability T stateLaw) :=
  isProbabilityMeasure_symmetrizePathMeasure _

/-- The simplex path probability is reversal invariant. -/
theorem map_pathProbability_reverse
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    (pathProbability T stateLaw).map JumpPath.reverse =
      pathProbability T stateLaw :=
  map_symmetrizePathMeasure_reverse _

/-- The raw simplex construction is supported on paths of total duration `T`. -/
theorem rawPathProbability_ae_horizon
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂rawPathProbability T stateLaw,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  let f := assemblePath (Ω := Ω) (n := n) T
  have hf : Measurable f := measurable_assemblePath T
  rw [rawPathProbability, ae_map_iff hf.aemeasurable
    (JumpPath.measurableSet_horizonSet T)]
  apply (ae_prod_iff_ae_ae (hf (JumpPath.measurableSet_horizonSet T))).2
  refine ae_of_all stateLaw fun states => ?_
  have hmem : ∀ᵐ u ∂freeSimplexProbability n, u ∈ freeSimplexSet n := by
    unfold freeSimplexProbability
    exact ProbabilityTheory.ae_cond_mem (measurableSet_freeSimplexSet n)
  exact hmem.mono fun u hu => by
    change ∑ i, holdingTimesOfFree T u i = T
    exact sum_holdingTimesOfFree T u hu

/-- Symmetrization preserves concentration on the reversal-invariant horizon. -/
theorem pathProbability_ae_horizon
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂pathProbability T stateLaw,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  have hraw := rawPathProbability_ae_horizon T stateLaw
  have hreverse :
      ∀ᵐ γ ∂(rawPathProbability T stateLaw).map JumpPath.reverse,
        γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
    rw [ae_map_iff JumpPath.measurable_reverse.aemeasurable
      (JumpPath.measurableSet_horizonSet T)]
    exact hraw.mono fun γ hγ => by
      simpa [JumpPath.horizonSet] using hγ
  unfold pathProbability symmetrizePathMeasure
  exact ae_smul_measure ((ae_add_measure_iff).2 ⟨hraw, hreverse⟩) _

/-- Scale the canonical horizon probability to obtain a reference measure of a
prescribed finite mass. -/
noncomputable def reference {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    (mass : ℝ≥0∞) : Measure (JumpPath Ω n) :=
  mass • pathProbability T stateLaw

/-- Every scaled simplex reference is reversal invariant. -/
theorem map_reference_reverse
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    (mass : ℝ≥0∞) :
    (reference T stateLaw mass).map JumpPath.reverse =
      reference T stateLaw mass := by
  simp [reference, map_pathProbability_reverse]

/-- The total mass of the scaled reference is the requested scalar. -/
theorem reference_univ
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    [IsProbabilityMeasure stateLaw] (mass : ℝ≥0∞) :
    reference T stateLaw mass Set.univ = mass := by
  simp [reference]

/-- Positive mass gives a genuinely nonzero fixed-horizon reference measure. -/
theorem reference_ne_zero
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    [IsProbabilityMeasure stateLaw] {mass : ℝ≥0∞} (hmass : mass ≠ 0) :
    reference T stateLaw mass ≠ 0 := by
  rw [Ne, Measure.ennreal_smul_eq_zero]
  exact not_or_intro hmass (IsProbabilityMeasure.ne_zero _)

/-- The scaled reference remains concentrated on the physical horizon. -/
theorem reference_ae_horizon
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    (mass : ℝ≥0∞) :
    ∀ᵐ γ ∂reference T stateLaw mass,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T :=
  ae_smul_measure (pathProbability_ae_horizon T stateLaw) mass

end Simplex
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
