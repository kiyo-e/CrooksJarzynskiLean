/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoState
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Normalization and Poisson jump counts for the two-state CTMC

The simplex reference in this module is scaled by its geometric volume
`T^n / n!`.  The unit escape-rate density is constant `exp (-T)` on the
reference support, so the `n`-jump sector has exactly the Poisson mass
`exp (-T) T^n / n!`.  Summing all sectors constructs a probability measure on
finite-jump paths and therefore proves non-explosion for this concrete chain.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- The measurable event that all state changes are the allowed flips. -/
def pathAlternatesSet (n : ℕ) : Set (JumpPath State n) :=
  {γ | Alternates γ.1}

/-- The alternating-path event is measurable. -/
theorem measurableSet_pathAlternatesSet (n : ℕ) :
    MeasurableSet (pathAlternatesSet n) := by
  change MeasurableSet
    (Prod.fst ⁻¹' {states : Fin (n + 1) → State | Alternates states})
  exact measurable_fst measurableSet_alternates

/-- Before symmetrization, the simplex path probability has alternating states. -/
theorem rawPathProbability_ae_alternates (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂Simplex.rawPathProbability T (alternatingStateLaw n),
      Alternates γ.1 := by
  let f := Simplex.assemblePath (Ω := State) (n := n) T
  have hf : Measurable f := Simplex.measurable_assemblePath T
  rw [Simplex.rawPathProbability,
    ae_map_iff hf.aemeasurable (measurableSet_pathAlternatesSet n)]
  apply (Measure.ae_prod_iff_ae_ae
    (μ := alternatingStateLaw n) (ν := Simplex.freeSimplexProbability n)
    (hf (measurableSet_pathAlternatesSet n))).2
  exact (alternatingStateLaw_ae_alternates n).mono fun states hstates =>
    ae_of_all (Simplex.freeSimplexProbability n) fun u => by
      change Alternates states
      exact hstates

/-- Symmetrization preserves alternation because path reversal preserves it. -/
theorem pathProbability_ae_alternates (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂Simplex.pathProbability T (alternatingStateLaw n),
      Alternates γ.1 := by
  have hraw := rawPathProbability_ae_alternates T n
  have hreverse :
      ∀ᵐ γ ∂(Simplex.rawPathProbability T (alternatingStateLaw n)).map
          JumpPath.reverse,
        Alternates γ.1 := by
    rw [ae_map_iff JumpPath.measurable_reverse.aemeasurable
      (measurableSet_pathAlternatesSet n)]
    exact hraw.mono fun γ hγ => by
      change Alternates (fun i => γ.1 i.rev)
      exact alternates_reverse hγ
  unfold Simplex.pathProbability Simplex.symmetrizePathMeasure
  exact Measure.ae_smul_measure ((ae_add_measure_iff).2 ⟨hraw, hreverse⟩) _

/-- The scaled CTMC reference is concentrated on alternating paths. -/
theorem sectorReference_ae_alternates (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂sectorReference T n, Alternates γ.1 := by
  unfold sectorReference Simplex.reference
  exact Measure.ae_smul_measure (pathProbability_ae_alternates T n) _

/-- Survival through a time interval of length `T` at unit escape rate. -/
noncomputable def survivalWeight (T : NNReal) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(T : ℝ)))

/-- On every alternating fixed-horizon path, the rate density is the constant
survival factor `exp (-T)`. -/
theorem rateDensity_eq_survivalWeight {T : NNReal} {n : ℕ}
    (γ : JumpPath State n) (halternates : Alternates γ.1)
    (hhorizon : γ ∈ JumpPath.horizonSet (Ω := State) (n := n) T) :
    JumpPath.rateDensity endpointWeight escapeRate jumpRate γ =
      survivalWeight T := by
  unfold JumpPath.rateDensity JumpPath.density endpointWeight
  simp only [one_mul]
  have hjump : ∀ i : Fin n,
      JumpPath.jumpWeightOfRate jumpRate i
          (γ.1 i.castSucc) (γ.1 i.succ) = 1 := by
    intro i
    unfold JumpPath.jumpWeightOfRate jumpRate
    simp [halternates i]
  simp_rw [hjump, mul_one]
  let holding : Fin (n + 1) → ℝ≥0∞ := fun i =>
    JumpPath.holdingWeightOfEscapeRate escapeRate i (γ.1 i) (γ.2 i)
  change (∏ i : Fin n, holding i.castSucc) * holding (Fin.last n) =
    survivalWeight T
  rw [← Fin.prod_univ_castSucc holding]
  dsimp [holding]
  unfold JumpPath.holdingWeightOfEscapeRate escapeRate
  simp only [NNReal.coe_one, one_mul]
  have hprod :
      (∏ i : Fin (n + 1),
          ENNReal.ofReal (Real.exp (-((γ.2 i : NNReal) : ℝ)))) =
        ENNReal.ofReal
          (Real.exp (-(∑ i : Fin (n + 1), ((γ.2 i : NNReal) : ℝ)))) := by
    calc
      (∏ i : Fin (n + 1),
          ENNReal.ofReal (Real.exp (-((γ.2 i : NNReal) : ℝ)))) =
          ENNReal.ofReal
            (∏ i : Fin (n + 1), Real.exp (-((γ.2 i : NNReal) : ℝ))) := by
        rw [ENNReal.ofReal_prod_of_nonneg]
        intro i hi
        positivity
      _ = ENNReal.ofReal
          (Real.exp (-(∑ i : Fin (n + 1), ((γ.2 i : NNReal) : ℝ)))) := by
        congr 1
        simpa using
          (Real.exp_sum Finset.univ
            (fun i : Fin (n + 1) => -((γ.2 i : NNReal) : ℝ))).symm
  rw [hprod]
  unfold survivalWeight
  change JumpPath.totalHoldingTime γ = T at hhorizon
  have hsum :
      (∑ i : Fin (n + 1), ((γ.2 i : NNReal) : ℝ)) = (T : ℝ) := by
    exact_mod_cast hhorizon
  rw [hsum]

/-- The rate density equals the constant survival factor almost everywhere
with respect to the concrete simplex reference. -/
theorem rateDensity_ae_eq_survivalWeight (T : NNReal) (n : ℕ) :
    JumpPath.rateDensity endpointWeight escapeRate jumpRate =ᵐ[sectorReference T n]
      fun _ => survivalWeight T := by
  filter_upwards [sectorReference_ae_alternates T n,
    sectorReference_ae_horizon T n] with γ halternates hhorizon
  exact rateDensity_eq_survivalWeight γ halternates hhorizon

/-- The actual forward CTMC law in one jump-count sector. -/
noncomputable def sectorLaw (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  pathMeasure (sectorReference T n)
    (JumpPath.rateDensity endpointWeight escapeRate jumpRate)

/-- The sector law is the simplex reference scaled by the survival factor. -/
theorem sectorLaw_eq_smul_reference (T : NNReal) (n : ℕ) :
    sectorLaw T n = survivalWeight T • sectorReference T n := by
  unfold sectorLaw pathMeasure
  calc
    (sectorReference T n).withDensity
        (JumpPath.rateDensity endpointWeight escapeRate jumpRate) =
      (sectorReference T n).withDensity (fun _ => survivalWeight T) :=
        MeasureTheory.withDensity_congr_ae
          (rateDensity_ae_eq_survivalWeight T n)
    _ = survivalWeight T • sectorReference T n := by
      exact MeasureTheory.withDensity_const
        (μ := sectorReference T n) (survivalWeight T)

/-- The mass of the `n`-jump sector is the corresponding Poisson probability. -/
theorem sectorLaw_univ_eq_poisson (T : NNReal) (n : ℕ) :
    sectorLaw T n Set.univ = ProbabilityTheory.poissonMeasure T {n} := by
  rw [sectorLaw_eq_smul_reference, Measure.smul_apply, sectorReference_univ,
    ProbabilityTheory.poissonMeasure_singleton]
  rw [simplexMass_eq_ofReal]
  unfold survivalWeight
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

/-- The full finite-jump path law of the unit-rate two-state CTMC. -/
noncomputable def pathLaw (T : NNReal) : Measure (FullPath State) :=
  FullPath.measure (sectorLaw T)

/-- The Poisson sector masses sum to one. -/
theorem tsum_sectorLaw_univ (T : NNReal) :
    ∑' n, sectorLaw T n Set.univ = 1 := by
  calc
    (∑' n, sectorLaw T n Set.univ) =
        ∑' n, ProbabilityTheory.poissonMeasure T {n} := by
      apply tsum_congr
      exact sectorLaw_univ_eq_poisson T
    _ = ProbabilityTheory.poissonMeasure T (⋃ n : ℕ, ({n} : Set ℕ)) := by
      have hdisj : Pairwise (fun i j : ℕ =>
          Disjoint ({i} : Set ℕ) ({j} : Set ℕ)) := by
        intro i j hij
        refine Set.disjoint_left.2 ?_
        intro x hxi hxj
        simp only [Set.mem_singleton_iff] at hxi hxj
        exact (hij (hxi.symm.trans hxj)).elim
      exact (measure_iUnion hdisj (fun n => measurableSet_singleton n)).symm
    _ = ProbabilityTheory.poissonMeasure T Set.univ := by
      congr 1
      ext n
      simp
    _ = 1 := measure_univ

/-- The constructed full finite-jump law is a probability measure.  Since its
sample space is the disjoint union of finite jump-count sectors, this is the
non-explosion theorem for the concrete unit-rate two-state chain. -/
noncomputable instance instIsProbabilityMeasurePathLaw (T : NNReal) :
    IsProbabilityMeasure (pathLaw T) := by
  unfold pathLaw
  exact FullPath.isProbabilityMeasure_measure (sectorLaw T)
    (tsum_sectorLaw_univ T)

/-- The reverse-experiment law in one sector. -/
noncomputable def reverseSectorLaw (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  JumpPath.timeReversedMeasure
    (pathMeasure (sectorReference T n)
      (JumpPath.reverseRateDensity endpointWeight escapeRate jumpRate))

/-- At equilibrium and with zero work, the reverse law equals the forward law. -/
theorem reverseSectorLaw_eq_sectorLaw (T : NNReal) (n : ℕ) :
    reverseSectorLaw T n = sectorLaw T n := by
  have h := sector_crooks T n
  unfold CrooksRelation at h
  have hwork :
      JumpPath.rateWorkWeight boundaryWork (jumpWork (n := n)) =
        fun _ => 1 := by
    funext γ
    exact rateWorkWeight_eq_one γ
  simpa [reverseSectorLaw, sectorLaw, hwork] using h.symm

/-- The full reverse law. -/
noncomputable def reversePathLaw (T : NNReal) : Measure (FullPath State) :=
  FullPath.measure (reverseSectorLaw T)

/-- The full forward and reverse laws coincide in this equilibrium model. -/
theorem reversePathLaw_eq_pathLaw (T : NNReal) :
    reversePathLaw T = pathLaw T := by
  unfold reversePathLaw pathLaw
  congr 1
  funext n
  exact reverseSectorLaw_eq_sectorLaw T n

noncomputable instance instIsProbabilityMeasureReversePathLaw (T : NNReal) :
    IsProbabilityMeasure (reversePathLaw T) := by
  rw [reversePathLaw_eq_pathLaw]
  infer_instance

/-- The work observable on the full path space is identically one. -/
theorem fullWorkWeight_eq_one (γ : FullPath State) :
    FullPath.weight
        (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork)) γ = 1 := by
  rcases γ with ⟨n, γ⟩
  exact rateWorkWeight_eq_one γ

/-- Crooks relation for the normalized, non-explosive two-state CTMC path law. -/
theorem pathLaw_crooks (T : NNReal) :
    CrooksRelation (pathLaw T) (reversePathLaw T)
      (FullPath.weight
        (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork))) 1 := by
  apply FullPath.crooks_of_sector_relations
    (sectorLaw T) (reverseSectorLaw T)
    (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork)) 1
    measurable_rateWorkWeight
  exact sector_crooks T

/-- Jarzynski equality for the normalized two-state CTMC. -/
theorem pathLaw_jarzynski (T : NNReal) :
    ∫⁻ γ, FullPath.weight
        (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork)) γ
        ∂pathLaw T = 1 :=
  jarzynski_lintegral _ _ _ _ (pathLaw_crooks T)

/-- Real-valued Jarzynski equality for the normalized two-state CTMC. -/
theorem pathLaw_jarzynski_toReal (T : NNReal) :
    ∫ γ, (FullPath.weight
        (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork)) γ).toReal
        ∂pathLaw T = 1 := by
  simpa using
    (jarzynski_toReal_integral (pathLaw T) (reversePathLaw T)
      (FullPath.weight
        (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork)))
      1 (FullPath.measurable_weight _ measurable_rateWorkWeight)
      (by simp) (pathLaw_crooks T))

/-- The off-diagonal generator rate of the concrete chain. -/
def generatorRate (x y : State) : NNReal :=
  if y = flip x then 1 else 0

/-- The escape rate computed from the generator is one. -/
theorem generator_escape_eq_one (x : State) :
    (∑ y : State, (if y = x then (0 : NNReal) else generatorRate x y)) = 1 := by
  have huniv : (Finset.univ : Finset State) = {.zero, .one} := by decide
  cases x <;> simp [huniv, generatorRate, flip]

/-- The segment jump-rate family is the generator's off-diagonal rate. -/
theorem jumpRate_eq_generatorRate {n : ℕ} (i : Fin n) (x y : State) :
    jumpRate i x y = generatorRate x y :=
  rfl

/-- The real-valued conservative generator matrix. -/
def generator (x y : State) : ℝ :=
  if y = x then -1 else generatorRate x y

/-- Every row of the generator sums to zero. -/
theorem generator_row_sum (x : State) :
    ∑ y : State, generator x y = 0 := by
  have huniv : (Finset.univ : Finset State) = {.zero, .one} := by decide
  cases x <;> simp [huniv, generator, generatorRate, flip]

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
