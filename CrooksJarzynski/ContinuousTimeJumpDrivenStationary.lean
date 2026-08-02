/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenMixture

/-!
# Equilibrium reversal of driven jump sectors

This module combines detailed balance with the reversal-invariant raw counting
chart. It proves reversal invariance first for every weighted fixed-jump-count
sector and then for the actual all-jump-count path measure.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Product of all holding-time survival factors in a fixed jump-count path. -/
noncomputable def pathHoldingProduct
    (G : FiniteJumpGenerator Ω) {n : ℕ} (γ : JumpPath Ω n) : ℝ≥0∞ :=
  ∏ i : Fin (n + 1),
    JumpPath.holdingWeightOfEscapeRate
      (G.pathEscapeRate (n := n)) i (γ.1 i) (γ.2 i)

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- A finite-generator rate density factors into its initial weight, jump-rate
product, and the product of all holding factors. -/
theorem rateDensity_eq_weight_mul_jumpProduct_mul_pathHoldingProduct
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞)
    {n : ℕ} (γ : JumpPath Ω n) :
    JumpPath.rateDensity weight G.pathEscapeRate G.pathJumpRate γ =
      weight (γ.1 0) * G.jumpProduct γ.1 * G.pathHoldingProduct γ := by
  unfold JumpPath.rateDensity JumpPath.density
    JumpPath.jumpWeightOfRate pathJumpRate jumpProduct pathHoldingProduct
  rw [Finset.prod_mul_distrib, Fin.prod_univ_castSucc]
  ring

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Reversing a state sequence turns the forward jump product into the product
of all reversed jump rates. -/
theorem jumpProduct_reverse
    (G : FiniteJumpGenerator Ω) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    G.jumpProduct (fun i => states i.rev) =
      ∏ i : Fin n,
        (G.jumpRate (states i.succ) (states i.castSucc) : ℝ≥0∞) := by
  unfold jumpProduct
  simp only [Fin.rev_castSucc, Fin.rev_succ]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The holding-factor product is invariant under path reversal. -/
theorem pathHoldingProduct_reverse
    (G : FiniteJumpGenerator Ω) {n : ℕ} (γ : JumpPath Ω n) :
    G.pathHoldingProduct (JumpPath.reverse γ) = G.pathHoldingProduct γ := by
  unfold pathHoldingProduct JumpPath.holdingWeightOfEscapeRate
    pathEscapeRate JumpPath.reverse
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Detailed balance makes the complete weighted fixed-sector density invariant
under path reversal. -/
theorem rateDensity_detailedBalance_reverse
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞)
    (hbalance : G.IsDetailedBalanceWeight weight)
    {n : ℕ} (γ : JumpPath Ω n) :
    JumpPath.rateDensity weight G.pathEscapeRate G.pathJumpRate
        (JumpPath.reverse γ) =
      JumpPath.rateDensity weight G.pathEscapeRate G.pathJumpRate γ := by
  rw [G.rateDensity_eq_weight_mul_jumpProduct_mul_pathHoldingProduct,
    G.rateDensity_eq_weight_mul_jumpProduct_mul_pathHoldingProduct]
  have hzero :
      (JumpPath.reverse γ).1 0 = γ.1 (Fin.last n) := by
    simp [JumpPath.reverse]
  rw [hzero]
  change
    weight (γ.1 (Fin.last n)) *
          G.jumpProduct (fun i => γ.1 i.rev) *
        G.pathHoldingProduct (JumpPath.reverse γ) =
      weight (γ.1 0) * G.jumpProduct γ.1 * G.pathHoldingProduct γ
  rw [G.jumpProduct_reverse, G.pathHoldingProduct_reverse]
  rw [← G.weight_mul_jumpProduct_eq_reverse weight hbalance γ.1]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Gibbs detailed balance is the Boltzmann-weight specialization of weighted
path-density reversal. -/
theorem rateDensity_gibbs_reverse
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy)
    {n : ℕ} (γ : JumpPath Ω n) :
    JumpPath.rateDensity
        (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
        G.pathEscapeRate G.pathJumpRate (JumpPath.reverse γ) =
      JumpPath.rateDensity
        (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
        G.pathEscapeRate G.pathJumpRate γ :=
  G.rateDensity_detailedBalance_reverse
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) hbalance γ

/-- Weighted path law in a fixed jump-count sector. -/
noncomputable def weightedSectorLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (weight : Ω → ℝ≥0∞) (n : ℕ) : Measure (JumpPath Ω n) :=
  pathMeasure (G.rawCountingReference T n)
    (JumpPath.rateDensity weight G.pathEscapeRate G.pathJumpRate)

/-- The actual weighted fixed-sector measure is invariant under path reversal
whenever its endpoint weight satisfies detailed balance. -/
theorem map_weightedSectorLaw_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (weight : Ω → ℝ≥0∞)
    (hbalance : G.IsDetailedBalanceWeight weight) (n : ℕ) :
    (G.weightedSectorLaw T weight n).map JumpPath.reverse =
      G.weightedSectorLaw T weight n := by
  unfold weightedSectorLaw
  rw [map_pathMeasure_involution
    (G.rawCountingReference T n) JumpPath.reverse
    (JumpPath.rateDensity weight G.pathEscapeRate G.pathJumpRate)
    JumpPath.measurable_reverse JumpPath.reverse_involutive
    (G.map_rawCountingReference_reverse T n)
    (G.measurable_rateDensity weight n)]
  congr 1
  funext γ
  exact G.rateDensity_detailedBalance_reverse weight hbalance γ

/-- Equilibrium-weighted path law in a fixed jump-count sector. -/
noncomputable def equilibriumSectorLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) (n : ℕ) : Measure (JumpPath Ω n) :=
  G.weightedSectorLaw T
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) n

/-- The equilibrium-weighted fixed-sector measure is invariant under path
reversal. -/
theorem map_equilibriumSectorLaw_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) (n : ℕ) :
    (G.equilibriumSectorLaw T β energy n).map JumpPath.reverse =
      G.equilibriumSectorLaw T β energy n := by
  exact G.map_weightedSectorLaw_reverse T
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) hbalance n

/-- Weighted all-jump-count path law. -/
noncomputable def weightedFullPathLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (weight : Ω → ℝ≥0∞) : Measure (FullPath Ω) :=
  FullPath.measure (fun n => G.weightedSectorLaw T weight n)

/-- The constructed weighted full path law is invariant under complete-path
reversal. -/
theorem map_weightedFullPathLaw_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (weight : Ω → ℝ≥0∞)
    (hbalance : G.IsDetailedBalanceWeight weight) :
    (G.weightedFullPathLaw T weight).map FullPath.reverse =
      G.weightedFullPathLaw T weight := by
  unfold weightedFullPathLaw FullPath.measure
  ext s hs
  rw [Measure.map_apply FullPath.measurable_reverse hs,
    Measure.sum_apply _ (hs.preimage FullPath.measurable_reverse),
    Measure.sum_apply _ hs]
  apply tsum_congr
  intro n
  unfold FullPath.liftMeasure
  rw [Measure.map_apply (FullPath.measurable_mk n)
      (hs.preimage FullPath.measurable_reverse),
    Measure.map_apply (FullPath.measurable_mk n) hs]
  change
    G.weightedSectorLaw T weight n
        (JumpPath.reverse ⁻¹' (Sigma.mk n ⁻¹' s)) =
      G.weightedSectorLaw T weight n (Sigma.mk n ⁻¹' s)
  have hsector := congrArg
    (fun μ : Measure (JumpPath Ω n) => μ (Sigma.mk n ⁻¹' s))
    (G.map_weightedSectorLaw_reverse T weight hbalance n)
  rw [Measure.map_apply JumpPath.measurable_reverse
    ((FullPath.measurable_mk n) hs)] at hsector
  exact hsector

/-- Equilibrium-weighted all-jump-count path law. -/
noncomputable def equilibriumFullPathLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) : Measure (FullPath Ω) :=
  G.weightedFullPathLaw T
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))

/-- Gibbs detailed balance makes the equilibrium-weighted full path law
invariant under complete-path reversal. -/
theorem map_equilibriumFullPathLaw_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    (G.equilibriumFullPathLaw T β energy).map FullPath.reverse =
      G.equilibriumFullPathLaw T β energy := by
  exact G.map_weightedFullPathLaw_reverse T
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) hbalance

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
