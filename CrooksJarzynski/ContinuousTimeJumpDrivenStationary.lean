/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenMixture

/-!
# Equilibrium reversal of driven jump sectors

This module combines the Gibbs jump-product balance with the reversal-invariant
raw counting chart. It proves that the equilibrium-weighted path law in every
fixed jump-count sector is invariant under the existing path-reversal map.
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
/-- Detailed balance makes the complete equilibrium-weighted fixed-sector
density invariant under path reversal. -/
theorem rateDensity_gibbs_reverse
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy)
    {n : ℕ} (γ : JumpPath Ω n) :
    JumpPath.rateDensity
        (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
        G.pathEscapeRate G.pathJumpRate (JumpPath.reverse γ) =
      JumpPath.rateDensity
        (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
        G.pathEscapeRate G.pathJumpRate γ := by
  rw [G.rateDensity_eq_weight_mul_jumpProduct_mul_pathHoldingProduct,
    G.rateDensity_eq_weight_mul_jumpProduct_mul_pathHoldingProduct]
  have hzero :
      (JumpPath.reverse γ).1 0 = γ.1 (Fin.last n) := by
    simp [JumpPath.reverse]
  rw [hzero]
  change
    ENNReal.ofReal (Real.exp (-β * energy (γ.1 (Fin.last n)))) *
          G.jumpProduct (fun i => γ.1 i.rev) *
        G.pathHoldingProduct (JumpPath.reverse γ) =
      ENNReal.ofReal (Real.exp (-β * energy (γ.1 0))) *
          G.jumpProduct γ.1 * G.pathHoldingProduct γ
  rw [G.jumpProduct_reverse, G.pathHoldingProduct_reverse]
  rw [← G.gibbsWeight_mul_jumpProduct_eq_reverse β energy hbalance γ.1]

/-- Equilibrium-weighted path law in a fixed jump-count sector. -/
noncomputable def equilibriumSectorLaw
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ) (n : ℕ) : Measure (JumpPath Ω n) :=
  pathMeasure (G.rawCountingReference T n)
    (JumpPath.rateDensity
      (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
      G.pathEscapeRate G.pathJumpRate)

/-- The actual equilibrium-weighted fixed-sector measure is invariant under
path reversal. -/
theorem map_equilibriumSectorLaw_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) (n : ℕ) :
    (G.equilibriumSectorLaw T β energy n).map JumpPath.reverse =
      G.equilibriumSectorLaw T β energy n := by
  unfold equilibriumSectorLaw
  rw [map_pathMeasure_involution
    (G.rawCountingReference T n) JumpPath.reverse
    (JumpPath.rateDensity
      (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
      G.pathEscapeRate G.pathJumpRate)
    JumpPath.measurable_reverse JumpPath.reverse_involutive
    (G.map_rawCountingReference_reverse T n)
    (G.measurable_rateDensity
      (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) n)]
  congr 1
  funext γ
  exact G.rateDensity_gibbs_reverse β energy hbalance γ

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
