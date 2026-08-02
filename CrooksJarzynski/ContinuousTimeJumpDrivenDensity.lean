/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenBalance

/-!
# Gibbs reversal of finite-generator window densities

Instantaneous detailed balance makes the equilibrium-weighted density of every
fixed jump-count sector equal to its time-reversal-aligned density.  The proof
separates the common holding factors and applies the pathwise jump-product
identity from `ContinuousTimeJumpDrivenBalance`.
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

/-- Gibbs detailed balance identifies the forward and aligned reverse rate
densities pointwise in every fixed jump-count sector. -/
theorem rateDensity_gibbs_eq_alignedReverse
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy)
    {n : ℕ} (γ : JumpPath Ω n) :
    JumpPath.rateDensity
        (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
        G.pathEscapeRate G.pathJumpRate γ =
      JumpPath.alignedReverseRateDensity
        (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
        G.pathEscapeRate G.pathJumpRate γ := by
  have hjump := G.gibbsWeight_mul_jumpProduct_eq_reverse
    β energy hbalance γ.1
  unfold JumpPath.rateDensity JumpPath.density
    JumpPath.alignedReverseRateDensity JumpPath.alignedReverseDensity
    JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
    pathEscapeRate pathJumpRate
  unfold jumpProduct at hjump
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  calc
    ENNReal.ofReal (Real.exp (-β * energy (γ.1 0))) *
          ((∏ i : Fin n,
              ENNReal.ofReal
                (Real.exp
                  (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
                    (γ.2 i.castSucc : ℝ))))) *
            ∏ i : Fin n,
              (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ≥0∞)) *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (γ.1 (Fin.last n)) : ℝ) *
              (γ.2 (Fin.last n) : ℝ)))) =
      (ENNReal.ofReal (Real.exp (-β * energy (γ.1 0))) *
          ∏ i : Fin n,
            (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ≥0∞)) *
        (∏ i : Fin n,
          ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
                (γ.2 i.castSucc : ℝ))))) *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (γ.1 (Fin.last n)) : ℝ) *
              (γ.2 (Fin.last n) : ℝ)))) := by
        ac_rfl
    _ = (ENNReal.ofReal
            (Real.exp (-β * energy (γ.1 (Fin.last n)))) *
          ∏ i : Fin n,
            (G.jumpRate (γ.1 i.succ) (γ.1 i.castSucc) : ℝ≥0∞)) *
        (∏ i : Fin n,
          ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
                (γ.2 i.castSucc : ℝ))))) *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (γ.1 (Fin.last n)) : ℝ) *
              (γ.2 (Fin.last n) : ℝ)))) := by
        rw [hjump]
    _ = ENNReal.ofReal
          (Real.exp (-β * energy (γ.1 (Fin.last n)))) *
        ((∏ i : Fin n,
            ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
                  (γ.2 i.castSucc : ℝ))))) *
          ∏ i : Fin n,
            (G.jumpRate (γ.1 i.succ) (γ.1 i.castSucc) : ℝ≥0∞)) *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (γ.1 (Fin.last n)) : ℝ) *
              (γ.2 (Fin.last n) : ℝ)))) := by
        ac_rfl

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
