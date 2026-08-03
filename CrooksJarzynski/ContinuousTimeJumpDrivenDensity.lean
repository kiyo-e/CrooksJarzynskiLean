/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenBalance
import CrooksJarzynski.ContinuousTimeJumpFull

/-!
# Gibbs reversal of finite-generator window densities

Instantaneous detailed balance makes the equilibrium-weighted density of every
fixed jump-count sector equal to its time-reversal-aligned density. The proof
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

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
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

omit [DecidableEq Ω] in
/-- The equilibrium-weighted law in each fixed jump-count sector satisfies a
unit-work, unit-free-energy Crooks relation. -/
theorem gibbsSector_crooks
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    CrooksRelation
      (pathMeasure (G.rawCountingReference T n)
        (JumpPath.rateDensity
          (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
          G.pathEscapeRate G.pathJumpRate))
      (JumpPath.timeReversedMeasure
        (pathMeasure (G.rawCountingReference T n)
          (JumpPath.reverseExperimentDensity
            (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
            (JumpPath.holdingWeightOfEscapeRate G.pathEscapeRate)
            (JumpPath.jumpWeightOfRate G.pathJumpRate))))
      (fun _ => 1) 1 := by
  apply JumpPath.crooks_of_density_identity
    (G.rawCountingReference T n)
    (JumpPath.rateDensity
      (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
      G.pathEscapeRate G.pathJumpRate)
    (JumpPath.reverseExperimentDensity
      (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
      (JumpPath.holdingWeightOfEscapeRate G.pathEscapeRate)
      (JumpPath.jumpWeightOfRate G.pathJumpRate))
    (fun _ => 1) 1
  · exact G.map_rawCountingReference_reverse T n
  · exact G.measurable_rateDensity
      (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) n
  · unfold JumpPath.reverseExperimentDensity
      JumpPath.alignedReverseDensity
      JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
      pathEscapeRate pathJumpRate
    fun_prop
  · exact measurable_const
  · refine ae_of_all _ fun γ => ?_
    simp only [mul_one, one_mul,
      JumpPath.reverseExperimentDensity_reverse]
    exact G.rateDensity_gibbs_eq_alignedReverse β energy hbalance γ

omit [DecidableEq Ω] in
/-- Summing the equilibrium sector relations yields a Crooks relation on the
complete finite-jump path space.  Both sides are unnormalized
Boltzmann-weighted laws — no partition-function normalization has been divided
out; because the same landscape weights both sides, the unnormalized masses
agree and the relation holds with trivial work weight and constant `1`. -/
theorem gibbsFullPath_crooks
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy) :
    CrooksRelation
      (FullPath.measure fun n =>
        pathMeasure (G.rawCountingReference T n)
          (JumpPath.rateDensity
            (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
            G.pathEscapeRate G.pathJumpRate))
      (FullPath.measure fun n =>
        JumpPath.timeReversedMeasure
          (pathMeasure (G.rawCountingReference T n)
            (JumpPath.reverseExperimentDensity
              (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
              (JumpPath.holdingWeightOfEscapeRate G.pathEscapeRate)
              (JumpPath.jumpWeightOfRate G.pathJumpRate))))
      (FullPath.weight (fun _ _ => 1)) 1 :=
  FullPath.crooks_of_sector_relations
    (fun n =>
      pathMeasure (G.rawCountingReference T n)
        (JumpPath.rateDensity
          (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
          G.pathEscapeRate G.pathJumpRate))
    (fun n =>
      JumpPath.timeReversedMeasure
        (pathMeasure (G.rawCountingReference T n)
          (JumpPath.reverseExperimentDensity
            (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))
            (JumpPath.holdingWeightOfEscapeRate G.pathEscapeRate)
            (JumpPath.jumpWeightOfRate G.pathJumpRate))))
    (fun _ _ => 1) 1
    (fun _ => measurable_const)
    (fun n => G.gibbsSector_crooks T n β energy hbalance)

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
