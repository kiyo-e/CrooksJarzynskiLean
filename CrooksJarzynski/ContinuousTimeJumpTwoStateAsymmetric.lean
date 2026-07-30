/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoState
import CrooksJarzynski.MeasureProtocolFiniteBridge

/-!
# A non-equilibrium asymmetric two-state jump example

This module gives a concrete nontrivial application of the rate-level Crooks
theorem.  The forward chain jumps from `zero` to `one` at rate two and from
`one` to `zero` at rate one.  Its initial endpoint density is the corresponding
Gibbs equilibrium density relative to the uniform state reference.  The final
endpoint density is uniform, and the free-energy weight is two.

Both the jump-work factor and the resulting path-work observable are
nonconstant, so this example does not reduce to equality of the forward and
reverse laws.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- State-dependent escape rate: two from `zero`, one from `one`. -/
def escapeRate {n : ℕ} : Fin (n + 1) → State → NNReal :=
  fun _ x => match x with
    | .zero => 2
    | .one => 1

/-- The asymmetric off-diagonal jump rates. -/
def jumpRate {n : ℕ} : Fin n → State → State → NNReal :=
  fun _ x y => match x, y with
    | .zero, .one => 2
    | .one, .zero => 1
    | _, _ => 0

/-- The normalized Gibbs density relative to the uniform two-state reference.
It gives probabilities `1/3` and `2/3`. -/
noncomputable def gibbsInitialWeight : State → ℝ≥0∞
  | .zero => 2 / 3
  | .one => 4 / 3

/-- The final Gibbs density is uniform. -/
def gibbsFinalWeight : State → ℝ≥0∞ :=
  fun _ => 1

/-- A non-unit free-energy weight. -/
def freeEnergyWeight : ℝ≥0∞ := 2

/-- Endpoint work for the change from the asymmetric Gibbs state to the
uniform Gibbs state. -/
noncomputable def boundaryWork : State → State → ℝ≥0∞
  | .zero, _ => 3
  | .one, _ => 3 / 2

/-- Jump work compensating the asymmetry of the forward and reverse rates. -/
noncomputable def jumpWork {n : ℕ} : Fin n → State → State → ℝ≥0∞ :=
  fun _ x y => match x, y with
    | .zero, .one => 1 / 2
    | .one, .zero => 2
    | _, _ => 1

/-- The Gibbs endpoint factors and boundary work have the prescribed
free-energy ratio. -/
theorem endpoint_balance (x y : State) :
    gibbsInitialWeight x * boundaryWork x y =
      freeEnergyWeight * gibbsFinalWeight y := by
  cases x <;> cases y
  · simp only [gibbsInitialWeight, boundaryWork, freeEnergyWeight,
      gibbsFinalWeight, mul_one]
    exact ENNReal.div_mul_cancel (a := (3 : ℝ≥0∞))
      (by norm_num) (by norm_num)
  · simp only [gibbsInitialWeight, boundaryWork, freeEnergyWeight,
      gibbsFinalWeight, mul_one]
    exact ENNReal.div_mul_cancel (a := (3 : ℝ≥0∞))
      (by norm_num) (by norm_num)
  · simp only [gibbsInitialWeight, boundaryWork, freeEnergyWeight,
      gibbsFinalWeight, mul_one]
    calc
      (4 / 3 : ℝ≥0∞) * (3 / 2) =
          (3⁻¹ * 3) * (2 * (2 * 2⁻¹)) := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
            ring
      _ = 2 := by
        rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        norm_num
  · simp only [gibbsInitialWeight, boundaryWork, freeEnergyWeight,
      gibbsFinalWeight, mul_one]
    calc
      (4 / 3 : ℝ≥0∞) * (3 / 2) =
          (3⁻¹ * 3) * (2 * (2 * 2⁻¹)) := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
            ring
      _ = 2 := by
        rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        norm_num

/-- Local jump balance holds with a genuinely nonconstant jump-work factor. -/
theorem jump_balance {n : ℕ} (i : Fin n) (x y : State) :
    JumpPath.jumpWeightOfRate jumpRate i x y * jumpWork i x y =
      JumpPath.jumpWeightOfRate jumpRate i y x := by
  cases x <;> cases y
  · norm_num [JumpPath.jumpWeightOfRate, jumpRate, jumpWork]
  · change (2 : ℝ≥0∞) * (1 / 2) = 1
    simpa using ENNReal.mul_div_cancel (a := (2 : ℝ≥0∞)) (b := 1)
      (by norm_num) (by norm_num)
  · norm_num [JumpPath.jumpWeightOfRate, jumpRate, jumpWork]
  · norm_num [JumpPath.jumpWeightOfRate, jumpRate, jumpWork]

/-- The asymmetric forward rate density is measurable. -/
theorem measurable_rateDensity (n : ℕ) :
    Measurable
      (JumpPath.rateDensity gibbsInitialWeight
        (escapeRate (n := n)) (jumpRate (n := n))) := by
  unfold JumpPath.rateDensity JumpPath.density
    JumpPath.holdingWeightOfEscapeRate gibbsInitialWeight escapeRate
    jumpRate JumpPath.jumpWeightOfRate
  fun_prop

/-- The aligned reverse rate density is measurable. -/
theorem measurable_alignedReverseRateDensity (n : ℕ) :
    Measurable
      (JumpPath.alignedReverseRateDensity gibbsFinalWeight
        (escapeRate (n := n)) (jumpRate (n := n))) := by
  unfold JumpPath.alignedReverseRateDensity JumpPath.alignedReverseDensity
    JumpPath.holdingWeightOfEscapeRate gibbsFinalWeight escapeRate
    jumpRate JumpPath.jumpWeightOfRate
  fun_prop

/-- The nonconstant work observable is measurable. -/
theorem measurable_rateWorkWeight (n : ℕ) :
    Measurable
      (JumpPath.rateWorkWeight boundaryWork (jumpWork (n := n))) := by
  unfold JumpPath.rateWorkWeight JumpPath.factorizedWorkWeight
    boundaryWork jumpWork
  fun_prop

theorem freeEnergyWeight_ne_one : freeEnergyWeight ≠ 1 := by
  norm_num [freeEnergyWeight]

/-- Sectorwise Crooks relation for the asymmetric chain, obtained directly
from the generic local-rate-balance theorem. -/
theorem sector_crooks (T : NNReal) (n : ℕ) :
    CrooksRelation
      (pathMeasure (TwoState.sectorReference T n)
        (JumpPath.rateDensity gibbsInitialWeight escapeRate jumpRate))
      (JumpPath.timeReversedMeasure
        (pathMeasure (TwoState.sectorReference T n)
          (JumpPath.reverseRateDensity gibbsFinalWeight escapeRate jumpRate)))
      (JumpPath.rateWorkWeight boundaryWork jumpWork)
      freeEnergyWeight := by
  apply JumpPath.crooks_of_rate_local_balance
    (TwoState.sectorReference T n) gibbsInitialWeight gibbsFinalWeight
    escapeRate escapeRate jumpRate jumpRate
    boundaryWork jumpWork freeEnergyWeight
  · exact TwoState.map_sectorReference_reverse T n
  · exact measurable_rateDensity n
  · exact measurable_alignedReverseRateDensity n
  · exact measurable_rateWorkWeight n
  · exact endpoint_balance
  · intro i x
    rfl
  · exact jump_balance

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
