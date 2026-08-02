/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDriven

/-!
# Rate detailed balance for driven jump windows

This module records the division-free finite-state detailed-balance hypothesis
used by every driven window and proves the finite-path telescoping identity for
its jump-rate factors.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω]

/-- Division-free detailed balance for nonnegative state weights and jump
rates. -/
def IsDetailedBalanceWeight
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞) : Prop :=
  ∀ x y,
    weight x * (G.jumpRate x y : ℝ≥0∞) =
      weight y * (G.jumpRate y x : ℝ≥0∞)

/-- Instantaneous Gibbs detailed balance for an energy landscape. -/
def IsGibbsDetailedBalance
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ) : Prop :=
  IsDetailedBalanceWeight G
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))

/-- Detailed balance telescopes along every finite state sequence: the forward
jump-rate product weighted at the initial state equals the reversed jump-rate
product weighted at the terminal state. -/
theorem weight_mul_jumpProduct_eq_reverse
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞)
    (hbalance : G.IsDetailedBalanceWeight weight)
    {n : ℕ} (states : Fin (n + 1) → Ω) :
    weight (states 0) * G.jumpProduct states =
      weight (states (Fin.last n)) *
        ∏ i : Fin n,
          (G.jumpRate (states i.succ) (states i.castSucc) : ℝ≥0∞) := by
  induction n with
  | zero =>
      simp [jumpProduct]
  | succ n ih =>
      let forwardTail : ℝ≥0∞ :=
        ∏ i : Fin n,
          (G.jumpRate (states i.succ.castSucc)
            (states i.succ.succ) : ℝ≥0∞)
      let reverseTail : ℝ≥0∞ :=
        ∏ i : Fin n,
          (G.jumpRate (states i.succ.succ)
            (states i.succ.castSucc) : ℝ≥0∞)
      have htail :
          weight (states 1) * forwardTail =
            weight (states (Fin.last (n + 1))) * reverseTail := by
        simpa [forwardTail, reverseTail, jumpProduct, Fin.succ_last] using
          ih (fun i : Fin (n + 1) => states i.succ)
      rw [jumpProduct, Fin.prod_univ_succ, Fin.prod_univ_succ]
      change
        weight (states 0) *
            ((G.jumpRate (states 0) (states 1) : ℝ≥0∞) * forwardTail) =
          weight (states (Fin.last (n + 1))) *
            ((G.jumpRate (states 1) (states 0) : ℝ≥0∞) * reverseTail)
      calc
        weight (states 0) *
              ((G.jumpRate (states 0) (states 1) : ℝ≥0∞) * forwardTail) =
            (weight (states 0) *
              (G.jumpRate (states 0) (states 1) : ℝ≥0∞)) *
                forwardTail := by ac_rfl
        _ = (weight (states 1) *
              (G.jumpRate (states 1) (states 0) : ℝ≥0∞)) *
                forwardTail := by
              rw [hbalance]
        _ = (G.jumpRate (states 1) (states 0) : ℝ≥0∞) *
              (weight (states 1) * forwardTail) := by ac_rfl
        _ = (G.jumpRate (states 1) (states 0) : ℝ≥0∞) *
              (weight (states (Fin.last (n + 1))) * reverseTail) := by
              rw [htail]
        _ = weight (states (Fin.last (n + 1))) *
              ((G.jumpRate (states 1) (states 0) : ℝ≥0∞) *
                reverseTail) := by ac_rfl

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
