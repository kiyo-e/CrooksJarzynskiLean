/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcat

/-!
# Density factorization for concatenated jump paths

This module proves the deterministic density factorization used by the
path-law composition.  For time-homogeneous escape and jump rates, gluing two
paths at a shared state multiplies their rate densities; the exponential
survival factors at the seam split across the sum of the two holding times.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem holdingWeightOfEscapeRate_add
    {q : ℕ} (i : Fin (q + 1))
    (escapeRate : Ω → NNReal) (x : Ω) (a b : NNReal) :
    holdingWeightOfEscapeRate (fun _ => escapeRate) i x (a + b) =
      holdingWeightOfEscapeRate (fun _ => escapeRate) i x a *
        holdingWeightOfEscapeRate (fun _ => escapeRate) i x b := by
  unfold holdingWeightOfEscapeRate
  rw [show -((escapeRate x : ℝ) * ((a + b : NNReal) : ℝ)) =
      -((escapeRate x : ℝ) * (a : ℝ)) +
        -((escapeRate x : ℝ) * (b : ℝ)) by
    push_cast
    ring]
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

omit [MeasurableSpace Ω] in
private theorem rateDensity_succ
    {k : ℕ} (η : JumpPath Ω (k + 1))
    (initialWeight : Ω → ℝ≥0∞)
    (escapeRate : Ω → NNReal) (jumpRate : Ω → Ω → NNReal) :
    rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate) η =
      rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate)
          (dropLast η) *
        (jumpRate ((dropLast η).1 (Fin.last k))
          (η.1 (Fin.last (k + 1))) : ℝ≥0∞) *
        holdingWeightOfEscapeRate (fun _ => escapeRate) (Fin.last (k + 1))
          (η.1 (Fin.last (k + 1))) (η.2 (Fin.last (k + 1))) := by
  unfold rateDensity density jumpWeightOfRate
  rw [Fin.prod_univ_castSucc]
  unfold holdingWeightOfEscapeRate
  simp [dropLast]
  ring

omit [MeasurableSpace Ω] in
/-- For time-homogeneous rates, the rate density of two paths glued at a
shared boundary state is the product of their rate densities. -/
theorem rateDensity_concat [DecidableEq Ω]
    {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (initialWeight : Ω → ℝ≥0∞)
    (escapeRate : Ω → NNReal) (jumpRate : Ω → Ω → NNReal)
    (hmatch : γ.1 (Fin.last n) = δ.1 0) :
    rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate)
        (concat γ δ) =
      rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate) γ *
        rateDensity (FiniteJumpGenerator.fixedInitialWeight (δ.1 0))
          (fun _ => escapeRate) (fun _ => jumpRate) δ := by
  induction m with
  | zero =>
      simp only [Nat.add_zero]
      unfold rateDensity density jumpWeightOfRate
      have hprod :
          (∏ i : Fin n,
            holdingWeightOfEscapeRate (fun _ => escapeRate) i.castSucc
                ((concat γ δ).1 i.castSucc) ((concat γ δ).2 i.castSucc) *
              (jumpRate ((concat γ δ).1 i.castSucc)
                ((concat γ δ).1 i.succ) : ℝ≥0∞)) =
            ∏ i : Fin n,
              holdingWeightOfEscapeRate (fun _ => escapeRate) i.castSucc
                  (γ.1 i.castSucc) (γ.2 i.castSucc) *
                (jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ≥0∞) := by
        apply Finset.prod_congr rfl
        intro i _
        have hi : i.castSucc ≠ Fin.last n := by simp
        have hstate0 : (concat γ δ).1 i.castSucc = γ.1 i.castSucc := by
          have hidx : i.castSucc =
              Fin.cast (by omega : (n + 1) + 0 = n + 0 + 1)
                (Fin.castAdd 0 i.castSucc) := by
            apply Fin.ext
            simp
          calc
            (concat γ δ).1 i.castSucc =
                (concat γ δ).1 (Fin.cast (by omega) (Fin.castAdd 0 i.castSucc)) :=
              congrArg (concat γ δ).1 hidx
            _ = γ.1 i.castSucc := concat_fst_castAdd γ δ i.castSucc
        have hstate1 : (concat γ δ).1 i.succ = γ.1 i.succ := by
          have hidx : i.succ =
              Fin.cast (by omega : (n + 1) + 0 = n + 0 + 1)
                (Fin.castAdd 0 i.succ) := by
            apply Fin.ext
            simp
          calc
            (concat γ δ).1 i.succ =
                (concat γ δ).1 (Fin.cast (by omega) (Fin.castAdd 0 i.succ)) :=
              congrArg (concat γ δ).1 hidx
            _ = γ.1 i.succ := concat_fst_castAdd γ δ i.succ
        have hholding : (concat γ δ).2 i.castSucc = γ.2 i.castSucc := by
          have hidx : i.castSucc =
              Fin.cast (by omega : (n + 1) + 0 = n + 0 + 1)
                (Fin.castAdd 0 i.castSucc) := by
            apply Fin.ext
            simp
          calc
            (concat γ δ).2 i.castSucc =
                (concat γ δ).2 (Fin.cast (by omega) (Fin.castAdd 0 i.castSucc)) :=
              congrArg (concat γ δ).2 hidx
            _ = if i.castSucc = Fin.last n then
                  γ.2 i.castSucc + δ.2 0 else γ.2 i.castSucc :=
              concat_snd_castAdd γ δ i.castSucc
            _ = γ.2 i.castSucc := if_neg hi
        rw [hstate0, hstate1, hholding]
      have hlastState : (concat γ δ).1 (Fin.last n) = γ.1 (Fin.last n) := by
        simpa using concat_fst_castAdd (m := 0) γ δ (Fin.last n)
      have hboundary : (concat γ δ).2 (Fin.last n) =
          γ.2 (Fin.last n) + δ.2 0 := by
        have hidx : (Fin.last n : Fin (n + 1)) = ⟨n, by omega⟩ := by
          apply Fin.ext
          simp
        calc
          (concat γ δ).2 (Fin.last n) = (concat γ δ).2 ⟨n, by omega⟩ :=
            congrArg (concat γ δ).2 hidx
          _ = γ.2 (Fin.last n) + δ.2 0 := concat_snd_boundary γ δ
      rw [concat_state_zero, hprod, hlastState, hboundary,
        FiniteJumpGenerator.fixedInitialWeight_self]
      simp only [Fin.prod_univ_zero, mul_one, one_mul]
      rw [holdingWeightOfEscapeRate_add (Fin.last n) escapeRate]
      rw [hmatch]
      unfold holdingWeightOfEscapeRate
      simp
      ring
  | succ m ih =>
      have hconcatSucc := rateDensity_succ (k := n + m)
        (@concat Ω n (m + 1) γ δ) initialWeight escapeRate jumpRate
      have hlastDrop :
          (concat γ (dropLast δ)).1 (Fin.last (n + m)) =
            (dropLast δ).1 (Fin.last m) :=
        concat_state_last γ (dropLast δ) (by simpa [dropLast] using hmatch)
      have hlast :
          (concat γ δ).1 (Fin.last (n + (m + 1))) =
            δ.1 (Fin.last (m + 1)) :=
        concat_state_last γ δ hmatch
      have hholding :
          (concat γ δ).2 (Fin.last (n + (m + 1))) =
            δ.2 (Fin.last (m + 1)) := by
        have hidx : Fin.last (n + (m + 1)) =
            Fin.cast (by omega : (n + 1) + (m + 1) = n + (m + 1) + 1)
              (Fin.natAdd (n + 1) (Fin.last m)) := by
          apply Fin.ext
          simp
          omega
        calc
          (concat γ δ).2 (Fin.last (n + (m + 1))) =
              (concat γ δ).2
                (Fin.cast (by omega) (Fin.natAdd (n + 1) (Fin.last m))) :=
            congrArg (concat γ δ).2 hidx
          _ = δ.2 (Fin.last (m + 1)) := by
            simpa using concat_snd_natAdd (n := n) γ δ (Fin.last m)
      have hlast' :
          (concat γ δ).1 (Fin.last (n + m + 1)) =
            δ.1 (Fin.last (m + 1)) := by
        have hidx : Fin.last (n + m + 1) = Fin.last (n + (m + 1)) := by
          apply Fin.ext
          simp
          omega
        calc
          (concat γ δ).1 (Fin.last (n + m + 1)) =
              (concat γ δ).1 (Fin.last (n + (m + 1))) :=
            congrArg (concat γ δ).1 hidx
          _ = δ.1 (Fin.last (m + 1)) := hlast
      have hholding' :
          (concat γ δ).2 (Fin.last (n + m + 1)) =
            δ.2 (Fin.last (m + 1)) := by
        have hidx : Fin.last (n + m + 1) = Fin.last (n + (m + 1)) := by
          apply Fin.ext
          simp
          omega
        calc
          (concat γ δ).2 (Fin.last (n + m + 1)) =
              (concat γ δ).2 (Fin.last (n + (m + 1))) :=
            congrArg (concat γ δ).2 hidx
          _ = δ.2 (Fin.last (m + 1)) := hholding
      have hdeltaSucc := rateDensity_succ (k := m) δ
        (FiniteJumpGenerator.fixedInitialWeight (δ.1 0)) escapeRate jumpRate
      calc
        rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate)
            (@concat Ω n (m + 1) γ δ) =
            rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate)
                (dropLast (@concat Ω n (m + 1) γ δ)) *
              (jumpRate ((dropLast (@concat Ω n (m + 1) γ δ)).1 (Fin.last (n + m)))
                ((@concat Ω n (m + 1) γ δ).1 (Fin.last (n + m + 1))) : ℝ≥0∞) *
              holdingWeightOfEscapeRate (fun _ => escapeRate)
                (Fin.last (n + m + 1))
                ((@concat Ω n (m + 1) γ δ).1 (Fin.last (n + m + 1)))
                ((@concat Ω n (m + 1) γ δ).2 (Fin.last (n + m + 1))) := hconcatSucc
        _ = (rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate) γ *
                rateDensity (FiniteJumpGenerator.fixedInitialWeight (δ.1 0))
                  (fun _ => escapeRate) (fun _ => jumpRate) (dropLast δ)) *
              (jumpRate ((dropLast δ).1 (Fin.last m))
                (δ.1 (Fin.last (m + 1))) : ℝ≥0∞) *
              holdingWeightOfEscapeRate (fun _ => escapeRate) (Fin.last (m + 1))
                (δ.1 (Fin.last (m + 1))) (δ.2 (Fin.last (m + 1))) := by
          rw [dropLast_concat]
          have hi := ih (dropLast δ) (by simpa [dropLast] using hmatch)
          calc
            rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate)
                  (concat γ (dropLast δ)) *
                (jumpRate ((concat γ (dropLast δ)).1 (Fin.last (n + m)))
                  ((concat γ δ).1 (Fin.last (n + m + 1))) : ℝ≥0∞) *
                holdingWeightOfEscapeRate (fun _ => escapeRate)
                  (Fin.last (n + m + 1))
                  ((concat γ δ).1 (Fin.last (n + m + 1)))
                  ((concat γ δ).2 (Fin.last (n + m + 1))) =
                (rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate) γ *
                    rateDensity
                      (FiniteJumpGenerator.fixedInitialWeight ((dropLast δ).1 0))
                      (fun _ => escapeRate) (fun _ => jumpRate) (dropLast δ)) *
                  (jumpRate ((concat γ (dropLast δ)).1 (Fin.last (n + m)))
                    ((concat γ δ).1 (Fin.last (n + m + 1))) : ℝ≥0∞) *
                  holdingWeightOfEscapeRate (fun _ => escapeRate)
                    (Fin.last (n + m + 1))
                    ((concat γ δ).1 (Fin.last (n + m + 1)))
                    ((concat γ δ).2 (Fin.last (n + m + 1))) :=
              congrArg (fun z => z *
                (jumpRate ((concat γ (dropLast δ)).1 (Fin.last (n + m)))
                  ((concat γ δ).1 (Fin.last (n + m + 1))) : ℝ≥0∞) *
                holdingWeightOfEscapeRate (fun _ => escapeRate)
                  (Fin.last (n + m + 1))
                  ((concat γ δ).1 (Fin.last (n + m + 1)))
                  ((concat γ δ).2 (Fin.last (n + m + 1)))) hi
            _ = _ := by
              rw [hlastDrop, hlast', hholding']
              unfold holdingWeightOfEscapeRate
              rfl
        _ = rateDensity initialWeight (fun _ => escapeRate) (fun _ => jumpRate) γ *
              rateDensity (FiniteJumpGenerator.fixedInitialWeight (δ.1 0))
                (fun _ => escapeRate) (fun _ => jumpRate) δ := by
          rw [hdeltaSucc]
          ring

end JumpPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Generator-specialized density factorization for concatenated paths. -/
theorem rateDensity_concat
    (G : FiniteJumpGenerator Ω) {n m : ℕ}
    (γ : JumpPath Ω n) (δ : JumpPath Ω m) (x : Ω)
    (hmatch : γ.1 (Fin.last n) = δ.1 0) :
    JumpPath.rateDensity (fixedInitialWeight x)
        G.pathEscapeRate G.pathJumpRate (JumpPath.concat γ δ) =
      JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate γ *
        JumpPath.rateDensity (fixedInitialWeight (δ.1 0))
          G.pathEscapeRate G.pathJumpRate δ := by
  exact JumpPath.rateDensity_concat γ δ (fixedInitialWeight x)
    G.escapeRate G.jumpRate hmatch

end FiniteJumpGenerator

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
