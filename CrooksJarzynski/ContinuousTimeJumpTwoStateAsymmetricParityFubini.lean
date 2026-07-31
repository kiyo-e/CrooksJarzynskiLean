/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricParityCandidate
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini decomposition for asymmetric renewal
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- Fubini decomposition after appending one final free holding-time
coordinate. -/
theorem lintegral_cubeExpWeight_succ_transition
    {n : ℕ} (r : Fin (n + 1) → NNReal) (T : NNReal) (ρ : ℝ)
    (q : ℝ → ℝ≥0∞) (hq : Measurable q) :
    (∫⁻ u in freeSimplexSetAt (n + 1) ρ,
        cubeExpWeight r T u * q (residualAt ρ u)) =
      ∫⁻ v in freeSimplexSetAt n ρ,
        cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ v},
            ENNReal.ofReal
                (Real.exp
                  (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
              q (residualAt ρ v - (a : ℝ)) := by
  classical
  set F : I × (Fin n → I) → ℝ≥0∞ := fun p =>
    Set.indicator
      {z : I × (Fin n → I) |
        (z.1 : ℝ) + ∑ i, (z.2 i : ℝ) ≤ ρ}
      (fun z =>
        cubeExpWeight (fun i : Fin n => r i.castSucc) T z.2 *
          ENNReal.ofReal
            (Real.exp
              (-((r (Fin.last n) : ℝ) * (T : ℝ) * (z.1 : ℝ)))) *
          q (ρ - ((z.1 : ℝ) + ∑ i, (z.2 i : ℝ)))) p
    with hFdef
  have hFmeas : Measurable F := by
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_le (by fun_prop) measurable_const
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => I) (Fin.last n)
  set e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => I) (Fin.last n) with he
  have happly : ∀ u : Fin (n + 1) → I,
      e u = (u (Fin.last n), fun j : Fin n => u j.castSucc) := by
    intro u
    simp only [he, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.coe_mk, Equiv.symm_mk, Equiv.coe_fn_mk]
    refine congrArg (Prod.mk _) ?_
    funext j
    simp [Fin.removeNth_apply, Fin.succAbove_last]
  have hFe : ∀ u : Fin (n + 1) → I,
      F (e u) =
        (freeSimplexSetAt (n + 1) ρ).indicator
          (fun u => cubeExpWeight r T u * q (residualAt ρ u)) u := by
    intro u
    rw [happly u]
    by_cases hu : u ∈ freeSimplexSetAt (n + 1) ρ
    · have hsum : ∑ i, (u i : ℝ) ≤ ρ := hu
      rw [Fin.sum_univ_castSucc] at hsum
      have hmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∈
            {z : I × (Fin n → I) |
              (z.1 : ℝ) + ∑ i, (z.2 i : ℝ) ≤ ρ} := by
        change (u (Fin.last n) : ℝ) +
            ∑ j : Fin n, (u j.castSucc : ℝ) ≤ ρ
        linarith
      simp only [hFdef]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu]
      unfold cubeExpWeight residualAt
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      ring_nf
      have hprod :
          (∏ j : Fin n,
              ENNReal.ofReal
                (Real.exp
                  (-((r j.castSucc : ℝ) * (T : ℝ) *
                    (u j.castSucc : ℝ))))) =
            ∏ j : Fin n,
              ENNReal.ofReal
                (Real.exp
                  (-((T : ℝ) * (r j.castSucc : ℝ) *
                    (u j.castSucc : ℝ)))) := by
        apply Finset.prod_congr rfl
        intro j hj
        congr 2
        ring
      rw [hprod]
      ac_rfl
    · have hnotmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∉
            {z : I × (Fin n → I) |
              (z.1 : ℝ) + ∑ i, (z.2 i : ℝ) ≤ ρ} := by
        intro hmem
        apply hu
        change ∑ i, (u i : ℝ) ≤ ρ
        rw [Fin.sum_univ_castSucc]
        change (u (Fin.last n) : ℝ) +
          ∑ j : Fin n, (u j.castSucc : ℝ) ≤ ρ at hmem
        linarith
      simp only [hFdef]
      rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hu]
  have hsection : ∀ v : Fin n → I,
      (∫⁻ a : I, F (a, v)) =
        (freeSimplexSetAt n ρ).indicator
          (fun v =>
            cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ v},
                ENNReal.ofReal
                    (Real.exp
                      (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  q (residualAt ρ v - (a : ℝ))) v := by
    intro v
    by_cases hv : v ∈ freeSimplexSetAt n ρ
    · have hFav : ∀ a : I,
          F (a, v) =
            ({a : I | (a : ℝ) ≤ residualAt ρ v}).indicator
              (fun a : I =>
                cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                  (ENNReal.ofReal
                    (Real.exp
                      (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                    q (residualAt ρ v - (a : ℝ)))) a := by
        intro a
        simp only [hFdef]
        by_cases ha : (a : ℝ) ≤ residualAt ρ v
        · have hmem : ((a, v) : I × (Fin n → I)) ∈
              {z : I × (Fin n → I) |
                (z.1 : ℝ) + ∑ i, (z.2 i : ℝ) ≤ ρ} := by
            change (a : ℝ) + ∑ i, (v i : ℝ) ≤ ρ
            unfold residualAt at ha
            linarith
          rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem
              (show a ∈ {a : I | (a : ℝ) ≤ residualAt ρ v} from ha)]
          have hresidual :
              ρ - ((a : ℝ) + ∑ i, (v i : ℝ)) =
                residualAt ρ v - (a : ℝ) := by
            unfold residualAt
            ring
          rw [hresidual]
          ac_rfl
        · have hnotmem : ((a, v) : I × (Fin n → I)) ∉
              {z : I × (Fin n → I) |
                (z.1 : ℝ) + ∑ i, (z.2 i : ℝ) ≤ ρ} := by
            intro hmem
            apply ha
            have : (a : ℝ) + ∑ i, (v i : ℝ) ≤ ρ := hmem
            unfold residualAt
            linarith
          rw [Set.indicator_of_notMem hnotmem,
            Set.indicator_of_notMem
              (show a ∉ {a : I | (a : ℝ) ≤ residualAt ρ v} from ha)]
      rw [Set.indicator_of_mem hv]
      calc
        (∫⁻ a : I, F (a, v)) =
            ∫⁻ a : I,
              ({a : I | (a : ℝ) ≤ residualAt ρ v}).indicator
                (fun a : I =>
                  cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                    (ENNReal.ofReal
                      (Real.exp
                        (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                      q (residualAt ρ v - (a : ℝ)))) a :=
          lintegral_congr hFav
        _ = ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ v},
              cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                (ENNReal.ofReal
                  (Real.exp
                    (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  q (residualAt ρ v - (a : ℝ))) := by
          rw [lintegral_indicator
            (measurableSet_le (by fun_prop) measurable_const)]
        _ = cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ v},
                ENNReal.ofReal
                    (Real.exp
                      (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  q (residualAt ρ v - (a : ℝ)) := by
          rw [lintegral_const_mul' _ _ (by
            unfold cubeExpWeight
            exact ENNReal.prod_ne_top fun i hi => ENNReal.ofReal_ne_top)]
    · have hzero : ∀ a : I, F (a, v) = 0 := by
        intro a
        simp only [hFdef]
        apply Set.indicator_of_notMem
        intro hmem
        apply hv
        change ∑ i, (v i : ℝ) ≤ ρ
        have h0 : 0 ≤ (a : ℝ) := a.2.1
        have h1 : (a : ℝ) + ∑ i, (v i : ℝ) ≤ ρ := hmem
        linarith
      rw [Set.indicator_of_notMem hv]
      simp [hzero]
  calc
    (∫⁻ u in freeSimplexSetAt (n + 1) ρ,
        cubeExpWeight r T u * q (residualAt ρ u)) =
      ∫⁻ u,
        (freeSimplexSetAt (n + 1) ρ).indicator
          (fun u => cubeExpWeight r T u * q (residualAt ρ u)) u := by
        rw [lintegral_indicator (measurableSet_freeSimplexSetAt (n + 1) ρ)]
    _ = ∫⁻ u, F (e u) := by
      exact lintegral_congr fun u => (hFe u).symm
    _ = ∫⁻ p, F p := by
      rw [hmp.lintegral_comp hFmeas]
    _ = ∫⁻ v : Fin n → I, ∫⁻ a : I, F (a, v) := by
      rw [Measure.volume_eq_prod,
        lintegral_prod_symm F hFmeas.aemeasurable]
    _ = ∫⁻ v : Fin n → I,
        (freeSimplexSetAt n ρ).indicator
          (fun v =>
            cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ v},
                ENNReal.ofReal
                    (Real.exp
                      (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  q (residualAt ρ v - (a : ℝ))) v :=
      lintegral_congr hsection
    _ = _ := by
      rw [lintegral_indicator (measurableSet_freeSimplexSetAt n ρ)]

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski