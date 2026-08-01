/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorPathLaw
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricRenewalEquation

/-!
# Peeling the first holding coordinate

The renewal equation runs in the horizon direction, so it needs the holding-time
integral of an `(n+1)`-jump sector expressed through the `n`-jump one on a
shorter horizon.  Splitting off the *first* coordinate is what achieves that:
the remaining coordinates then describe the same process started from the state
reached by the first jump.

Everything here happens at a fixed chart scale `T`, with only the available
fraction `ρ` shrinking.  That is what keeps a rescaling of the chart -- and its
Jacobian -- out of the argument entirely.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

open TwoState.AsymmetricExample (cubeExpWeight residualAt)

universe u

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The holding-time integral of one state sequence on a variable available
fraction `ρ` of the horizon, with the horizon scale `T` held fixed.  At `ρ = 1`
this is `holdingIntegral`. -/
noncomputable def holdingIntegralAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in TwoState.AsymmetricExample.freeSimplexSetAt n ρ,
    cubeExpWeight (G.stateEscapeRates states) T u *
      ENNReal.ofReal
        (Real.exp
          (-((G.escapeRate (states (Fin.last n)) : ℝ) * (T : ℝ) *
            residualAt ρ u)))

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem holdingIntegralAt_one
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    G.holdingIntegralAt T states 1 = G.holdingIntegral T states := by
  unfold holdingIntegralAt holdingIntegral
    TwoState.AsymmetricExample.freeSimplexSetAt Simplex.freeSimplexSet
    residualAt TwoState.AsymmetricExample.residual
  simp only [Simplex.coe_unitNNReal]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The escape rates of the shifted sequence are the tail of the original ones:
coordinate `j` of the shifted sequence is spent in the same state as coordinate
`j + 1` of the original. -/
theorem stateEscapeRates_succ
    (G : FiniteJumpGenerator Ω) {n : ℕ} (states : Fin (n + 2) → Ω) :
    G.stateEscapeRates (fun i : Fin (n + 1) => states i.succ) =
      fun j : Fin n => G.stateEscapeRates states j.succ := by
  funext j
  simp only [stateEscapeRates]
  rw [Fin.succ_castSucc]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem stateEscapeRates_zero
    (G : FiniteJumpGenerator Ω) {n : ℕ} (states : Fin (n + 2) → Ω) :
    G.stateEscapeRates states 0 = G.escapeRate (states 0) := by
  simp [stateEscapeRates]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **Peeling the first holding coordinate.**  The first jump leaves at a time
`T v`, and the rest of the path is the same construction for the shifted state
sequence on the remaining fraction `ρ - v`.

The chart scale never changes, so no rescaling of the simplex is involved: only
the available fraction shrinks. -/
theorem holdingIntegralAt_succ
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 2) → Ω) (ρ : ℝ) :
    G.holdingIntegralAt T states ρ =
      ∫⁻ v : I,
        ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * (v : ℝ)))) *
          G.holdingIntegralAt T (fun i : Fin (n + 1) => states i.succ)
            (ρ - (v : ℝ)) := by
  classical
  set r : Fin (n + 1) → NNReal := G.stateEscapeRates states with hr
  set c : NNReal := G.escapeRate (states (Fin.last (n + 1))) with hc
  set head : I → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (Real.exp (-((r 0 : ℝ) * (T : ℝ) * (a : ℝ)))) with hhead
  set tail : ℝ → (Fin n → I) → ℝ≥0∞ := fun frac w =>
    cubeExpWeight (fun j : Fin n => r j.succ) T w *
      ENNReal.ofReal
        (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt frac w))) with htail
  set g : I × (Fin n → I) → ℝ≥0∞ :=
    {p : I × (Fin n → I) | (p.1 : ℝ) + ∑ j, (p.2 j : ℝ) ≤ ρ}.indicator
      (fun p => head p.1 * tail (ρ - (p.1 : ℝ)) p.2) with hg
  have hcond : MeasurableSet
      {p : I × (Fin n → I) | (p.1 : ℝ) + ∑ j, (p.2 j : ℝ) ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hbody : Measurable
      fun p : I × (Fin n → I) => head p.1 * tail (ρ - (p.1 : ℝ)) p.2 := by
    simp only [hhead, htail, residualAt]
    refine Measurable.mul (by fun_prop) (Measurable.mul ?_ (by fun_prop))
    exact (TwoState.AsymmetricExample.measurable_cubeExpWeight
      (fun j : Fin n => r j.succ) T).comp measurable_snd
  have hgmeas : Measurable g := hbody.indicator hcond
  -- The pulled-back integrand is the indicator of the full simplex.
  have hpull : ∀ u : Fin (n + 1) → I,
      g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0 u) =
        (TwoState.AsymmetricExample.freeSimplexSetAt (n + 1) ρ).indicator
          (fun w => cubeExpWeight r T w *
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt ρ w)))) u := by
    intro u
    have hchart :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0 u) =
          (u 0, fun j : Fin n => u j.succ) := rfl
    have hsum : (u 0 : ℝ) + ∑ j : Fin n, (u j.succ : ℝ) =
        ∑ i : Fin (n + 1), (u i : ℝ) :=
      (Fin.sum_univ_succ (fun i : Fin (n + 1) => (u i : ℝ))).symm
    rw [hchart]
    simp only [hg, Set.indicator_apply,
      TwoState.AsymmetricExample.freeSimplexSetAt, Set.mem_setOf_eq, hsum]
    split_ifs with hmem
    · have hres : residualAt (ρ - (u 0 : ℝ)) (fun j : Fin n => u j.succ) =
          residualAt ρ u := by
        simp only [residualAt]
        rw [← hsum]
        ring
      have hprod : head (u 0) *
          cubeExpWeight (fun j : Fin n => r j.succ) T
            (fun j : Fin n => u j.succ) = cubeExpWeight r T u := by
        simp only [hhead, TwoState.AsymmetricExample.cubeExpWeight]
        rw [Fin.prod_univ_succ]
      rw [htail]
      dsimp only
      rw [hres, ← mul_assoc, hprod]
    · rfl
  -- Transport to the product chart and use Fubini.
  have hstep :
      G.holdingIntegralAt T states ρ =
        ∫⁻ a : I, ∫⁻ w : Fin n → I, g (a, w) := by
    unfold holdingIntegralAt
    rw [← hr, ← hc,
      ← lintegral_indicator
        (TwoState.AsymmetricExample.measurableSet_freeSimplexSetAt (n + 1) ρ)]
    rw [show (∫⁻ u : Fin (n + 1) → I,
        (TwoState.AsymmetricExample.freeSimplexSetAt (n + 1) ρ).indicator
          (fun w => cubeExpWeight r T w *
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt ρ w)))) u) =
        ∫⁻ u : Fin (n + 1) → I,
          g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0 u) from
      lintegral_congr fun u => (hpull u).symm]
    rw [(volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => I) 0).lintegral_comp hgmeas]
    rw [Measure.volume_eq_prod, lintegral_prod _ hgmeas.aemeasurable]
  rw [hstep]
  refine lintegral_congr fun a => ?_
  have hinner : ∀ w : Fin n → I,
      g (a, w) =
        (TwoState.AsymmetricExample.freeSimplexSetAt n (ρ - (a : ℝ))).indicator
          (fun w => head a * tail (ρ - (a : ℝ)) w) w := by
    intro w
    simp only [hg, Set.indicator_apply,
      TwoState.AsymmetricExample.freeSimplexSetAt, Set.mem_setOf_eq]
    have hiff : ((a : ℝ) + ∑ j, (w j : ℝ) ≤ ρ) ↔ (∑ j, (w j : ℝ) ≤ ρ - (a : ℝ)) := by
      constructor <;> intro h <;> linarith
    simp only [hiff]
  simp_rw [hinner]
  rw [lintegral_indicator
    (TwoState.AsymmetricExample.measurableSet_freeSimplexSetAt n (ρ - (a : ℝ)))]
  rw [lintegral_const_mul' _ _ (by simp [hhead] : head a ≠ ∞)]
  congr 1

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
