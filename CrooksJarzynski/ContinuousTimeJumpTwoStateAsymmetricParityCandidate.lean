/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricFixedInitial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Renewal candidate for the asymmetric two-state parity sums

This module develops the variable-horizon sector masses and proves the
one-jump renewal equation for the explicit asymmetric transition matrix.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- The free simplex with a variable residual horizon `ρ`. -/
def freeSimplexSetAt (n : ℕ) (ρ : ℝ) : Set (Fin n → I) :=
  {u | ∑ i, (u i : ℝ) ≤ ρ}

theorem measurableSet_freeSimplexSetAt (n : ℕ) (ρ : ℝ) :
    MeasurableSet (freeSimplexSetAt n ρ) := by
  unfold freeSimplexSetAt
  exact measurableSet_le (by fun_prop) measurable_const

/-- The residual fraction after the free holding-time coordinates. -/
def residualAt {n : ℕ} (ρ : ℝ) (u : Fin n → I) : ℝ :=
  ρ - ∑ i, (u i : ℝ)

@[fun_prop]
theorem measurable_residualAt {n : ℕ} (ρ : ℝ) :
    Measurable (residualAt (n := n) ρ) := by
  unfold residualAt
  fun_prop

/-- The `n`-jump sector mass on a variable residual horizon `ρ`, with the
physical horizon scale `T` kept fixed.  At `ρ = 1` this is `sectorMass T x n`. -/
noncomputable def sectorMassAt
    (T : NNReal) (x : State) (n : ℕ) (ρ : ℝ) : ℝ≥0∞ :=
  ratePrefixProduct (chainRates x n) T *
    ∫⁻ u in freeSimplexSetAt n ρ,
      cubeExpWeight (chainRates x n) T u *
        ENNReal.ofReal
          (Real.exp
            (-((stateRate (iterateFlip n x) : ℝ) * (T : ℝ) *
              residualAt ρ u)))

theorem sectorMassAt_one (T : NNReal) (x : State) (n : ℕ) :
    sectorMassAt T x n 1 = sectorMass T x n := by
  unfold sectorMassAt sectorMass sectorIntegral freeSimplexSetAt residualAt
    Simplex.freeSimplexSet residual
  simp only [Simplex.coe_unitNNReal]

/-- The explicit transition probability, regarded as an `ENNReal` function of
an available residual fraction. -/
noncomputable def transitionCandidate
    (T : NNReal) (x y : State) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (asymmetricTransitionProbability ((T : ℝ) * ρ) x y)

@[fun_prop]
theorem measurable_transitionCandidate
    (T : NNReal) (x y : State) :
    Measurable (transitionCandidate T x y) := by
  cases x <;> cases y <;>
    unfold transitionCandidate asymmetricTransitionProbability <;> fun_prop

private theorem asymmetricTransitionProbability_nonneg_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (x y : State) :
    0 ≤ asymmetricTransitionProbability t x y := by
  change 0 ≤ asymmetricTransitionProbability
    (((⟨t, ht⟩ : NNReal) : ℝ)) x y
  exact asymmetricTransitionProbability_nonneg (⟨t, ht⟩ : NNReal) x y

private theorem asymmetricTransitionProbability_le_one_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (x y : State) :
    asymmetricTransitionProbability t x y ≤ 1 := by
  have hexp0 : 0 < Real.exp (-3 * t) := Real.exp_pos _
  have hexp1 : Real.exp (-3 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  cases x <;> cases y <;>
    simp only [asymmetricTransitionProbability] <;> nlinarith

theorem transitionCandidate_le_one
    (T : NNReal) (x y : State) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    transitionCandidate T x y ρ ≤ 1 := by
  unfold transitionCandidate
  rw [ENNReal.ofReal_le_one]
  exact asymmetricTransitionProbability_le_one_of_nonneg
    (mul_nonneg T.2 hρ) x y

/-- Convert a nonnegative continuous integral over an initial segment of the
unit interval into an ordinary interval integral. -/
private theorem lintegral_unitInterval_Iic_of_continuous_nonneg
    (f : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hf : Continuous f)
    (hfnn : ∀ z ∈ Set.Icc (0 : ℝ) ρ, 0 ≤ f z) :
    ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ}, ENNReal.ofReal (f (a : ℝ)) =
      ENNReal.ofReal (∫ z : ℝ in (0 : ℝ)..ρ, f z) := by
  have hpre :
      ((fun a : I => (a : ℝ)) ⁻¹' Set.Icc (0 : ℝ) ρ) =
        {a : I | (a : ℝ) ≤ ρ} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨a.2.1, h⟩⟩
  rw [← hpre]
  rw [unitInterval.measurePreserving_coe.setLIntegral_comp_preimage_emb
    unitInterval.measurableEmbedding_coe
    (fun z : ℝ => ENNReal.ofReal (f z)) (Set.Icc 0 ρ)]
  change (∫⁻ z : ℝ, ENNReal.ofReal (f z)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict
        (Set.Icc 0 ρ))) = _
  rw [Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl hρ1)]
  have hint : Integrable f (volume.restrict (Set.Icc 0 ρ)) :=
    hf.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) ρ)] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with z hz
    exact hfnn z hz
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hρ0]

/-- The explicit transition matrix satisfies the backward Kolmogorov equation. -/
private theorem hasDerivAt_asymmetricTransitionProbability
    (t : ℝ) (x y : State) :
    HasDerivAt
      (fun s : ℝ => asymmetricTransitionProbability s x y)
      (-(stateRate x : ℝ) * asymmetricTransitionProbability t x y +
        (stateRate x : ℝ) *
          asymmetricTransitionProbability t (flip x) y) t := by
  have hinner : HasDerivAt (fun s : ℝ => -3 * s) (-3) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (-3)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-3 * s))
      (-3 * Real.exp (-3 * t)) t := by
    exact hinner.exp.congr_deriv (by ring)
  cases x <;> cases y
  · refine ((hasDerivAt_const t (1 / 3 : ℝ)).add
      (hexp.const_mul (2 / 3 : ℝ))).congr_deriv ?_
    dsimp [asymmetricTransitionProbability, stateRate, flip]
    ring
  · refine ((hasDerivAt_const t (2 / 3 : ℝ)).sub
      (hexp.const_mul (2 / 3 : ℝ))).congr_deriv ?_
    dsimp [asymmetricTransitionProbability, stateRate, flip]
    ring
  · refine ((hasDerivAt_const t (1 / 3 : ℝ)).sub
      (hexp.const_mul (1 / 3 : ℝ))).congr_deriv ?_
    dsimp [asymmetricTransitionProbability, stateRate, flip]
    ring
  · refine ((hasDerivAt_const t (2 / 3 : ℝ)).add
      (hexp.const_mul (1 / 3 : ℝ))).congr_deriv ?_
    dsimp [asymmetricTransitionProbability, stateRate, flip]
    ring

/-- Real-valued first-jump renewal equation for the explicit transition
matrix. -/
set_option backward.isDefEq.respectTransparency false in
private theorem asymmetricTransitionProbability_renewal_real
    (T : NNReal) (ρ : ℝ) (x y : State) :
    asymmetricTransitionProbability ((T : ℝ) * ρ) x y =
      (if x = y then
        Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ))
       else 0) +
      (stateRate x : ℝ) * (T : ℝ) *
        (∫ a : ℝ in 0..ρ,
          Real.exp
              (-((stateRate x : ℝ) * (T : ℝ) * a)) *
            asymmetricTransitionProbability
              ((T : ℝ) * (ρ - a)) (flip x) y) := by
  let rate : ℝ := stateRate x
  let τ : ℝ := T
  let P : ℝ → ℝ := fun t => asymmetricTransitionProbability t x y
  let R : ℝ → ℝ := fun t =>
    asymmetricTransitionProbability t (flip x) y
  have hg : ∀ u : ℝ,
      HasDerivAt
        (fun s : ℝ => Real.exp (rate * τ * s) * P (τ * s))
        (rate * τ * Real.exp (rate * τ * u) * R (τ * u)) u := by
    intro u
    have hlinear : HasDerivAt (fun s : ℝ => rate * τ * s) (rate * τ) u := by
      simpa only [id_eq, mul_one, mul_assoc] using
        (hasDerivAt_id u).const_mul (rate * τ)
    have he : HasDerivAt (fun s : ℝ => Real.exp (rate * τ * s))
        (rate * τ * Real.exp (rate * τ * u)) u := by
      exact hlinear.exp.congr_deriv (by ring)
    have hinnerP : HasDerivAt
        (fun s : ℝ => -3 * (τ * s)) (-3 * τ) u := by
      simpa only [mul_assoc] using
        (hasDerivAt_id u).const_mul (-3 * τ)
    have hexpP : HasDerivAt
        (fun s : ℝ => Real.exp (-3 * (τ * s)))
        ((-3 * τ) * Real.exp (-3 * (τ * u))) u := by
      exact hinnerP.exp.congr_deriv (by ring)
    have hp : HasDerivAt (fun s : ℝ => P (τ * s))
        (τ * (-(stateRate x : ℝ) * P (τ * u) +
          (stateRate x : ℝ) * R (τ * u))) u := by
      cases x <;> cases y
      · refine ((hasDerivAt_const u (1 / 3 : ℝ)).add
          (hexpP.const_mul (2 / 3 : ℝ))).congr_deriv ?_
        dsimp [P, R, asymmetricTransitionProbability, stateRate, flip]
        ring
      · refine ((hasDerivAt_const u (2 / 3 : ℝ)).sub
          (hexpP.const_mul (2 / 3 : ℝ))).congr_deriv ?_
        dsimp [P, R, asymmetricTransitionProbability, stateRate, flip]
        ring
      · refine ((hasDerivAt_const u (1 / 3 : ℝ)).sub
          (hexpP.const_mul (1 / 3 : ℝ))).congr_deriv ?_
        dsimp [P, R, asymmetricTransitionProbability, stateRate, flip]
        ring
      · refine ((hasDerivAt_const u (2 / 3 : ℝ)).add
          (hexpP.const_mul (1 / 3 : ℝ))).congr_deriv ?_
        dsimp [P, R, asymmetricTransitionProbability, stateRate, flip]
        ring
    exact (he.mul hp).congr_deriv (by
      dsimp [rate, P, R]
      ring)
  have hRcont : Continuous R := by
    cases x <;> cases y <;>
      dsimp [R, asymmetricTransitionProbability, flip] <;> fun_prop
  have hExp : Continuous (fun u : ℝ => Real.exp (rate * τ * u)) := by
    fun_prop
  have hRτ : Continuous (fun u : ℝ => R (τ * u)) :=
    hRcont.comp (by fun_prop)
  have hIntegrand : Continuous
      (fun u : ℝ => rate * τ * Real.exp (rate * τ * u) * R (τ * u)) :=
    ((continuous_const.mul continuous_const).mul hExp).mul hRτ
  have hint : IntervalIntegrable
      (fun u : ℝ => rate * τ * Real.exp (rate * τ * u) * R (τ * u))
      volume 0 ρ :=
    hIntegrand.intervalIntegrable (μ := volume) 0 ρ
  have hftc :
      (∫ u : ℝ in 0..ρ,
        rate * τ * Real.exp (rate * τ * u) * R (τ * u)) =
        Real.exp (rate * τ * ρ) * P (τ * ρ) - P 0 := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ => Real.exp (rate * τ * s) * P (τ * s))
        (f' := fun u : ℝ =>
          rate * τ * Real.exp (rate * τ * u) * R (τ * u))
        (a := (0 : ℝ)) (b := ρ)
        (fun u _ => hg u) hint)
  have hgrewrite :
      Real.exp (rate * τ * ρ) * P (τ * ρ) =
        P 0 +
          (∫ u : ℝ in 0..ρ,
            rate * τ * Real.exp (rate * τ * u) * R (τ * u)) := by
    linarith
  have hrev :
      (∫ u : ℝ in 0..ρ,
        Real.exp (-((rate * τ) * (ρ - u))) * R (τ * u)) =
        ∫ a : ℝ in 0..ρ,
          Real.exp (-(rate * τ * a)) * R (τ * (ρ - a)) := by
    simpa [sub_sub_cancel, mul_assoc] using
      (intervalIntegral.integral_comp_sub_left
        (fun a : ℝ => Real.exp (-(rate * τ * a)) *
          R (τ * (ρ - a))) (d := ρ) (a := 0) (b := ρ))
  have hexp_cancel :
      Real.exp (-(rate * τ * ρ)) * Real.exp (rate * τ * ρ) = 1 := by
    rw [← Real.exp_add]
    have hzero : -(rate * τ * ρ) + rate * τ * ρ = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hfactor :
      (∫ u : ℝ in 0..ρ,
        rate * τ * Real.exp (rate * τ * u) * R (τ * u)) =
        rate * τ *
          (∫ u : ℝ in 0..ρ,
            Real.exp (rate * τ * u) * R (τ * u)) := by
    calc
      (∫ u : ℝ in 0..ρ,
        rate * τ * Real.exp (rate * τ * u) * R (τ * u)) =
          ∫ u : ℝ in 0..ρ,
            (rate * τ) * (Real.exp (rate * τ * u) * R (τ * u)) := by
              apply intervalIntegral.integral_congr
              intro u hu
              ring
      _ = _ := by
        exact intervalIntegral.integral_const_mul
          (μ := volume) (a := (0 : ℝ)) (b := ρ)
          (rate * τ)
          (fun u : ℝ => Real.exp (rate * τ * u) * R (τ * u))
  have hinter :
      Real.exp (-(rate * τ * ρ)) *
          (∫ u : ℝ in 0..ρ,
            rate * τ * Real.exp (rate * τ * u) * R (τ * u)) =
        rate * τ *
          (∫ a : ℝ in 0..ρ,
            Real.exp (-(rate * τ * a)) * R (τ * (ρ - a))) := by
    calc
      Real.exp (-(rate * τ * ρ)) *
          (∫ u : ℝ in 0..ρ,
            rate * τ * Real.exp (rate * τ * u) * R (τ * u)) =
          Real.exp (-(rate * τ * ρ)) *
            (rate * τ *
              ∫ u : ℝ in 0..ρ,
                Real.exp (rate * τ * u) * R (τ * u)) := by
                  rw [hfactor]
      _ = rate * τ *
            (Real.exp (-(rate * τ * ρ)) *
              ∫ u : ℝ in 0..ρ,
                Real.exp (rate * τ * u) * R (τ * u)) := by ring
      _ = rate * τ *
            ∫ u : ℝ in 0..ρ,
              Real.exp (-(rate * τ * ρ)) *
                (Real.exp (rate * τ * u) * R (τ * u)) := by
                  apply congrArg (fun z : ℝ => rate * τ * z)
                  exact (intervalIntegral.integral_const_mul
                    (μ := volume) (a := (0 : ℝ)) (b := ρ)
                    (Real.exp (-(rate * τ * ρ)))
                    (fun u : ℝ =>
                      Real.exp (rate * τ * u) * R (τ * u))).symm
      _ = rate * τ *
            ∫ u : ℝ in 0..ρ,
              Real.exp (-((rate * τ) * (ρ - u))) * R (τ * u) := by
                  apply congrArg (fun z : ℝ => rate * τ * z)
                  apply intervalIntegral.integral_congr
                  intro u hu
                  change Real.exp (-(rate * τ * ρ)) *
                      (Real.exp (rate * τ * u) * R (τ * u)) =
                    Real.exp (-((rate * τ) * (ρ - u))) * R (τ * u)
                  have hexp_u :
                      Real.exp (-(rate * τ * ρ)) *
                          Real.exp (rate * τ * u) =
                        Real.exp (-((rate * τ) * (ρ - u))) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
                  calc
                    Real.exp (-(rate * τ * ρ)) *
                        (Real.exp (rate * τ * u) * R (τ * u)) =
                      (Real.exp (-(rate * τ * ρ)) *
                        Real.exp (rate * τ * u)) * R (τ * u) := by
                          ring
                    _ = _ := by rw [hexp_u]
      _ = rate * τ *
            ∫ a : ℝ in 0..ρ,
              Real.exp (-(rate * τ * a)) * R (τ * (ρ - a)) := by
                  rw [hrev]
  calc
    asymmetricTransitionProbability ((T : ℝ) * ρ) x y = P (τ * ρ) := by
      rfl
    _ = Real.exp (-(rate * τ * ρ)) *
        (Real.exp (rate * τ * ρ) * P (τ * ρ)) := by
      rw [← mul_assoc, hexp_cancel, one_mul]
    _ = Real.exp (-(rate * τ * ρ)) *
        (P 0 +
          ∫ u : ℝ in 0..ρ,
            rate * τ * Real.exp (rate * τ * u) * R (τ * u)) := by
      rw [hgrewrite]
    _ = Real.exp (-(rate * τ * ρ)) * P 0 +
        rate * τ *
          (∫ a : ℝ in 0..ρ,
            Real.exp (-(rate * τ * a)) * R (τ * (ρ - a))) := by
      rw [mul_add, hinter]
    _ = (if x = y then
          Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ))
        else 0) +
        (stateRate x : ℝ) * (T : ℝ) *
          (∫ a : ℝ in 0..ρ,
            Real.exp
                (-((stateRate x : ℝ) * (T : ℝ) * a)) *
              asymmetricTransitionProbability
                ((T : ℝ) * (ρ - a)) (flip x) y) := by
      rw [show P 0 = if x = y then 1 else 0 by
        simpa [P] using asymmetricTransitionProbability_zero x y]
      simp only [P, R, rate, τ]
      split_ifs <;> ring

/-- The explicit transition matrix satisfies the one-jump renewal equation. -/
theorem transitionCandidate_renewal
    (T : NNReal) (x y : State) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    transitionCandidate T x y ρ =
      (if x = y then
        ENNReal.ofReal
          (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ)))
      else 0) +
      ((stateRate x : ℝ≥0∞) * (T : ℝ≥0∞)) *
        ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
          ENNReal.ofReal
              (Real.exp
                (-((stateRate x : ℝ) * (T : ℝ) * (a : ℝ)))) *
            transitionCandidate T (flip x) y (ρ - (a : ℝ)) := by
  let f : ℝ → ℝ := fun a =>
    Real.exp (-((stateRate x : ℝ) * (T : ℝ) * a)) *
      asymmetricTransitionProbability
        ((T : ℝ) * (ρ - a)) (flip x) y
  have hfcont : Continuous f := by
    cases x <;> cases y <;>
      simp [f, asymmetricTransitionProbability, flip, stateRate] <;>
      fun_prop
  have hfnn : ∀ a ∈ Set.Icc (0 : ℝ) ρ, 0 ≤ f a := by
    intro a ha
    have htime : 0 ≤ (T : ℝ) * (ρ - a) :=
      mul_nonneg T.2 (sub_nonneg.mpr ha.2)
    exact mul_nonneg (Real.exp_pos _).le
      (asymmetricTransitionProbability_nonneg_of_nonneg
        htime (flip x) y)
  have hlin :
      (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
        ENNReal.ofReal
            (Real.exp
              (-((stateRate x : ℝ) * (T : ℝ) * (a : ℝ)))) *
          transitionCandidate T (flip x) y (ρ - (a : ℝ))) =
        ENNReal.ofReal (∫ a : ℝ in (0 : ℝ)..ρ, f a) := by
    rw [← lintegral_unitInterval_Iic_of_continuous_nonneg
      f ρ hρ0 hρ1 hfcont hfnn]
    apply setLIntegral_congr_fun
      (measurableSet_le (by fun_prop) measurable_const)
    intro a ha
    unfold transitionCandidate f
    change
      ENNReal.ofReal
          (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * (a : ℝ)))) *
        ENNReal.ofReal
          (asymmetricTransitionProbability
            ((T : ℝ) * (ρ - (a : ℝ))) (flip x) y) =
      ENNReal.ofReal
        (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * (a : ℝ))) *
          asymmetricTransitionProbability
            ((T : ℝ) * (ρ - (a : ℝ))) (flip x) y)
    exact (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  have hint_nonneg : 0 ≤ ∫ a : ℝ in (0 : ℝ)..ρ, f a := by
    rw [intervalIntegral.integral_of_le hρ0]
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    exact hfnn a ⟨ha.1.le, ha.2⟩
  have hreal := asymmetricTransitionProbability_renewal_real T ρ x y
  have hsurv :
      0 ≤ (if x = y then
        Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ)) else 0) := by
    split_ifs <;> positivity
  have hrate : 0 ≤ (stateRate x : ℝ) * (T : ℝ) := by positivity
  have hcast :
      ENNReal.ofReal ((stateRate x : ℝ) * (T : ℝ)) =
        (stateRate x : ℝ≥0∞) * (T : ℝ≥0∞) := by
    symm
    rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_mul]
  calc
    transitionCandidate T x y ρ =
        ENNReal.ofReal
          ((if x = y then
              Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ))
            else 0) +
            (stateRate x : ℝ) * (T : ℝ) *
              (∫ a : ℝ in (0 : ℝ)..ρ, f a)) := by
      unfold transitionCandidate
      rw [hreal]
    _ = ENNReal.ofReal
          (if x = y then
            Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ))
          else 0) +
        ENNReal.ofReal
          ((stateRate x : ℝ) * (T : ℝ) *
            (∫ a : ℝ in (0 : ℝ)..ρ, f a)) := by
      rw [ENNReal.ofReal_add hsurv (mul_nonneg hrate hint_nonneg)]
    _ = ENNReal.ofReal
          (if x = y then
            Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ))
          else 0) +
        ENNReal.ofReal ((stateRate x : ℝ) * (T : ℝ)) *
          ENNReal.ofReal (∫ a : ℝ in (0 : ℝ)..ρ, f a) := by
      rw [ENNReal.ofReal_mul hrate]
    _ = ENNReal.ofReal
          (if x = y then
            Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ))
          else 0) +
        ((stateRate x : ℝ≥0∞) * (T : ℝ≥0∞)) *
          (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
            ENNReal.ofReal
                (Real.exp
                  (-((stateRate x : ℝ) * (T : ℝ) * (a : ℝ)))) *
              transitionCandidate T (flip x) y (ρ - (a : ℝ))) := by
      rw [hcast, hlin]
    _ = (if x = y then
          ENNReal.ofReal
            (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ)))
        else 0) +
        ((stateRate x : ℝ≥0∞) * (T : ℝ≥0∞)) *
          (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
            ENNReal.ofReal
                (Real.exp
                  (-((stateRate x : ℝ) * (T : ℝ) * (a : ℝ)))) *
              transitionCandidate T (flip x) y (ρ - (a : ℝ))) := by
      by_cases hxy : x = y <;> simp [hxy]

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
