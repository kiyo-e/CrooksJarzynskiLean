/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricFixedInitial
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Renewal evaluation of the asymmetric two-state parity sums

This module closes the remaining analytic gap between the fixed-initial
asymmetric path law and the explicit transition matrix. The proof expands the
explicit transition probability through its one-jump renewal equation. After
`N` renewals, the first `N` jump sectors appear explicitly and the remainder is
bounded by the `N`-jump arrival mass. The previously proved Poisson-type tail
bound makes that remainder vanish.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- The free simplex with a variable residual horizon `ρ`. -/
private def freeSimplexSetAt (n : ℕ) (ρ : ℝ) : Set (Fin n → I) :=
  {u | ∑ i, (u i : ℝ) ≤ ρ}

private theorem measurableSet_freeSimplexSetAt (n : ℕ) (ρ : ℝ) :
    MeasurableSet (freeSimplexSetAt n ρ) := by
  unfold freeSimplexSetAt
  exact measurableSet_le (by fun_prop) measurable_const

/-- The residual fraction after the free holding-time coordinates. -/
private def residualAt {n : ℕ} (ρ : ℝ) (u : Fin n → I) : ℝ :=
  ρ - ∑ i, (u i : ℝ)

@[fun_prop]
private theorem measurable_residualAt {n : ℕ} (ρ : ℝ) :
    Measurable (residualAt (n := n) ρ) := by
  unfold residualAt
  fun_prop

/-- The `n`-jump sector mass on a variable residual horizon `ρ`, with the
physical horizon scale `T` kept fixed. At `ρ = 1` this is `sectorMass T x n`. -/
private noncomputable def sectorMassAt
    (T : NNReal) (x : State) (n : ℕ) (ρ : ℝ) : ℝ≥0∞ :=
  ratePrefixProduct (chainRates x n) T *
    ∫⁻ u in freeSimplexSetAt n ρ,
      cubeExpWeight (chainRates x n) T u *
        ENNReal.ofReal
          (Real.exp
            (-((stateRate (iterateFlip n x) : ℝ) * (T : ℝ) *
              residualAt ρ u)))

private theorem sectorMassAt_one (T : NNReal) (x : State) (n : ℕ) :
    sectorMassAt T x n 1 = sectorMass T x n := by
  unfold sectorMassAt sectorMass sectorIntegral freeSimplexSetAt residualAt
    Simplex.freeSimplexSet residual
  simp only [Simplex.coe_unitNNReal]

/-- The explicit transition probability, regarded as an `ENNReal` function of
an available residual fraction. -/
private noncomputable def transitionCandidate
    (T : NNReal) (x y : State) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (asymmetricTransitionProbability ((T : ℝ) * ρ) x y)

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

private theorem transitionCandidate_le_one
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

private theorem intervalIntegral_exp_mul
    (k ρ : ℝ) (hk : k ≠ 0) :
    (∫ z : ℝ in (0 : ℝ)..ρ, Real.exp (k * z)) =
      (Real.exp (k * ρ) - 1) / k := by
  rw [intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := ρ) (fun z : ℝ => Real.exp z) hk,
    integral_exp]
  simp only [smul_eq_mul, mul_zero, Real.exp_zero]
  field_simp

/-- The explicit transition matrix satisfies the one-jump renewal equation. -/
private theorem transitionCandidate_renewal
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
  let t : ℝ := (T : ℝ)
  have ht0 : 0 ≤ t := T.2
  by_cases hT : T = 0
  · subst T
    cases x <;> cases y <;>
      simp [transitionCandidate, asymmetricTransitionProbability, stateRate, flip, t]
  have ht : t ≠ 0 := by
    simp [t, hT]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  have hmeasSet : MeasurableSet {a : I | (a : ℝ) ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hlintegral (x' y' : State) :
      (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
          ENNReal.ofReal
              (Real.exp
                (-((stateRate x' : ℝ) * t * (a : ℝ)))) *
            transitionCandidate T (flip x') y' (ρ - (a : ℝ))) =
        ENNReal.ofReal
          (∫ z : ℝ in (0 : ℝ)..ρ,
            Real.exp (-((stateRate x' : ℝ) * t * z)) *
              asymmetricTransitionProbability
                (t * (ρ - z)) (flip x') y') := by
    let f : ℝ → ℝ := fun z =>
      Real.exp (-((stateRate x' : ℝ) * t * z)) *
        asymmetricTransitionProbability (t * (ρ - z)) (flip x') y'
    have htrans : Continuous fun z : ℝ =>
        asymmetricTransitionProbability (t * (ρ - z)) (flip x') y' := by
      cases x' <;> cases y' <;>
        dsimp [asymmetricTransitionProbability, flip] <;> fun_prop
    have hf : Continuous f := by
      dsimp [f]
      apply Continuous.mul
      · fun_prop
      · exact htrans
    have hfnn : ∀ z ∈ Set.Icc (0 : ℝ) ρ, 0 ≤ f z := by
      intro z hz
      dsimp [f]
      exact mul_nonneg (Real.exp_pos _).le
        (asymmetricTransitionProbability_nonneg_of_nonneg
          (mul_nonneg ht0 (sub_nonneg.mpr hz.2)) _ _)
    calc
      (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
          ENNReal.ofReal
              (Real.exp
                (-((stateRate x' : ℝ) * t * (a : ℝ)))) *
            transitionCandidate T (flip x') y' (ρ - (a : ℝ))) =
          ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
            ENNReal.ofReal (f (a : ℝ)) := by
        apply setLIntegral_congr_fun hmeasSet
        intro a ha
        dsimp [f, transitionCandidate]
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ = ENNReal.ofReal (∫ z : ℝ in (0 : ℝ)..ρ, f z) :=
        lintegral_unitInterval_Iic_of_continuous_nonneg
          f ρ hρ0 hρ1 hf hfnn
      _ = _ := rfl
  rw [hlintegral x y]
  have hrate :
      ((stateRate x : ℝ≥0∞) * (T : ℝ≥0∞)) =
        ENNReal.ofReal ((stateRate x : ℝ) * t) := by
    rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
    rfl
  rw [hrate, ← ENNReal.ofReal_mul (by positivity)]
  have hnojump :
      0 ≤ if x = y then
        Real.exp (-((stateRate x : ℝ) * t * ρ)) else 0 := by
    split_ifs <;> positivity
  have hnojump_eq :
      (if x = y then
          ENNReal.ofReal
            (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * ρ)))
        else 0) =
        ENNReal.ofReal
          (if x = y then
            Real.exp (-((stateRate x : ℝ) * t * ρ)) else 0) := by
    by_cases hxy : x = y <;> simp [hxy, t]
  rw [hnojump_eq, ← ENNReal.ofReal_add hnojump]
  congr 1
  cases x <;> cases y <;>
    simp only [transitionCandidate, asymmetricTransitionProbability,
      stateRate, flip, if_pos, if_neg, State.zero.injEq, State.one.injEq]
  all_goals
    have hneg1 : -t ≠ 0 := neg_ne_zero.mpr ht
    have hneg2 : -(2 * t) ≠ 0 := by nlinarith
    have hpos1 : t ≠ 0 := ht
    have hpos2 : 2 * t ≠ 0 := by nlinarith
  · have hfun :
        (fun z : ℝ =>
          Real.exp (-(2 * t * z)) *
            (1 / 3 - 1 / 3 * Real.exp (-3 * (t * (ρ - z))))) =
        fun z : ℝ =>
          (1 / 3) * Real.exp ((-(2 * t)) * z) -
            (1 / 3) * Real.exp (-3 * t * ρ) * Real.exp (t * z) := by
      funext z
      rw [show -3 * (t * (ρ - z)) = -3 * t * ρ + 3 * t * z by ring,
        Real.exp_add]
      ring
    rw [hfun, intervalIntegral.integral_sub (by fun_prop) (by fun_prop),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const,
      intervalIntegral_exp_mul (-(2 * t)) ρ hneg2,
      intervalIntegral_exp_mul t ρ hpos1]
    field_simp
    ring_nf
    rw [← Real.exp_add]
    ring_nf
  · have hfun :
        (fun z : ℝ =>
          Real.exp (-(2 * t * z)) *
            (2 / 3 + 1 / 3 * Real.exp (-3 * (t * (ρ - z))))) =
        fun z : ℝ =>
          (2 / 3) * Real.exp ((-(2 * t)) * z) +
            (1 / 3) * Real.exp (-3 * t * ρ) * Real.exp (t * z) := by
      funext z
      rw [show -3 * (t * (ρ - z)) = -3 * t * ρ + 3 * t * z by ring,
        Real.exp_add]
      ring
    rw [hfun, intervalIntegral.integral_add (by fun_prop) (by fun_prop),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const,
      intervalIntegral_exp_mul (-(2 * t)) ρ hneg2,
      intervalIntegral_exp_mul t ρ hpos1]
    field_simp
    ring_nf
    rw [← Real.exp_add]
    ring_nf
  · have hfun :
        (fun z : ℝ =>
          Real.exp (-(1 * t * z)) *
            (1 / 3 + 2 / 3 * Real.exp (-3 * (t * (ρ - z))))) =
        fun z : ℝ =>
          (1 / 3) * Real.exp ((-t) * z) +
            (2 / 3) * Real.exp (-3 * t * ρ) * Real.exp ((2 * t) * z) := by
      funext z
      rw [show -3 * (t * (ρ - z)) = -3 * t * ρ + 3 * t * z by ring,
        Real.exp_add]
      ring
    rw [hfun, intervalIntegral.integral_add (by fun_prop) (by fun_prop),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const,
      intervalIntegral_exp_mul (-t) ρ hneg1,
      intervalIntegral_exp_mul (2 * t) ρ hpos2]
    field_simp
    ring_nf
    rw [← Real.exp_add]
    ring_nf
  · have hfun :
        (fun z : ℝ =>
          Real.exp (-(1 * t * z)) *
            (2 / 3 - 2 / 3 * Real.exp (-3 * (t * (ρ - z))))) =
        fun z : ℝ =>
          (2 / 3) * Real.exp ((-t) * z) -
            (2 / 3) * Real.exp (-3 * t * ρ) * Real.exp ((2 * t) * z) := by
      funext z
      rw [show -3 * (t * (ρ - z)) = -3 * t * ρ + 3 * t * z by ring,
        Real.exp_add]
      ring
    rw [hfun, intervalIntegral.integral_sub (by fun_prop) (by fun_prop),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const,
      intervalIntegral_exp_mul (-t) ρ hneg1,
      intervalIntegral_exp_mul (2 * t) ρ hpos2]
    field_simp
    ring_nf
    rw [← Real.exp_add]
    ring_nf

/-- Fubini decomposition after appending one final free holding-time
coordinate. -/
private theorem lintegral_cubeExpWeight_succ_transition
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
    · have hnotmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∉
            {z : I × (Fin n → I) |
              (z.1 : ℝ) + ∑ i, (z.2 i : ℝ) ≤ ρ} := by
        intro hmem
        apply hu
        change ∑ i, (u i : ℝ) ≤ ρ
        rw [Fin.sum_univ_castSucc]
        simpa [add_comm] using hmem
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

/-- The renewal remainder after exposing the first `N` jump sectors. -/
private noncomputable def renewalRemainder
    (T : NNReal) (x y : State) (N : ℕ) (ρ : ℝ) : ℝ≥0∞ :=
  ratePrefixProduct (chainRates x N) T *
    ∫⁻ u in freeSimplexSetAt N ρ,
      cubeExpWeight (chainRates x N) T u *
        transitionCandidate T (iterateFlip N x) y (residualAt ρ u)

private theorem renewalRemainder_zero
    (T : NNReal) (x y : State) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    renewalRemainder T x y 0 ρ = transitionCandidate T x y ρ := by
  have hset : freeSimplexSetAt 0 ρ = Set.univ := by
    ext u
    simp [freeSimplexSetAt, hρ]
  simp [renewalRemainder, ratePrefixProduct, cubeExpWeight,
    residualAt, hset]

private theorem iterateFlip_succ_eq_flip (n : ℕ) (x : State) :
    iterateFlip (n + 1) x = flip (iterateFlip n x) :=
  rfl

/-- One renewal step exposes exactly one more parity-filtered sector. -/
private theorem renewalRemainder_step
    (T : NNReal) (x y : State) (N : ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    renewalRemainder T x y N ρ =
      (if iterateFlip N x = y then sectorMassAt T x N ρ else 0) +
        renewalRemainder T x y (N + 1) ρ := by
  unfold renewalRemainder
  have hres : ∀ u ∈ freeSimplexSetAt N ρ, 0 ≤ residualAt ρ u := by
    intro u hu
    exact sub_nonneg.mpr hu
  have hres1 : ∀ u ∈ freeSimplexSetAt N ρ, residualAt ρ u ≤ 1 := by
    intro u hu
    have hsum0 : 0 ≤ ∑ i, (u i : ℝ) :=
      Finset.sum_nonneg fun i _ => (u i).2.1
    unfold residualAt
    linarith
  have hrenew : ∀ u ∈ freeSimplexSetAt N ρ,
      transitionCandidate T (iterateFlip N x) y (residualAt ρ u) =
        (if iterateFlip N x = y then
          ENNReal.ofReal
            (Real.exp
              (-((stateRate (iterateFlip N x) : ℝ) * (T : ℝ) *
                residualAt ρ u)))
        else 0) +
        ((stateRate (iterateFlip N x) : ℝ≥0∞) * (T : ℝ≥0∞)) *
          ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ u},
            ENNReal.ofReal
                (Real.exp
                  (-((stateRate (iterateFlip N x) : ℝ) * (T : ℝ) *
                    (a : ℝ)))) *
              transitionCandidate T (iterateFlip (N + 1) x) y
                (residualAt ρ u - (a : ℝ)) := by
    intro u hu
    simpa [iterateFlip_succ_eq_flip] using
      transitionCandidate_renewal T (iterateFlip N x) y
        (residualAt ρ u) (hres u hu) (hres1 u hu)
  rw [show
      (∫⁻ u in freeSimplexSetAt N ρ,
        cubeExpWeight (chainRates x N) T u *
          transitionCandidate T (iterateFlip N x) y (residualAt ρ u)) =
      ∫⁻ u in freeSimplexSetAt N ρ,
        cubeExpWeight (chainRates x N) T u *
          ((if iterateFlip N x = y then
            ENNReal.ofReal
              (Real.exp
                (-((stateRate (iterateFlip N x) : ℝ) * (T : ℝ) *
                  residualAt ρ u)))
          else 0) +
          ((stateRate (iterateFlip N x) : ℝ≥0∞) * (T : ℝ≥0∞)) *
            ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ u},
              ENNReal.ofReal
                  (Real.exp
                    (-((stateRate (iterateFlip N x) : ℝ) * (T : ℝ) *
                      (a : ℝ)))) *
                transitionCandidate T (iterateFlip (N + 1) x) y
                  (residualAt ρ u - (a : ℝ))) from by
        apply setLIntegral_congr_fun (measurableSet_freeSimplexSetAt N ρ)
        intro u hu
        exact congrArg
          (fun z => cubeExpWeight (chainRates x N) T u * z)
          (hrenew u hu)]
  simp_rw [mul_add]
  rw [lintegral_add_left (by fun_prop), mul_add]
  congr 1
  · by_cases hxy : iterateFlip N x = y
    · rw [if_pos hxy]
      rfl
    · rw [if_neg hxy]
      simp
  · have hprefix :
        ratePrefixProduct (chainRates x (N + 1)) T =
          ratePrefixProduct (chainRates x N) T *
            ((stateRate (iterateFlip N x) : ℝ≥0∞) * (T : ℝ≥0∞)) := by
      unfold ratePrefixProduct
      rw [Fin.prod_univ_castSucc, chainRates_castSucc, chainRates_last]
    rw [hprefix]
    simp only [mul_assoc]
    congr 1
    rw [lintegral_cubeExpWeight_succ_transition
      (chainRates x (N + 1)) T ρ
      (fun s => transitionCandidate T (iterateFlip (N + 1) x) y s)
      (by unfold transitionCandidate; fun_prop)]
    simp only [chainRates_castSucc, chainRates_last]

private theorem renewalRemainder_le_arrivalMass
    (T : NNReal) (x y : State) (N : ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    renewalRemainder T x y N ρ ≤ arrivalMass T x N := by
  unfold renewalRemainder arrivalMass arrivalIntegral
  apply mul_le_mul_left'
  calc
    (∫⁻ u in freeSimplexSetAt N ρ,
        cubeExpWeight (chainRates x N) T u *
          transitionCandidate T (iterateFlip N x) y (residualAt ρ u)) ≤
      ∫⁻ u in freeSimplexSetAt N ρ,
        cubeExpWeight (chainRates x N) T u := by
      apply setLIntegral_mono'
      intro u hu
      apply mul_le_of_le_one_right
      · exact bot_le
      · exact transitionCandidate_le_one T _ _
          (sub_nonneg.mpr hu)
    _ ≤ ∫⁻ u in Simplex.freeSimplexSet N,
        cubeExpWeight (chainRates x N) T u := by
      rw [← lintegral_indicator (measurableSet_freeSimplexSetAt N ρ),
        ← lintegral_indicator (Simplex.measurableSet_freeSimplexSet N)]
      apply lintegral_mono
      intro u
      by_cases hu : u ∈ freeSimplexSetAt N ρ
      · rw [Set.indicator_of_mem hu]
        have hu1 : u ∈ Simplex.freeSimplexSet N := by
          change ∑ i, (u i : ℝ) ≤ 1
          exact hu.trans hρ1
        rw [Set.indicator_of_mem hu1]
      · rw [Set.indicator_of_notMem hu]
        exact bot_le

private theorem tendsto_renewalRemainder
    (T : NNReal) (x y : State) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Filter.Tendsto (fun N => renewalRemainder T x y N ρ)
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun N => arrivalMass T x N)
    tendsto_const_nhds (tendsto_arrivalMass T x)
    (fun N => bot_le)
    (fun N => renewalRemainder_le_arrivalMass T x y N ρ hρ0 hρ1)

private theorem sum_sectorMassAt_add_remainder
    (T : NNReal) (x y : State) (N : ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑ n ∈ Finset.range N,
      if iterateFlip n x = y then sectorMassAt T x n ρ else 0) +
        renewalRemainder T x y N ρ =
      transitionCandidate T x y ρ := by
  induction N with
  | zero =>
      simp [renewalRemainder_zero T x y ρ hρ0]
  | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc,
        ← renewalRemainder_step T x y N ρ hρ0 hρ1]
      exact ih

/-- Explicit evaluation of every parity-filtered sector sum on a residual
horizon fraction. -/
private theorem tsum_sectorMassAt_parity
    (T : NNReal) (x y : State) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑' n, if iterateFlip n x = y then sectorMassAt T x n ρ else 0) =
      transitionCandidate T x y ρ := by
  have hpartial :
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          if iterateFlip n x = y then sectorMassAt T x n ρ else 0)
        Filter.atTop
        (nhds (∑' n,
          if iterateFlip n x = y then sectorMassAt T x n ρ else 0)) :=
    ENNReal.tendsto_nat_tsum _
  have hsum := hpartial.add
    (tendsto_renewalRemainder T x y ρ hρ0 hρ1)
  rw [add_zero] at hsum
  have hconst :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N,
            if iterateFlip n x = y then sectorMassAt T x n ρ else 0) +
              renewalRemainder T x y N ρ)
        Filter.atTop (nhds (transitionCandidate T x y ρ)) := by
    simp only [sum_sectorMassAt_add_remainder T x y _ ρ hρ0 hρ1]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hconst

/-- The parity-filtered analytic sector masses are exactly the explicit
asymmetric transition probabilities. -/
theorem tsum_sectorMass_parity
    (T : NNReal) (x y : State) :
    (∑' n, if iterateFlip n x = y then sectorMass T x n else 0) =
      ENNReal.ofReal (asymmetricTransitionProbability (T : ℝ) x y) := by
  simpa [sectorMassAt_one, transitionCandidate] using
    tsum_sectorMassAt_parity T x y 1 (by norm_num) (by norm_num)

/-- The actual terminal marginal of the normalized fixed-initial asymmetric
path law is the explicit transition probability. -/
theorem asymmetricPathLawFrom_terminalState_real_singleton
    (T : NNReal) (x y : State) :
    ((asymmetricPathLawFrom T x).map FullPath.terminalState).real {y} =
      asymmetricTransitionProbability (T : ℝ) x y := by
  change
    (((asymmetricPathLawFrom T x).map FullPath.terminalState {y}).toReal) =
      asymmetricTransitionProbability (T : ℝ) x y
  rw [map_asymmetricPathLawFrom_terminalState_apply,
    tsum_sectorMass_parity,
    ENNReal.toReal_ofReal (asymmetricTransitionProbability_nonneg T x y)]

/-- The actual terminal marginal is the corresponding row of the exponential
of the physical conservative generator. -/
theorem asymmetricPathLawFrom_terminalState_eq_exp_generator
    (T : NNReal) (x y : State) :
    ((asymmetricPathLawFrom T x).map FullPath.terminalState).real {y} =
      NormedSpace.exp
        ((T : ℝ) • (show Matrix State State ℝ from
          fun a b => physicalGenerator a b)) x y := by
  rw [asymmetricPathLawFrom_terminalState_real_singleton,
    exp_smul_physicalGenerator_fun_apply]

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski