/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricParityFubini

/-!
# Renewal evaluation of the asymmetric two-state parity sums

After `N` renewal steps, the first `N` parity-filtered jump sectors are explicit
and the remainder is bounded by the `N`-jump arrival mass.  The existing tail
bound sends the remainder to zero.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

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
  have hmeasNoJump :
      Measurable (fun u : Fin N → I =>
        cubeExpWeight (chainRates x N) T u *
          (if iterateFlip N x = y then
            ENNReal.ofReal
              (Real.exp
                (-((stateRate (iterateFlip N x) : ℝ) * (T : ℝ) *
                  residualAt ρ u)))
          else 0)) := by
    by_cases hxy : iterateFlip N x = y
    · simp only [if_pos hxy]
      fun_prop
    · simp only [if_neg hxy, mul_zero]
      exact measurable_const
  rw [lintegral_add_left hmeasNoJump, mul_add]
  congr 1
  · by_cases hxy : iterateFlip N x = y
    · simp [hxy, sectorMassAt]
    · simp [hxy]
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
      (measurable_transitionCandidate T _ _)]
    simp only [chainRates_castSucc, chainRates_last]
    calc
      _ = ∫⁻ u in freeSimplexSetAt N ρ,
          (stateRate (iterateFlip N x) : ℝ≥0∞) *
            ((T : ℝ≥0∞) *
              (cubeExpWeight (chainRates x N) T u *
                ∫⁻ a : I in {a : I | (a : ℝ) ≤ residualAt ρ u},
                  ENNReal.ofReal
                      (Real.exp
                        (-((stateRate (iterateFlip N x) : ℝ) *
                          (T : ℝ) * (a : ℝ)))) *
                    transitionCandidate T (iterateFlip (N + 1) x) y
                      (residualAt ρ u - (a : ℝ)))) := by
            apply setLIntegral_congr_fun (measurableSet_freeSimplexSetAt N ρ)
            intro u hu
            ac_rfl
      _ = _ := by
            rw [lintegral_const_mul' _ _ (by finiteness)]
            rw [lintegral_const_mul' _ _ (by finiteness)]

private theorem renewalRemainder_le_arrivalMass
    (T : NNReal) (x y : State) (N : ℕ) (ρ : ℝ)
    (_hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    renewalRemainder T x y N ρ ≤ arrivalMass T x N := by
  unfold renewalRemainder arrivalMass arrivalIntegral
  apply mul_le_mul_right
  calc
    (∫⁻ u in freeSimplexSetAt N ρ,
        cubeExpWeight (chainRates x N) T u *
          transitionCandidate T (iterateFlip N x) y (residualAt ρ u)) ≤
      ∫⁻ u in freeSimplexSetAt N ρ,
        cubeExpWeight (chainRates x N) T u := by
      apply setLIntegral_mono' (measurableSet_freeSimplexSetAt N ρ)
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
