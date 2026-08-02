/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetric
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricNormalization
import CrooksJarzynski.ContinuousTimeJumpSimplexReversal
import CrooksJarzynski.ContinuousTimeJumpTwoStateNormalization
import CrooksJarzynski.ContinuousTimeJumpRateFull
import Mathlib.Data.Fin.Rev

/-!
# Normalized asymmetric two-state Crooks and Jarzynski laws

This module connects the analytic sector-mass calculation for the asymmetric
two-state chain to its rate-density path measures.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

open Simplex (cubeExpWeight measurable_cubeExpWeight residualAt measurable_residualAt
  freeSimplexSetAt measurableSet_freeSimplexSetAt)

/-- An alternating state sequence is completely determined by its initial
state. -/
theorem Alternates.apply_eq_iterateFlip {n : ℕ}
    {states : Fin (n + 1) → State} (hstates : Alternates states)
    (i : Fin (n + 1)) :
    states i = iterateFlip i.1 (states 0) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      rw [hstates i, ih]
      rfl

/-- Reversal of an alternating sequence starts from its former endpoint. -/
private theorem reverse_alternatingStates (n : ℕ) (x : State) :
    (fun i => alternatingStates n x i.rev) =
      alternatingStates n (iterateFlip n x) := by
  funext i
  rw [Alternates.apply_eq_iterateFlip
    (alternates_reverse (alternatingStates_alternates n x)) i]
  congr 1

/-- The free-coordinate reversal realizes path reversal in the positive
jump-count sectors. -/
private theorem reverse_assemblePath {n : ℕ} (T : NNReal) (x : State)
    (u : Fin (n + 1) → I)
    (hu : u ∈ Simplex.freeSimplexSet (n + 1)) :
    JumpPath.reverse
        (Simplex.assemblePath T (alternatingStates (n + 1) x, u)) =
      Simplex.assemblePath T
        (alternatingStates (n + 1) (iterateFlip (n + 1) x),
          Simplex.reverseFree u) := by
  apply Prod.ext
  · exact reverse_alternatingStates (n + 1) x
  · exact (Simplex.holdingTimesOfFree_reverseFree T u hu).symm

/-- Iterated flips commute with the single-step flip. -/
private theorem iterateFlip_flip (n : ℕ) (x : State) :
    iterateFlip n (flip x) = flip (iterateFlip n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterateFlip_succ, ih, flip_flip]

/-- Iterated flipping permutes the two-state finite sum. -/
private theorem sum_iterateFlip (f : State → ℝ≥0∞) (n : ℕ) :
    ∑ x : State, f (iterateFlip n x) = ∑ x : State, f x := by
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  rw [show iterateFlip n .one = flip (iterateFlip n .zero) by
    simpa [flip] using iterateFlip_flip n .zero]
  cases iterateFlip n .zero <;> simp [flip, add_comm]

/-- Reversing an assembled positive-sector path preserves every measurable
simplex integral, after relabeling the initial state by the endpoint map. -/
private theorem lintegral_reverse_assemblePath {n : ℕ}
    (G : JumpPath State (n + 1) → ℝ≥0∞) (hG : Measurable G)
    (T : NNReal) (x : State) :
    (∫⁻ u, G (JumpPath.reverse
          (Simplex.assemblePath T (alternatingStates (n + 1) x, u)))
        ∂((T : ℝ≥0∞) ^ (n + 1) •
          (volume : Measure (Fin (n + 1) → I)).restrict
            (Simplex.freeSimplexSet (n + 1)))) =
      ∫⁻ u, G
          (Simplex.assemblePath T
            (alternatingStates (n + 1) (iterateFlip (n + 1) x), u))
        ∂((T : ℝ≥0∞) ^ (n + 1) •
          (volume : Measure (Fin (n + 1) → I)).restrict
            (Simplex.freeSimplexSet (n + 1))) := by
  rw [lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  calc
    (∫⁻ u in Simplex.freeSimplexSet (n + 1),
        G (JumpPath.reverse
          (Simplex.assemblePath T
            (alternatingStates (n + 1) x, u)))) =
        ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          G (Simplex.assemblePath T
            (alternatingStates (n + 1) (iterateFlip (n + 1) x),
              Simplex.reverseFree u)) := by
      apply setLIntegral_congr_fun
        (Simplex.measurableSet_freeSimplexSet (n + 1))
      intro u hu
      dsimp only
      rw [reverse_assemblePath T x u hu]
    _ = ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          G (Simplex.assemblePath T
            (alternatingStates (n + 1) (iterateFlip (n + 1) x), u)) := by
      exact Simplex.lintegral_freeSimplex_reverseFree
        (fun u => G (Simplex.assemblePath T
          (alternatingStates (n + 1) (iterateFlip (n + 1) x), u)))
        (hG.comp
          ((Simplex.measurable_assemblePath T).comp
            (Measurable.prodMk measurable_const measurable_id)))

/-- Reversal is the identity on the zero-jump simplex chart. -/
private theorem reverse_assemblePath_zero (T : NNReal) (x : State)
    (u : Fin 0 → I) :
    JumpPath.reverse
        (Simplex.assemblePath T (alternatingStates 0 x, u)) =
      Simplex.assemblePath T (alternatingStates 0 x, u) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- The path-model escape rate agrees with the scalar rate used in the
normalization calculation. -/
theorem escapeRate_eq_stateRate {n : ℕ} (i : Fin (n + 1)) (x : State) :
    escapeRate i x = stateRate x := by
  cases x <;> rfl

/-- Along the unique allowed transition, the jump rate is the current state's
escape rate. -/
theorem jumpRate_flip {n : ℕ} (i : Fin n) (x : State) :
    jumpRate i x (flip x) = stateRate x := by
  cases x <;> rfl

/-- On an alternating path, the abstract rate density reduces to the product
of the scalar rates and exponential holding weights used by `sectorMass`. -/
theorem rateDensity_eq_of_alternates {n : ℕ} (w : State → ℝ≥0∞)
    (γ : JumpPath State n) (hstates : Alternates γ.1) :
    JumpPath.rateDensity w escapeRate jumpRate γ =
      w (γ.1 0) *
        (∏ i : Fin n,
          ENNReal.ofReal
              (Real.exp
                (-((stateRate (γ.1 i.castSucc) : ℝ) *
                  (γ.2 i.castSucc : ℝ)))) *
            (stateRate (γ.1 i.castSucc) : ℝ≥0∞)) *
        ENNReal.ofReal
          (Real.exp
            (-((stateRate (γ.1 (Fin.last n)) : ℝ) *
              (γ.2 (Fin.last n) : ℝ)))) := by
  unfold JumpPath.rateDensity JumpPath.density
    JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
  simp_rw [escapeRate_eq_stateRate]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hstates i, jumpRate_flip]

/-- Common product form of the unit-endpoint forward and reverse densities. -/
private noncomputable def commonDensity {n : ℕ} (γ : JumpPath State n) :
    ℝ≥0∞ :=
  (∏ i : Fin n, (stateRate (γ.1 i.castSucc) : ℝ≥0∞)) *
    ∏ j : Fin (n + 1),
      ENNReal.ofReal
        (Real.exp (-((stateRate (γ.1 j) : ℝ) * (γ.2 j : ℝ))))

private theorem finalRateDensity_eq_commonDensity {n : ℕ}
    (γ : JumpPath State n) (hγ : Alternates γ.1) :
    JumpPath.rateDensity gibbsFinalWeight escapeRate jumpRate γ =
      commonDensity γ := by
  rw [rateDensity_eq_of_alternates gibbsFinalWeight γ hγ]
  unfold gibbsFinalWeight commonDensity
  simp only [one_mul]
  rw [Finset.prod_mul_distrib]
  calc
    _ = (∏ i : Fin n, (stateRate (γ.1 i.castSucc) : ℝ≥0∞)) *
        ((∏ i : Fin n,
          ENNReal.ofReal
            (Real.exp (-((stateRate (γ.1 i.castSucc) : ℝ) *
              (γ.2 i.castSucc : ℝ))))) *
          ENNReal.ofReal
            (Real.exp (-((stateRate (γ.1 (Fin.last n)) : ℝ) *
              (γ.2 (Fin.last n) : ℝ))))) := by ring
    _ = commonDensity γ := by
      unfold commonDensity
      congr 1
      exact (Fin.prod_univ_castSucc fun j : Fin (n + 1) =>
        ENNReal.ofReal
          (Real.exp (-((stateRate (γ.1 j) : ℝ) *
            (γ.2 j : ℝ))))).symm

private theorem reverseRateDensity_eq_commonDensity {n : ℕ}
    (γ : JumpPath State n) (hγ : Alternates γ.1) :
    JumpPath.reverseRateDensity gibbsFinalWeight escapeRate jumpRate γ =
      commonDensity γ := by
  unfold JumpPath.reverseRateDensity JumpPath.alignedReverseRateDensity
    JumpPath.alignedReverseDensity JumpPath.holdingWeightOfEscapeRate
    JumpPath.jumpWeightOfRate JumpPath.reverse gibbsFinalWeight
  simp only [Function.comp_apply, one_mul, Fin.rev_last, Fin.rev_castSucc,
    Fin.rev_succ]
  simp_rw [escapeRate_eq_stateRate]
  have hjump (i : Fin n) :
      (jumpRate i (γ.1 i.rev.castSucc) (γ.1 i.rev.succ) : ℝ≥0∞) =
        stateRate (γ.1 i.rev.castSucc) := by
    rw [hγ i.rev, jumpRate_flip]
  simp_rw [hjump]
  rw [Finset.prod_mul_distrib]
  have hholding :
      (∏ i : Fin n,
        ENNReal.ofReal
          (Real.exp
            (-((stateRate (γ.1 i.rev.succ) : ℝ) *
              (γ.2 i.rev.succ : ℝ))))) =
        ∏ i : Fin n,
          ENNReal.ofReal
            (Real.exp
              (-((stateRate (γ.1 i.succ) : ℝ) *
                (γ.2 i.succ : ℝ)))) := by
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)
  have hrates :
      (∏ i : Fin n,
        (stateRate (γ.1 i.rev.castSucc) : ℝ≥0∞)) =
        ∏ i : Fin n,
          (stateRate (γ.1 i.castSucc) : ℝ≥0∞) := by
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [hholding, hrates]
  unfold commonDensity
  rw [Fin.prod_univ_succ]
  ring

/-- Evaluation in the free simplex chart used to construct the raw sector
reference. -/
theorem rateDensity_assemblePath {n : ℕ} (w : State → ℝ≥0∞)
    (T : NNReal) (x : State) (u : Fin n → I)
    (hu : u ∈ Simplex.freeSimplexSet n) :
    JumpPath.rateDensity w escapeRate jumpRate
        (Simplex.assemblePath T (alternatingStates n x, u)) =
      w x * cubeExpWeight (chainRates x n) T u *
        (∏ i, (chainRates x n i : ℝ≥0∞)) *
          ENNReal.ofReal
            (Real.exp
              (-((stateRate (iterateFlip n x) : ℝ) *
                (T : ℝ) * Simplex.residual u))) := by
  rw [rateDensity_eq_of_alternates w _
    (alternatingStates_alternates n x)]
  have hsum : (∑ i, Simplex.unitNNReal (u i)) ≤ (1 : NNReal) := by
    change (∑ i, (Simplex.unitNNReal (u i) : ℝ)) ≤ 1 at hu
    exact_mod_cast hu
  have hscaled :
      (∑ i, T * Simplex.unitNNReal (u i)) ≤ T := by
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_right hsum T
  have hlast :
      ((T - ∑ i, T * Simplex.unitNNReal (u i) : NNReal) : ℝ) =
        (T : ℝ) * Simplex.residual u := by
    rw [NNReal.coe_sub hscaled]
    rw [NNReal.coe_sum]
    simp only [Simplex.residual, NNReal.coe_mul, Simplex.coe_unitNNReal]
    rw [← Finset.mul_sum]
    ring
  simp only [Simplex.assemblePath, alternatingStates,
    Simplex.holdingTimesOfFree, Fin.snoc_castSucc, Fin.snoc_last,
    chainRates, cubeExpWeight,
    Simplex.coe_unitNNReal, NNReal.coe_mul, hlast]
  rw [Finset.prod_mul_distrib]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, iterateFlip_zero,
    mul_comm]
  ac_rfl

/-- Scaling the conditioned simplex probability by its geometric sector mass
cancels the conditioning normalization. -/
theorem simplexMass_smul_freeSimplexProbability (T : NNReal) (n : ℕ) :
    TwoState.simplexMass T n • Simplex.freeSimplexProbability n =
      (T : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → I)).restrict
          (Simplex.freeSimplexSet n) := by
  unfold TwoState.simplexMass Simplex.freeSimplexProbability
    ProbabilityTheory.cond
  rw [smul_smul]
  congr 1
  have hpos := Simplex.volume_freeSimplexSet_pos n
  have hfinite :
      (volume : Measure (Fin n → I)) (Simplex.freeSimplexSet n) ≠ ∞ := by
    rw [Simplex.volume_freeSimplexSet]
    exact ENNReal.ofReal_ne_top
  rw [mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt hpos) hfinite, mul_one]

/-- The scalar prefactor in `sectorIntegral` is the geometric scale times the
product of the physical jump rates. -/
theorem ratePrefixProduct_chainRates (T : NNReal) (x : State) (n : ℕ) :
    ratePrefixProduct (chainRates x n) T =
      (T : ℝ≥0∞) ^ n * ∏ i, (chainRates x n i : ℝ≥0∞) := by
  unfold ratePrefixProduct
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- The rate density in one raw simplex chart integrates to the analytic
sector mass for its initial state. -/
theorem lintegral_rateDensity_assemblePath (w : State → ℝ≥0∞)
    (T : NNReal) (x : State) (n : ℕ) :
    ∫⁻ u, JumpPath.rateDensity w escapeRate jumpRate
          (Simplex.assemblePath T (alternatingStates n x, u))
        ∂((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n)) =
      w x * sectorMass T x n := by
  rw [lintegral_smul_measure, smul_eq_mul]
  rw [setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
    (fun u hu => rateDensity_assemblePath w T x u hu)]
  have hintegrand :
      Measurable (fun u : Fin n → I =>
        cubeExpWeight (chainRates x n) T u *
          ENNReal.ofReal
            (Real.exp
              (-((stateRate (iterateFlip n x) : ℝ) *
                (T : ℝ) * Simplex.residual u)))) := by
    fun_prop
  have hreorder : Set.EqOn
      (fun u =>
        (w x * cubeExpWeight (chainRates x n) T u *
            ∏ i, (chainRates x n i : ℝ≥0∞)) *
          ENNReal.ofReal
            (Real.exp
              (-((stateRate (iterateFlip n x) : ℝ) *
                (T : ℝ) * Simplex.residual u))))
      (fun u =>
        (w x * ∏ i, (chainRates x n i : ℝ≥0∞)) *
          (cubeExpWeight (chainRates x n) T u *
            ENNReal.ofReal
              (Real.exp
                (-((stateRate (iterateFlip n x) : ℝ) *
                  (T : ℝ) * Simplex.residual u)))))
      (Simplex.freeSimplexSet n) := by
    intro u _
    ring
  rw [setLIntegral_congr_fun
    (Simplex.measurableSet_freeSimplexSet n) hreorder]
  rw [lintegral_const_mul _ hintegrand]
  unfold sectorMass sectorIntegral
  rw [ratePrefixProduct_chainRates]
  ring

/-- The unsymmetrized geometric reference underlying `sectorReference`. -/
noncomputable def rawSectorReference (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  TwoState.simplexMass T n •
    Simplex.rawPathProbability T (alternatingStateLaw n)

theorem rawSectorReference_eq (T : NNReal) (n : ℕ) :
    rawSectorReference T n =
      ((alternatingStateLaw n).prod
        ((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))).map
        (Simplex.assemblePath T) := by
  unfold rawSectorReference Simplex.rawPathProbability
  rw [← Measure.map_smul, ← Measure.prod_smul_right,
    simplexMass_smul_freeSimplexProbability]

theorem initialStateLaw_singleton (x : State) :
  initialStateLaw {x} = 2⁻¹ := by
  rw [initialStateLaw, ProbabilityTheory.uniformOn_univ]
  rw [show Fintype.card State = 2 by decide]
  norm_num

/-- The unsymmetrized two-state simplex reference is already reversal
invariant at the level of all measurable integrals. -/
theorem lintegral_rawSectorReference_reverse
    (n : ℕ) (G : JumpPath State n → ℝ≥0∞) (hG : Measurable G)
    (T : NNReal) :
    (∫⁻ γ, G (JumpPath.reverse γ) ∂rawSectorReference T n) =
      ∫⁻ γ, G γ ∂rawSectorReference T n := by
  rw [rawSectorReference_eq]
  have hassemble := Simplex.measurable_assemblePath
    (Ω := State) (n := n) T
  have hleft :
      Measurable (fun p :
          (Fin (n + 1) → State) × (Fin n → I) =>
        G (JumpPath.reverse (Simplex.assemblePath T p))) :=
    (hG.comp JumpPath.measurable_reverse).comp hassemble
  have hright :
      Measurable (fun p :
          (Fin (n + 1) → State) × (Fin n → I) =>
        G (Simplex.assemblePath T p)) :=
    hG.comp hassemble
  change (∫⁻ γ, (G ∘ JumpPath.reverse) γ
      ∂Measure.map (Simplex.assemblePath T)
        ((alternatingStateLaw n).prod
          ((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n)))) =
    ∫⁻ γ, G γ
      ∂Measure.map (Simplex.assemblePath T)
        ((alternatingStateLaw n).prod
          ((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n)))
  rw [lintegral_map' (hG.comp JumpPath.measurable_reverse).aemeasurable
      hassemble.aemeasurable,
    lintegral_map' hG.aemeasurable hassemble.aemeasurable]
  change (∫⁻ p, G (JumpPath.reverse (Simplex.assemblePath T p))
      ∂(alternatingStateLaw n).prod
        ((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))) =
    ∫⁻ p, G (Simplex.assemblePath T p)
      ∂(alternatingStateLaw n).prod
        ((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))
  rw [lintegral_prod _ hleft.aemeasurable,
    lintegral_prod _ hright.aemeasurable]
  have hinnerLeft :
      Measurable (fun states : Fin (n + 1) → State =>
        ∫⁻ u, G (JumpPath.reverse
          (Simplex.assemblePath T (states, u)))
          ∂((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n))) :=
    hleft.lintegral_prod_right'
  have hinnerRight :
      Measurable (fun states : Fin (n + 1) → State =>
        ∫⁻ u, G (Simplex.assemblePath T (states, u))
          ∂((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n))) :=
    hright.lintegral_prod_right'
  unfold alternatingStateLaw
  rw [lintegral_map' hinnerLeft.aemeasurable
      Measurable.of_discrete.aemeasurable,
    lintegral_map' hinnerRight.aemeasurable
      Measurable.of_discrete.aemeasurable]
  rw [lintegral_fintype, lintegral_fintype]
  simp_rw [initialStateLaw_singleton]
  cases n with
  | zero =>
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      apply lintegral_congr
      intro u
      rw [reverse_assemblePath_zero T x u]
  | succ n =>
      simp_rw [lintegral_reverse_assemblePath G hG T]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 1
      exact sum_iterateFlip
        (fun x => ∫⁻ u, G
          (Simplex.assemblePath T (alternatingStates (n + 1) x, u))
          ∂((T : ℝ≥0∞) ^ (n + 1) •
            (volume : Measure (Fin (n + 1) → I)).restrict
              (Simplex.freeSimplexSet (n + 1)))) (n + 1)

/-- The raw two-state simplex reference itself is reversal invariant. -/
theorem map_rawSectorReference_reverse (T : NNReal) (n : ℕ) :
    (rawSectorReference T n).map JumpPath.reverse =
      rawSectorReference T n := by
  ext s hs
  rw [Measure.map_apply JumpPath.measurable_reverse hs]
  have h := lintegral_rawSectorReference_reverse n
    (s.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hs) T
  have hcomp :
      (fun γ => s.indicator (fun _ => (1 : ℝ≥0∞))
        (JumpPath.reverse γ)) =
        (JumpPath.reverse ⁻¹' s).indicator
          (fun _ => (1 : ℝ≥0∞)) := by
    funext γ
    by_cases hγ : JumpPath.reverse γ ∈ s
    · rw [Set.indicator_of_mem hγ]
      rw [Set.indicator_of_mem
        (show γ ∈ JumpPath.reverse ⁻¹' s from hγ)]
    · rw [Set.indicator_of_notMem hγ]
      rw [Set.indicator_of_notMem
        (show γ ∉ JumpPath.reverse ⁻¹' s from hγ)]
  rw [hcomp, lintegral_indicator
      (hs.preimage JumpPath.measurable_reverse),
    lintegral_indicator hs, setLIntegral_one, setLIntegral_one] at h
  exact h

/-- Since the raw chart is reversal invariant, the canonical symmetrized
reference coincides with it. -/
theorem sectorReference_eq_rawSectorReference (T : NNReal) (n : ℕ) :
    TwoState.sectorReference T n = rawSectorReference T n := by
  unfold TwoState.sectorReference Simplex.reference
    Simplex.pathProbability Simplex.symmetrizePathMeasure
  calc
    TwoState.simplexMass T n •
        ((2 : ℝ≥0∞)⁻¹ •
          (Simplex.rawPathProbability T (alternatingStateLaw n) +
            (Simplex.rawPathProbability T
              (alternatingStateLaw n)).map JumpPath.reverse)) =
        (2 : ℝ≥0∞)⁻¹ •
          (rawSectorReference T n +
            (rawSectorReference T n).map JumpPath.reverse) := by
      unfold rawSectorReference
      rw [Measure.map_smul]
      module
    _ = rawSectorReference T n := by
      rw [map_rawSectorReference_reverse]
      ext s hs
      simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]
      rw [← two_mul]
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel
          (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
          (show (2 : ℝ≥0∞) ≠ ∞ by norm_num),
        one_mul]

/-- The raw chart integral is the uniform average of the two analytic sector
masses, with the requested initial density. -/
theorem lintegral_rateDensity_rawSectorReference
    (w : State → ℝ≥0∞) (T : NNReal) (n : ℕ) :
    ∫⁻ γ, JumpPath.rateDensity w escapeRate jumpRate γ
        ∂rawSectorReference T n =
      2⁻¹ * ∑ x : State, w x * sectorMass T x n := by
  rw [rawSectorReference_eq]
  have hdensity :
      Measurable
        (JumpPath.rateDensity w
          (escapeRate (n := n)) (jumpRate (n := n))) := by
    unfold JumpPath.rateDensity JumpPath.density
      JumpPath.holdingWeightOfEscapeRate
      JumpPath.jumpWeightOfRate escapeRate jumpRate
    fun_prop
  have hassemble := Simplex.measurable_assemblePath
    (Ω := State) (n := n) T
  rw [lintegral_map' hdensity.aemeasurable hassemble.aemeasurable]
  have hjoint :
      Measurable (fun p :
          (Fin (n + 1) → State) × (Fin n → I) =>
        JumpPath.rateDensity w escapeRate jumpRate
          (Simplex.assemblePath T p)) :=
    hdensity.comp hassemble
  rw [lintegral_prod _ hjoint.aemeasurable]
  have hinner :
      Measurable (fun states : Fin (n + 1) → State =>
        ∫⁻ u, JumpPath.rateDensity w escapeRate jumpRate
          (Simplex.assemblePath T (states, u))
          ∂((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n))) :=
    hjoint.lintegral_prod_right'
  unfold alternatingStateLaw
  rw [lintegral_map' hinner.aemeasurable
    Measurable.of_discrete.aemeasurable]
  simp_rw [lintegral_rateDensity_assemblePath]
  rw [lintegral_fintype]
  simp_rw [initialStateLaw_singleton]
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  rw [Finset.sum_pair (by decide)]
  ring

/-! ### Normalized forward path law -/

/-- The actual asymmetric forward law in one fixed jump-count sector. -/
noncomputable def forwardSectorLaw (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  FullPath.forwardRateSectorMeasure
    (TwoState.sectorReference T) gibbsInitialWeight
    (fun n => escapeRate (n := n)) (fun n => jumpRate (n := n)) n

/-- The mass of a forward sector is the Gibbs-weighted average of its two
initial-state sector masses. -/
theorem forwardSectorLaw_univ (T : NNReal) (n : ℕ) :
    forwardSectorLaw T n Set.univ =
      2⁻¹ * ∑ x : State, gibbsInitialWeight x * sectorMass T x n := by
  unfold forwardSectorLaw FullPath.forwardRateSectorMeasure pathMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    sectorReference_eq_rawSectorReference]
  exact lintegral_rateDensity_rawSectorReference
    gibbsInitialWeight T n

/-- The forward sector masses sum to one. -/
theorem tsum_forwardSectorLaw_univ (T : NNReal) :
    ∑' n, forwardSectorLaw T n Set.univ = 1 := by
  simp_rw [forwardSectorLaw_univ]
  have hsum (n : ℕ) :
      (∑ x : State, gibbsInitialWeight x * sectorMass T x n) =
        gibbsInitialWeight .zero * sectorMass T .zero n +
          gibbsInitialWeight .one * sectorMass T .one n := by
    rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
      Finset.sum_pair (by decide)]
  simp_rw [hsum]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add,
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    tsum_sectorMass T .zero, tsum_sectorMass T .one]
  simp only [gibbsInitialWeight]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  simp only [mul_one]
  calc
    (2 : ℝ≥0∞)⁻¹ * (3⁻¹ * 2 + 3⁻¹ * 4) =
        (2⁻¹ * 2) * (3⁻¹ * 3) := by ring
    _ = 1 := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      norm_num

/-- The normalized full asymmetric forward path law. -/
noncomputable def forwardPathLaw (T : NNReal) : Measure (FullPath State) :=
  FullPath.measure (forwardSectorLaw T)

noncomputable instance instIsProbabilityMeasureForwardPathLaw (T : NNReal) :
    IsProbabilityMeasure (forwardPathLaw T) := by
  unfold forwardPathLaw
  exact FullPath.isProbabilityMeasure_measure
    (forwardSectorLaw T) (tsum_forwardSectorLaw_univ T)

/-! ### Normalized reverse path law -/

/-- On the alternating reference support, the chronological reverse density
equals the ordinary unit-endpoint density. -/
theorem pathMeasure_reverseRateDensity_eq_finalRateDensity
    (T : NNReal) (n : ℕ) :
    pathMeasure (TwoState.sectorReference T n)
        (JumpPath.reverseRateDensity gibbsFinalWeight escapeRate jumpRate) =
      pathMeasure (TwoState.sectorReference T n)
        (JumpPath.rateDensity gibbsFinalWeight escapeRate jumpRate) := by
  unfold pathMeasure
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards [TwoState.sectorReference_ae_alternates T n] with γ hγ
  rw [reverseRateDensity_eq_commonDensity γ hγ,
    finalRateDensity_eq_commonDensity γ hγ]

/-- The time-reversed reverse-experiment law in one jump-count sector. -/
noncomputable def reverseSectorLaw (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  FullPath.reversedRateSectorMeasure
    (TwoState.sectorReference T) gibbsFinalWeight
    (fun n => escapeRate (n := n)) (fun n => jumpRate (n := n)) n

/-- The reverse sector mass is the uniform average of the two initial-state
sector masses. -/
theorem reverseSectorLaw_univ (T : NNReal) (n : ℕ) :
    reverseSectorLaw T n Set.univ =
      2⁻¹ * ∑ x : State, sectorMass T x n := by
  unfold reverseSectorLaw FullPath.reversedRateSectorMeasure
    JumpPath.timeReversedMeasure
  rw [Measure.map_apply JumpPath.measurable_reverse MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [pathMeasure_reverseRateDensity_eq_finalRateDensity]
  unfold pathMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    sectorReference_eq_rawSectorReference,
    lintegral_rateDensity_rawSectorReference]
  simp only [gibbsFinalWeight, one_mul]

/-- The reverse sector masses sum to one. -/
theorem tsum_reverseSectorLaw_univ (T : NNReal) :
    ∑' n, reverseSectorLaw T n Set.univ = 1 := by
  simp_rw [reverseSectorLaw_univ]
  have hsum (n : ℕ) :
      (∑ x : State, sectorMass T x n) =
        sectorMass T .zero n + sectorMass T .one n := by
    rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
      Finset.sum_pair (by decide)]
  simp_rw [hsum]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add,
    tsum_sectorMass T .zero, tsum_sectorMass T .one]
  rw [← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel
      (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
      (show (2 : ℝ≥0∞) ≠ ∞ by norm_num),
    one_mul]

/-- The normalized full asymmetric reverse path law. -/
noncomputable def reversePathLaw (T : NNReal) : Measure (FullPath State) :=
  FullPath.measure (reverseSectorLaw T)

noncomputable instance instIsProbabilityMeasureReversePathLaw (T : NNReal) :
    IsProbabilityMeasure (reversePathLaw T) := by
  unfold reversePathLaw
  exact FullPath.isProbabilityMeasure_measure
    (reverseSectorLaw T) (tsum_reverseSectorLaw_univ T)

/-! ### Full Crooks and Jarzynski equalities -/

/-- The nonconstant work observable on the full finite-jump path space. -/
noncomputable def fullWorkWeight : FullPath State → ℝ≥0∞ :=
  FullPath.weight
    (FullPath.rateWorkWeightFamily boundaryWork
      (fun n => jumpWork (n := n)))

theorem measurable_fullWorkWeight : Measurable fullWorkWeight := by
  unfold fullWorkWeight
  exact FullPath.measurable_weight _
    (fun n => measurable_rateWorkWeight n)

/-- Crooks' relation for the normalized asymmetric continuous-time chain. -/
theorem full_crooks (T : NNReal) :
    CrooksRelation (forwardPathLaw T) (reversePathLaw T)
      fullWorkWeight freeEnergyWeight := by
  unfold forwardPathLaw reversePathLaw forwardSectorLaw reverseSectorLaw
    fullWorkWeight
  apply FullPath.crooks_of_rate_local_balance
    (TwoState.sectorReference T) gibbsInitialWeight gibbsFinalWeight
    (fun n => escapeRate (n := n)) (fun n => escapeRate (n := n))
    (fun n => jumpRate (n := n)) (fun n => jumpRate (n := n))
    boundaryWork (fun n => jumpWork (n := n)) freeEnergyWeight
  · exact TwoState.map_sectorReference_reverse T
  · exact measurable_rateDensity
  · exact measurable_alignedReverseRateDensity
  · exact measurable_rateWorkWeight
  · exact endpoint_balance
  · intro n i x
    rfl
  · intro n i x y
    exact jump_balance i x y

/-- Jarzynski's equality for the normalized asymmetric chain. -/
theorem full_jarzynski_lintegral (T : NNReal) :
    ∫⁻ γ, fullWorkWeight γ ∂forwardPathLaw T =
      freeEnergyWeight := by
  exact jarzynski_lintegral _ _ _ _ (full_crooks T)

/-- Real-valued Jarzynski equality for the normalized asymmetric chain. -/
theorem full_jarzynski_toReal (T : NNReal) :
    ∫ γ, (fullWorkWeight γ).toReal ∂forwardPathLaw T =
      freeEnergyWeight.toReal := by
  exact jarzynski_toReal_integral _ _ _ _
    measurable_fullWorkWeight (by norm_num [freeEnergyWeight])
    (full_crooks T)


/-! ### The work observable is nondegenerate under the normalized law -/

/-- The Gibbs initial weight concentrated on a single state. -/
private noncomputable def initialIndicatorWeight (x : State) :
    State → ℝ≥0∞ :=
  fun s => if s = x then gibbsInitialWeight s else 0

/-- Cutting the forward density down to a fixed initial state replaces the
initial weight by its single-state restriction. -/
private theorem indicator_rateDensity {n : ℕ} (x : State)
    (γ : JumpPath State n) :
    ({γ : JumpPath State n | γ.1 0 = x}).indicator
        (JumpPath.rateDensity gibbsInitialWeight escapeRate jumpRate) γ =
      JumpPath.rateDensity (initialIndicatorWeight x) escapeRate jumpRate
        γ := by
  unfold JumpPath.rateDensity JumpPath.density initialIndicatorWeight
  by_cases h : γ.1 0 = x
  · rw [Set.indicator_of_mem (show γ ∈ _ from h)]
    simp [h]
  · rw [Set.indicator_of_notMem (show γ ∉ _ from h)]
    simp [h]

/-- The mass a forward sector assigns to paths with a fixed initial state. -/
theorem forwardSectorLaw_initialState (T : NNReal) (n : ℕ) (x : State) :
    forwardSectorLaw T n {γ : JumpPath State n | γ.1 0 = x} =
      2⁻¹ * (gibbsInitialWeight x * sectorMass T x n) := by
  have hmeas : Measurable (fun γ : JumpPath State n => γ.1 0) :=
    (measurable_pi_apply 0).comp measurable_fst
  have hset : MeasurableSet {γ : JumpPath State n | γ.1 0 = x} :=
    hmeas (measurableSet_singleton x)
  unfold forwardSectorLaw FullPath.forwardRateSectorMeasure pathMeasure
  rw [withDensity_apply _ hset, ← lintegral_indicator hset,
    lintegral_congr (indicator_rateDensity x),
    sectorReference_eq_rawSectorReference,
    lintegral_rateDensity_rawSectorReference (initialIndicatorWeight x) T n]
  congr 1
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases x <;> simp [initialIndicatorWeight]

/-- With no jump to place, the sector mass is a strictly positive survival
probability. -/
theorem sectorMass_zero_pos (T : NNReal) (x : State) :
    0 < sectorMass T x 0 := by
  unfold sectorMass sectorIntegral ratePrefixProduct cubeExpWeight
  have hset : Simplex.freeSimplexSet 0 = Set.univ := by
    ext u
    simp [Simplex.freeSimplexSet]
  have hres : ∀ u : Fin 0 → I, Simplex.residual u = 1 := by
    intro u
    unfold Simplex.residual
    simp
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, hset,
    Measure.restrict_univ]
  simp_rw [hres]
  rw [lintegral_const]
  have h1 : (volume : Measure (Fin 0 → I)) Set.univ = 1 := by
    simp
  rw [h1, mul_one]
  exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

/-- The Gibbs initial weight is strictly positive. -/
theorem gibbsInitialWeight_pos (x : State) :
    0 < gibbsInitialWeight x := by
  cases x <;>
    exact ENNReal.div_pos (by norm_num) (by norm_num)

/-- Both initial states carry positive forward mass in the no-jump sector. -/
theorem forwardSectorLaw_initialState_pos (T : NNReal) (x : State) :
    0 < forwardSectorLaw T 0 {γ : JumpPath State 0 | γ.1 0 = x} := by
  rw [forwardSectorLaw_initialState]
  exact ENNReal.mul_pos (by norm_num)
    (ENNReal.mul_pos (gibbsInitialWeight_pos x).ne'
      (sectorMass_zero_pos T x).ne').ne'

/-- On a path with no jumps, the work weight is the boundary factor of
the single occupied state. -/
theorem rateWorkWeight_zeroJump (γ : JumpPath State 0) :
    JumpPath.rateWorkWeight boundaryWork jumpWork γ =
      boundaryWork (γ.1 0) (γ.1 0) := by
  unfold JumpPath.rateWorkWeight JumpPath.factorizedWorkWeight
  have hlast : (Fin.last 0) = (0 : Fin 1) := rfl
  simp [hlast]

private theorem forwardPathLaw_workWeight_value_pos
    (T : NNReal) (x : State) (v : ℝ≥0∞)
    (hval : boundaryWork x x = v) :
    0 < forwardPathLaw T {γ : FullPath State | fullWorkWeight γ = v} := by
  have hA : MeasurableSet {γ : FullPath State | fullWorkWeight γ = v} :=
    measurable_fullWorkWeight (measurableSet_singleton v)
  have hincl : {γ : JumpPath State 0 | γ.1 0 = x} ⊆
      Sigma.mk 0 ⁻¹' {γ : FullPath State | fullWorkWeight γ = v} := by
    intro γ hγ
    have hstate : γ.1 0 = x := hγ
    show fullWorkWeight ⟨0, γ⟩ = v
    calc fullWorkWeight ⟨0, γ⟩ =
        JumpPath.rateWorkWeight boundaryWork jumpWork γ := rfl
      _ = boundaryWork (γ.1 0) (γ.1 0) := rateWorkWeight_zeroJump γ
      _ = v := by rw [hstate, hval]
  calc (0 : ℝ≥0∞) <
      forwardSectorLaw T 0 {γ : JumpPath State 0 | γ.1 0 = x} :=
        forwardSectorLaw_initialState_pos T x
    _ ≤ forwardSectorLaw T 0
          (Sigma.mk 0 ⁻¹' {γ : FullPath State | fullWorkWeight γ = v}) :=
        measure_mono hincl
    _ = FullPath.liftMeasure 0 (forwardSectorLaw T 0)
          {γ : FullPath State | fullWorkWeight γ = v} :=
        (Measure.map_apply (FullPath.measurable_mk 0) hA).symm
    _ ≤ ∑' n, FullPath.liftMeasure n (forwardSectorLaw T n)
          {γ : FullPath State | fullWorkWeight γ = v} :=
        ENNReal.le_tsum 0
    _ = forwardPathLaw T {γ : FullPath State | fullWorkWeight γ = v} := by
        unfold forwardPathLaw FullPath.measure
        rw [Measure.sum_apply _ hA]

/-- The work value `3` has positive probability under the forward law. -/
theorem forwardPathLaw_workWeight_three_pos (T : NNReal) :
    0 < forwardPathLaw T {γ : FullPath State | fullWorkWeight γ = 3} :=
  forwardPathLaw_workWeight_value_pos T .zero 3 rfl

/-- The work value `3 / 2` has positive probability under the forward law. -/
theorem forwardPathLaw_workWeight_three_halves_pos (T : NNReal) :
    0 < forwardPathLaw T
      {γ : FullPath State | fullWorkWeight γ = 3 / 2} :=
  forwardPathLaw_workWeight_value_pos T .one (3 / 2) rfl

/-- The work observable is not almost-everywhere constant under the
normalized forward path law: the asymmetric example is genuinely
nondegenerate on the support of its own path measure. -/
theorem fullWorkWeight_not_ae_const (T : NNReal) :
    ¬ ∃ c : ℝ≥0∞,
      fullWorkWeight =ᵐ[forwardPathLaw T] fun _ => c := by
  rintro ⟨c, hc⟩
  have h0 : forwardPathLaw T {γ | ¬ fullWorkWeight γ = c} = 0 :=
    ae_iff.mp hc
  have hval : ∀ v : ℝ≥0∞,
      0 < forwardPathLaw T {γ : FullPath State | fullWorkWeight γ = v} →
        c = v := by
    intro v hv
    by_contra hne
    have hsub : {γ : FullPath State | fullWorkWeight γ = v} ⊆
        {γ : FullPath State | ¬ fullWorkWeight γ = c} := by
      intro γ hγ h'
      exact hne (h'.symm.trans hγ)
    exact lt_irrefl (0 : ℝ≥0∞)
      (hv.trans_le ((measure_mono hsub).trans h0.le))
  have h3 := hval 3 (forwardPathLaw_workWeight_three_pos T)
  have h32 := hval (3 / 2) (forwardPathLaw_workWeight_three_halves_pos T)
  have hcontra : (3 : ℝ≥0∞) = 3 / 2 := h3.symm.trans h32
  have := congrArg ENNReal.toReal hcontra
  rw [ENNReal.toReal_div] at this
  norm_num at this

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
