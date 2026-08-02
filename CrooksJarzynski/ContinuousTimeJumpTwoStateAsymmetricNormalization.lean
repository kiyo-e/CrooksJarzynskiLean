/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoState
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Normalization of the asymmetric two-state jump law

The asymmetric chain has state-dependent escape rates, so its sector masses are
not the Poisson masses of the symmetric chain.  This module proves that they
still sum to one, by a telescoping argument that stays entirely inside
finite-dimensional simplex integrals.

For a fixed initial state, `arrivalIntegral` is the probability that the first
`n` jumps all occur before the horizon, written as a weighted integral over the
free-coordinate simplex.  `sectorIntegral` is the probability of seeing exactly
`n` jumps.  Integrating out the last free coordinate shows that consecutive
arrival integrals differ by exactly one sector integral, so the partial sums of
the sector integrals telescope to `1 - arrivalIntegral`.  The arrival integrals
are dominated by `(2T)^n / n!` and vanish, hence the sector integrals sum to
one.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-! ### Weighted simplex integrals -/

/-- Product of per-coordinate exponential survival weights in free cube
coordinates.  Coordinate `i` carries rate `r i` over the scaled holding time
`T * u i`. -/
noncomputable def cubeExpWeight {n : ℕ} (r : Fin n → NNReal) (T : NNReal)
    (u : Fin n → I) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (Real.exp (-((r i : ℝ) * (T : ℝ) * (u i : ℝ))))

@[fun_prop]
theorem measurable_cubeExpWeight {n : ℕ} (r : Fin n → NNReal) (T : NNReal) :
    Measurable (cubeExpWeight r T) := by
  unfold cubeExpWeight
  fun_prop

/-- The product of the jump-intensity prefactors `r i * T`. -/
noncomputable def ratePrefixProduct {n : ℕ} (r : Fin n → NNReal)
    (T : NNReal) : ℝ≥0∞ :=
  ∏ i, ((r i : ℝ≥0∞) * (T : ℝ≥0∞))

/-- Unnormalized probability that the first `n` holding intervals fit inside
the horizon: the density of the first `n` jump times integrated over the
free-coordinate simplex. -/
noncomputable def arrivalIntegral {n : ℕ} (r : Fin n → NNReal)
    (T : NNReal) : ℝ≥0∞ :=
  ratePrefixProduct r T *
    ∫⁻ u in Simplex.freeSimplexSet n, cubeExpWeight r T u

/-- Residual fraction of the horizon left after the `n` free coordinates. -/
def residual {n : ℕ} (u : Fin n → I) : ℝ :=
  1 - ∑ i, ((u i : ℝ))

@[fun_prop]
theorem measurable_residual {n : ℕ} :
    Measurable (residual (n := n)) := by
  unfold residual
  fun_prop

/-- Probability of exactly `n` jumps: the first `n` holding intervals fit and
the terminal interval survives the residual time at rate `c`. -/
noncomputable def sectorIntegral {n : ℕ} (r : Fin n → NNReal) (c : NNReal)
    (T : NNReal) : ℝ≥0∞ :=
  ratePrefixProduct r T *
    ∫⁻ u in Simplex.freeSimplexSet n,
      cubeExpWeight r T u *
        ENNReal.ofReal (Real.exp (-((c : ℝ) * (T : ℝ) * residual u)))

/-- With no jump yet to place, the arrival integral is total. -/
theorem arrivalIntegral_zero (r : Fin 0 → NNReal) (T : NNReal) :
    arrivalIntegral r T = 1 := by
  have hset : Simplex.freeSimplexSet 0 = Set.univ := by
    ext u
    simp [Simplex.freeSimplexSet]
  unfold arrivalIntegral ratePrefixProduct cubeExpWeight
  simp [hset]

/-- Core one-dimensional computation: the exponential survival density of rate
`c` integrates to `1 - exp (-c * ρ)` over an initial segment of the unit
interval. -/
private theorem ofReal_mul_lintegral_exp_le (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal c *
        ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
          ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) =
      ENNReal.ofReal (1 - Real.exp (-(c * ρ))) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · simp [← hc0]
  · have hpre :
        ((fun a : I => (a : ℝ)) ⁻¹' Set.Icc (0 : ℝ) ρ) =
          {a : I | (a : ℝ) ≤ ρ} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨a.2.1, h⟩⟩
    rw [← hpre]
    rw [unitInterval.measurePreserving_coe.setLIntegral_comp_preimage_emb
      unitInterval.measurableEmbedding_coe
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-(c * x))))
      (Set.Icc 0 ρ)]
    change ENNReal.ofReal c *
        ∫⁻ x : ℝ,
          ENNReal.ofReal (Real.exp (-(c * x)))
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Icc 0 ρ)) = _
    rw [Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl hρ1)]
    have hcont : Continuous fun x : ℝ => Real.exp (-(c * x)) := by
      fun_prop
    have hint :
        Integrable (fun x : ℝ => Real.exp (-(c * x)))
          (volume.restrict (Set.Icc 0 ρ)) :=
      hcont.integrableOn_Icc
    have hnn :
        0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) ρ)]
          fun x : ℝ => Real.exp (-(c * x)) :=
      ae_of_all _ fun x => (Real.exp_pos _).le
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
      ← ENNReal.ofReal_mul hc]
    congr 1
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hρ0]
    have hInt :
        (∫ x : ℝ in (0 : ℝ)..ρ, Real.exp (-(c * x))) =
          (1 - Real.exp (-(c * ρ))) / c := by
      have hcomp :
          (fun x : ℝ => Real.exp (-(c * x))) =
            fun x : ℝ => Real.exp ((-c) * x) := by
        funext x
        ring_nf
      rw [hcomp]
      have hc' : -c ≠ 0 := neg_ne_zero.mpr hcpos.ne'
      rw [intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := ρ) (fun x : ℝ => Real.exp x) hc',
        integral_exp]
      simp only [smul_eq_mul, mul_zero, Real.exp_zero]
      field_simp
      ring
    rw [hInt, mul_div_cancel₀ _ hcpos.ne']

/-- Membership in the free simplex in plain coordinates. -/
private theorem mem_freeSimplexSet_iff {m : ℕ} (u : Fin m → I) :
    u ∈ Simplex.freeSimplexSet m ↔ (∑ i, ((u i : ℝ))) ≤ 1 := by
  simp [Simplex.freeSimplexSet]

/-- Integrating out the last free coordinate of the `(n + 1)`-jump arrival
integrand yields the failure probability of the terminal survival factor on
the `n`-jump simplex.

The statement is at the level of a bare rate vector, with no sector prefactor,
so the general finite-generator layer can use it directly. -/
theorem lintegral_cubeExpWeight_succ
    {n : ℕ} (r : Fin (n + 1) → NNReal) (T : NNReal) :
    ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) *
        ∫⁻ u in Simplex.freeSimplexSet (n + 1), cubeExpWeight r T u =
      ∫⁻ v in Simplex.freeSimplexSet n,
        cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          ENNReal.ofReal
            (1 - Real.exp
              (-((r (Fin.last n) : ℝ) * (T : ℝ) * residual v))) := by
  classical
  set c : NNReal := r (Fin.last n) with hc
  set F : I × (Fin n → I) → ℝ≥0∞ := fun p =>
    Set.indicator
      {q : I × (Fin n → I) | (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1}
      (fun q =>
        cubeExpWeight (fun i : Fin n => r i.castSucc) T q.2 *
          ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (q.1 : ℝ))))) p
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
        (Simplex.freeSimplexSet (n + 1)).indicator (cubeExpWeight r T) u := by
    intro u
    rw [happly u]
    by_cases hu : u ∈ Simplex.freeSimplexSet (n + 1)
    · have hsum := (mem_freeSimplexSet_iff u).1 hu
      rw [Fin.sum_univ_castSucc] at hsum
      have hmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∈
            {q : I × (Fin n → I) |
              (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
        change ((u (Fin.last n) : ℝ)) +
            ∑ j : Fin n, ((u j.castSucc : ℝ)) ≤ 1
        linarith
      simp only [hFdef]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu]
      unfold cubeExpWeight
      rw [Fin.prod_univ_castSucc]
    · have hnotmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∉
            {q : I × (Fin n → I) |
              (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
        intro hmem'
        apply hu
        rw [mem_freeSimplexSet_iff, Fin.sum_univ_castSucc]
        have : ((u (Fin.last n) : ℝ)) +
            ∑ j : Fin n, ((u j.castSucc : ℝ)) ≤ 1 := hmem'
        linarith
      simp only [hFdef]
      rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hu]
  have hsection : ∀ v : Fin n → I,
      ((c : ℝ≥0∞) * (T : ℝ≥0∞)) * ∫⁻ a : I, F (a, v) =
        (Simplex.freeSimplexSet n).indicator
          (fun v : Fin n → I =>
            cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              ENNReal.ofReal
                (1 - Real.exp
                  (-((c : ℝ) * (T : ℝ) * residual v)))) v := by
    intro v
    by_cases hv : v ∈ Simplex.freeSimplexSet n
    · have hsum : (∑ i, ((v i : ℝ))) ≤ 1 :=
        (mem_freeSimplexSet_iff v).1 hv
      have hsum0 : 0 ≤ ∑ i, ((v i : ℝ)) :=
        Finset.sum_nonneg fun i _ => (v i).2.1
      have hres0 : 0 ≤ residual v := by
        unfold residual
        linarith
      have hres1 : residual v ≤ 1 := by
        unfold residual
        linarith
      have hFav : ∀ a : I,
          F (a, v) =
            ({a : I | (a : ℝ) ≤ residual v}).indicator
              (fun a : I =>
                cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                  ENNReal.ofReal
                    (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ))))) a := by
        intro a
        simp only [hFdef]
        by_cases ha : (a : ℝ) ≤ residual v
        · have hmem' : ((a, v) : I × (Fin n → I)) ∈
              {q : I × (Fin n → I) |
                (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
            change (a : ℝ) + ∑ i, ((v i : ℝ)) ≤ 1
            unfold residual at ha
            linarith
          rw [Set.indicator_of_mem hmem',
            Set.indicator_of_mem
              (show a ∈ {a : I | (a : ℝ) ≤ residual v} from ha)]
        · have hnotmem' : ((a, v) : I × (Fin n → I)) ∉
              {q : I × (Fin n → I) |
                (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
            intro hmem'
            apply ha
            have : (a : ℝ) + ∑ i, ((v i : ℝ)) ≤ 1 := hmem'
            unfold residual
            linarith
          rw [Set.indicator_of_notMem hnotmem',
            Set.indicator_of_notMem
              (show a ∉ {a : I | (a : ℝ) ≤ residual v} from ha)]
      have hmeasSec : MeasurableSet {a : I | (a : ℝ) ≤ residual v} :=
        measurableSet_le (by fun_prop) measurable_const
      calc ((c : ℝ≥0∞) * (T : ℝ≥0∞)) * ∫⁻ a : I, F (a, v)
          = ((c : ℝ≥0∞) * (T : ℝ≥0∞)) *
              ∫⁻ a : I in {a : I | (a : ℝ) ≤ residual v},
                cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                  ENNReal.ofReal
                    (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) := by
            rw [lintegral_congr hFav, lintegral_indicator hmeasSec]
        _ = cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              (((c : ℝ≥0∞) * (T : ℝ≥0∞)) *
                ∫⁻ a : I in {a : I | (a : ℝ) ≤ residual v},
                  ENNReal.ofReal
                    (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ))))) := by
            rw [lintegral_const_mul _ (by fun_prop)]
            ring
        _ = cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              ENNReal.ofReal
                (1 - Real.exp
                  (-((c : ℝ) * (T : ℝ) * residual v))) := by
            congr 1
            have hcast :
                ((c : ℝ≥0∞) * (T : ℝ≥0∞)) =
                  ENNReal.ofReal ((c : ℝ) * (T : ℝ)) := by
              rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal,
                NNReal.coe_mul]
            rw [hcast]
            exact ofReal_mul_lintegral_exp_le ((c : ℝ) * (T : ℝ))
              (residual v) (by positivity) hres0 hres1
        _ = (Simplex.freeSimplexSet n).indicator
              (fun v : Fin n → I =>
                cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                  ENNReal.ofReal
                    (1 - Real.exp
                      (-((c : ℝ) * (T : ℝ) * residual v)))) v := by
            rw [Set.indicator_of_mem hv]
    · have h0 : ∀ a : I, F (a, v) = 0 := by
        intro a
        simp only [hFdef]
        apply Set.indicator_of_notMem
        intro hmem'
        apply hv
        rw [mem_freeSimplexSet_iff]
        have h1 : (a : ℝ) + ∑ i, ((v i : ℝ)) ≤ 1 := hmem'
        have h2 : 0 ≤ (a : ℝ) := a.2.1
        linarith
      rw [Set.indicator_of_notMem hv]
      simp [h0]
  calc ((c : ℝ≥0∞) * (T : ℝ≥0∞)) *
        ∫⁻ u in Simplex.freeSimplexSet (n + 1), cubeExpWeight r T u
      = ((c : ℝ≥0∞) * (T : ℝ≥0∞)) *
          ∫⁻ u,
            (Simplex.freeSimplexSet (n + 1)).indicator
              (cubeExpWeight r T) u := by
        rw [lintegral_indicator
          (Simplex.measurableSet_freeSimplexSet (n + 1))]
    _ = ((c : ℝ≥0∞) * (T : ℝ≥0∞)) * ∫⁻ u, F (e u) := by
        congr 1
        exact lintegral_congr fun u => (hFe u).symm
    _ = ((c : ℝ≥0∞) * (T : ℝ≥0∞)) * ∫⁻ p, F p := by
        rw [hmp.lintegral_comp hFmeas]
    _ = ((c : ℝ≥0∞) * (T : ℝ≥0∞)) *
          ∫⁻ v : Fin n → I, ∫⁻ a : I, F (a, v) := by
        rw [Measure.volume_eq_prod,
          lintegral_prod_symm F hFmeas.aemeasurable]
    _ = ∫⁻ v : Fin n → I,
          ((c : ℝ≥0∞) * (T : ℝ≥0∞)) * ∫⁻ a : I, F (a, v) := by
        rw [lintegral_const_mul' _ _ (by finiteness)]
    _ = ∫⁻ v : Fin n → I,
          (Simplex.freeSimplexSet n).indicator
            (fun v : Fin n → I =>
              cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                ENNReal.ofReal
                  (1 - Real.exp
                    (-((c : ℝ) * (T : ℝ) * residual v)))) v :=
        lintegral_congr hsection
    _ = ∫⁻ v in Simplex.freeSimplexSet n,
          cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
            ENNReal.ofReal
              (1 - Real.exp
                (-((r (Fin.last n) : ℝ) * (T : ℝ) * residual v))) := by
        rw [lintegral_indicator (Simplex.measurableSet_freeSimplexSet n)]

/-- Consecutive arrival integrals differ by exactly one sector integral. -/
theorem sectorIntegral_add_arrivalIntegral_succ
    {n : ℕ} (r : Fin (n + 1) → NNReal) (T : NNReal) :
    sectorIntegral (fun i : Fin n => r i.castSucc) (r (Fin.last n)) T +
        arrivalIntegral r T =
      arrivalIntegral (fun i : Fin n => r i.castSucc) T := by
  unfold sectorIntegral arrivalIntegral
  have hsplit : ratePrefixProduct r T =
      ratePrefixProduct (fun i : Fin n => r i.castSucc) T *
        ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) := by
    unfold ratePrefixProduct
    rw [Fin.prod_univ_castSucc]
  rw [hsplit, mul_assoc, lintegral_cubeExpWeight_succ r T, ← mul_add]
  congr 1
  rw [← lintegral_add_left (by fun_prop)]
  apply setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
  intro v hv
  dsimp only
  have hsum : (∑ i, ((v i : ℝ))) ≤ 1 := (mem_freeSimplexSet_iff v).1 hv
  have hres0 : 0 ≤ residual v := by
    unfold residual
    linarith
  have hx : 0 ≤ (r (Fin.last n) : ℝ) * (T : ℝ) * residual v := by
    positivity
  have hexp1 :
      Real.exp (-((r (Fin.last n) : ℝ) * (T : ℝ) * residual v)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.mpr hx)
  rw [← mul_add,
    ← ENNReal.ofReal_add (Real.exp_nonneg _) (by linarith)]
  rw [show Real.exp (-((r (Fin.last n) : ℝ) * (T : ℝ) * residual v)) +
      (1 - Real.exp (-((r (Fin.last n) : ℝ) * (T : ℝ) * residual v))) =
        1 from by ring]
  simp

/-! ### Vanishing tail -/

/-- The arrival integral of a rate sequence bounded by an arbitrary cap `R` is
dominated by the Poisson-type tail `(R T)^n / n!`. -/
theorem arrivalIntegral_le {n : ℕ} (r : Fin n → NNReal) (T R : NNReal)
    (hr : ∀ i, r i ≤ R) :
    arrivalIntegral r T ≤
      ((R : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
        ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  unfold arrivalIntegral
  have hweight : ∀ u : Fin n → I, cubeExpWeight r T u ≤ 1 := by
    intro u
    unfold cubeExpWeight
    apply Finset.prod_le_one'
    intro i _
    apply ENNReal.ofReal_le_one.2
    apply Real.exp_le_one_iff.2
    apply neg_nonpos.mpr
    exact mul_nonneg (mul_nonneg (r i).2 T.2) (u i).2.1
  calc ratePrefixProduct r T *
        ∫⁻ u in Simplex.freeSimplexSet n, cubeExpWeight r T u
      ≤ ratePrefixProduct r T *
          ∫⁻ _ in Simplex.freeSimplexSet n, (1 : ℝ≥0∞) :=
        mul_le_mul_right (lintegral_mono hweight) _
    _ = ratePrefixProduct r T *
          (volume : Measure (Fin n → I)) (Simplex.freeSimplexSet n) := by
        rw [setLIntegral_one]
    _ ≤ ((R : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
        rw [Simplex.volume_freeSimplexSet]
        apply mul_le_mul_left
        unfold ratePrefixProduct
        calc (∏ i, ((r i : ℝ≥0∞) * (T : ℝ≥0∞)))
            ≤ ∏ _i : Fin n, ((R : ℝ≥0∞) * (T : ℝ≥0∞)) := by
              apply Finset.prod_le_prod'
              intro i _
              apply mul_le_mul_left
              exact_mod_cast hr i
          _ = ((R : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The dominating Poisson-type tail vanishes for every rate cap `R`. -/
theorem tendsto_pow_mul_factorial_inv (T R : NNReal) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((R : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ)))
      Filter.atTop (nhds 0) := by
  have hconv : ∀ n : ℕ,
      ((R : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ)) =
        ENNReal.ofReal (((R : ℝ) * (T : ℝ)) ^ n / (n.factorial : ℝ)) := by
    intro n
    have hRT : ((R : ℝ≥0∞) * (T : ℝ≥0∞)) =
        ENNReal.ofReal ((R : ℝ) * (T : ℝ)) := by
      rw [ENNReal.ofReal_mul R.coe_nonneg]
      simp [ENNReal.ofReal_coe_nnreal]
    rw [hRT, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp only [hconv]
  have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := by simp
  rw [h0]
  apply ENNReal.tendsto_ofReal
  exact FloorSemiring.tendsto_pow_div_factorial_atTop ((R : ℝ) * (T : ℝ))

/-! ### The alternating two-state chain -/

/-- The state-dependent total escape rate of the asymmetric chain. -/
def stateRate : State → NNReal
  | .zero => 2
  | .one => 1

theorem stateRate_le_two (x : State) : stateRate x ≤ 2 := by
  cases x <;> norm_num [stateRate]

/-- Rates seen along the alternating chain started at `x`. -/
def chainRates (x : State) (n : ℕ) : Fin n → NNReal :=
  fun i => stateRate (iterateFlip i.1 x)

theorem chainRates_castSucc (x : State) (n : ℕ) :
    (fun i : Fin n => chainRates x (n + 1) i.castSucc) = chainRates x n := by
  funext i
  simp [chainRates]

theorem chainRates_last (x : State) (n : ℕ) :
    chainRates x (n + 1) (Fin.last n) = stateRate (iterateFlip n x) := by
  simp [chainRates]

/-- Arrival mass of the asymmetric chain started at `x`. -/
noncomputable def arrivalMass (T : NNReal) (x : State) (n : ℕ) : ℝ≥0∞ :=
  arrivalIntegral (chainRates x n) T

/-- Sector mass of the asymmetric chain started at `x`. -/
noncomputable def sectorMass (T : NNReal) (x : State) (n : ℕ) : ℝ≥0∞ :=
  sectorIntegral (chainRates x n) (stateRate (iterateFlip n x)) T

theorem sectorMass_add_arrivalMass_succ (T : NNReal) (x : State) (n : ℕ) :
    sectorMass T x n + arrivalMass T x (n + 1) = arrivalMass T x n := by
  have h := sectorIntegral_add_arrivalIntegral_succ (chainRates x (n + 1)) T
  rw [chainRates_castSucc, chainRates_last] at h
  exact h

theorem arrivalMass_zero (T : NNReal) (x : State) :
    arrivalMass T x 0 = 1 :=
  arrivalIntegral_zero _ T

/-- Partial sums of sector masses telescope against the arrival mass. -/
theorem sum_sectorMass_add_arrivalMass (T : NNReal) (x : State) (N : ℕ) :
    (∑ n ∈ Finset.range N, sectorMass T x n) + arrivalMass T x N = 1 := by
  induction N with
  | zero => simp [arrivalMass_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc,
        sectorMass_add_arrivalMass_succ]
      exact ih

theorem tendsto_arrivalMass (T : NNReal) (x : State) :
    Filter.Tendsto (fun n => arrivalMass T x n) Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n : ℕ =>
      ((2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
        ENNReal.ofReal (1 / (n.factorial : ℝ)))
    tendsto_const_nhds (by
      simpa using tendsto_pow_mul_factorial_inv T 2)
    (fun n => bot_le)
    (fun n => by
      simpa [arrivalMass] using arrivalIntegral_le (chainRates x n) T 2
        (fun i => stateRate_le_two _))

/-- The sector masses of the asymmetric chain sum to one for every initial
state. -/
theorem tsum_sectorMass (T : NNReal) (x : State) :
    ∑' n, sectorMass T x n = 1 := by
  have hpartial :
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, sectorMass T x n)
        Filter.atTop (nhds (∑' n, sectorMass T x n)) :=
    ENNReal.tendsto_nat_tsum _
  have hsum :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, sectorMass T x n) + arrivalMass T x N)
        Filter.atTop (nhds ((∑' n, sectorMass T x n) + 0)) :=
    hpartial.add (tendsto_arrivalMass T x)
  rw [add_zero] at hsum
  have hone :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, sectorMass T x n) + arrivalMass T x N)
        Filter.atTop (nhds 1) := by
    simp only [sum_sectorMass_add_arrivalMass]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hone
