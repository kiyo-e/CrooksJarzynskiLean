/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricFixedInitial
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parity evaluation for the asymmetric two-state chain

This module evaluates the parity-filtered sums of the asymmetric jump-sector
masses.  The proof uses a first-jump renewal equation on a variable remaining
fraction of the fixed physical horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample
namespace Renewal

/-- The free simplex with total available fraction `ρ` instead of one. -/
def freeSimplexSetAt (n : ℕ) (ρ : I) : Set (Fin n → I) :=
  {u | ∑ i, (u i : ℝ) ≤ (ρ : ℝ)}

/-- The variable-horizon free simplex is measurable. -/
theorem measurableSet_freeSimplexSetAt (n : ℕ) (ρ : I) :
    MeasurableSet (freeSimplexSetAt n ρ) := by
  unfold freeSimplexSetAt
  exact measurableSet_le (by fun_prop) measurable_const

/-- The admissible first holding fractions inside a remaining fraction `ρ`. -/
def firstHoldingSet (ρ : I) : Set I :=
  {a | (a : ℝ) ≤ (ρ : ℝ)}

/-- The admissible first-holding set is measurable. -/
theorem measurableSet_firstHoldingSet (ρ : I) :
    MeasurableSet (firstHoldingSet ρ) := by
  unfold firstHoldingSet
  exact measurableSet_le (by fun_prop) measurable_const

/-- The fraction of the horizon remaining after a first holding fraction `a`. -/
def remainingFraction (ρ a : I) : I :=
  ⟨max ((ρ : ℝ) - (a : ℝ)) 0,
    le_max_right _ _,
    max_le (by linarith [ρ.2.2, a.2.1]) (by norm_num)⟩

@[simp]
theorem coe_remainingFraction_of_le (ρ a : I)
    (ha : (a : ℝ) ≤ (ρ : ℝ)) :
    (remainingFraction ρ a : ℝ) = (ρ : ℝ) - (a : ℝ) := by
  simp [remainingFraction, max_eq_left (sub_nonneg.mpr ha)]

/-- Tonelli decomposition of a variable free simplex at its first coordinate. -/
theorem lintegral_freeSimplexSetAt_succ
    {n : ℕ} (ρ : I) (g : I → (Fin n → I) → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    ∫⁻ u in freeSimplexSetAt (n + 1) ρ,
        g (u 0) (fun i : Fin n => u i.succ) =
      ∫⁻ a in firstHoldingSet ρ,
        ∫⁻ v in freeSimplexSetAt n (remainingFraction ρ a), g a v := by
  classical
  set s : Set (I × (Fin n → I)) :=
    {p | (p.1 : ℝ) + ∑ i, (p.2 i : ℝ) ≤ (ρ : ℝ)} with hsdef
  have hs : MeasurableSet s := by
    rw [hsdef]
    exact measurableSet_le (by fun_prop) measurable_const
  set h : I × (Fin n → I) → ℝ≥0∞ :=
    s.indicator (fun p => g p.1 p.2) with hhdef
  have hh : Measurable h := by
    apply Measurable.indicator
    · exact hg
    · exact hs
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => I) 0
  set e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => I) 0 with hedef
  have happly : ∀ u : Fin (n + 1) → I,
      e u = (u 0, fun j : Fin n => u j.succ) := by
    intro u
    simp only [hedef, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.coe_mk, Equiv.symm_mk, Equiv.coe_fn_mk]
    refine congrArg (Prod.mk _) ?_
    funext j
    simp [Fin.removeNth_apply, Fin.zero_succAbove]
  have hhe : ∀ u : Fin (n + 1) → I,
      h (e u) =
        (freeSimplexSetAt (n + 1) ρ).indicator
          (fun u => g (u 0) (fun i : Fin n => u i.succ)) u := by
    intro u
    rw [happly u]
    by_cases hu : u ∈ freeSimplexSetAt (n + 1) ρ
    · have hsum :
          (u 0 : ℝ) + ∑ i : Fin n, (u i.succ : ℝ) ≤ (ρ : ℝ) := by
        change (∑ i : Fin (n + 1), (u i : ℝ)) ≤ (ρ : ℝ) at hu
        simpa only [Fin.sum_univ_succ] using hu
      have hmem :
          ((u 0, fun i : Fin n => u i.succ) : I × (Fin n → I)) ∈ s := by
        rw [hsdef]
        exact hsum
      simp only [hhdef]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu]
    · have hnotmem :
          ((u 0, fun i : Fin n => u i.succ) : I × (Fin n → I)) ∉ s := by
        intro hmem
        apply hu
        change (∑ i : Fin (n + 1), (u i : ℝ)) ≤ (ρ : ℝ)
        rw [Fin.sum_univ_succ]
        simpa only [hsdef, Set.mem_setOf_eq] using hmem
      simp only [hhdef]
      rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hu]
  have hsection : ∀ a : I,
      (∫⁻ v : Fin n → I, h (a, v)) =
        (firstHoldingSet ρ).indicator
          (fun a =>
            ∫⁻ v in freeSimplexSetAt n (remainingFraction ρ a), g a v) a := by
    intro a
    by_cases ha : (a : ℝ) ≤ (ρ : ℝ)
    · have hav : ∀ v : Fin n → I,
          h (a, v) =
            (freeSimplexSetAt n (remainingFraction ρ a)).indicator
              (fun v => g a v) v := by
        intro v
        simp only [hhdef]
        by_cases hv : v ∈ freeSimplexSetAt n (remainingFraction ρ a)
        · have hsum :
              (∑ i : Fin n, (v i : ℝ)) ≤
                (ρ : ℝ) - (a : ℝ) := by
            change (∑ i : Fin n, (v i : ℝ)) ≤
              (remainingFraction ρ a : ℝ) at hv
            simpa [coe_remainingFraction_of_le ρ a ha] using hv
          have hmem : ((a, v) : I × (Fin n → I)) ∈ s := by
            rw [hsdef]
            change (a : ℝ) + ∑ i : Fin n, (v i : ℝ) ≤ (ρ : ℝ)
            linarith
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hv]
        · have hnotmem : ((a, v) : I × (Fin n → I)) ∉ s := by
            intro hmem
            apply hv
            change (∑ i : Fin n, (v i : ℝ)) ≤
              (remainingFraction ρ a : ℝ)
            rw [coe_remainingFraction_of_le ρ a ha]
            have hsum :
                (a : ℝ) + ∑ i : Fin n, (v i : ℝ) ≤ (ρ : ℝ) := by
              simpa only [hsdef, Set.mem_setOf_eq] using hmem
            linarith
          rw [Set.indicator_of_notMem hnotmem,
            Set.indicator_of_notMem hv]
      calc
        (∫⁻ v : Fin n → I, h (a, v)) =
            ∫⁻ v : Fin n → I,
              (freeSimplexSetAt n (remainingFraction ρ a)).indicator
                (fun v => g a v) v :=
          lintegral_congr hav
        _ = ∫⁻ v in freeSimplexSetAt n (remainingFraction ρ a), g a v := by
          rw [lintegral_indicator
            (measurableSet_freeSimplexSetAt n (remainingFraction ρ a))]
        _ = (firstHoldingSet ρ).indicator
            (fun a =>
              ∫⁻ v in freeSimplexSetAt n (remainingFraction ρ a), g a v) a := by
          rw [Set.indicator_of_mem
            (show a ∈ firstHoldingSet ρ from ha)]
    · have hzero : ∀ v : Fin n → I, h (a, v) = 0 := by
        intro v
        simp only [hhdef]
        apply Set.indicator_of_notMem
        intro hmem
        apply ha
        have hsum0 : 0 ≤ ∑ i : Fin n, (v i : ℝ) :=
          Finset.sum_nonneg fun i _ => (v i).2.1
        have hsum :
            (a : ℝ) + ∑ i : Fin n, (v i : ℝ) ≤ (ρ : ℝ) := by
          simpa only [hsdef, Set.mem_setOf_eq] using hmem
        linarith
      rw [Set.indicator_of_notMem
        (show a ∉ firstHoldingSet ρ from ha)]
      simp [hzero]
  calc
    (∫⁻ u in freeSimplexSetAt (n + 1) ρ,
        g (u 0) (fun i : Fin n => u i.succ)) =
        ∫⁻ u,
          (freeSimplexSetAt (n + 1) ρ).indicator
            (fun u => g (u 0) (fun i : Fin n => u i.succ)) u := by
      rw [lintegral_indicator (measurableSet_freeSimplexSetAt (n + 1) ρ)]
    _ = ∫⁻ u, h (e u) :=
      lintegral_congr fun u => (hhe u).symm
    _ = ∫⁻ p, h p := by
      rw [hmp.lintegral_comp hh]
    _ = ∫⁻ a : I, ∫⁻ v : Fin n → I, h (a, v) := by
      rw [Measure.volume_eq_prod, lintegral_prod h hh.aemeasurable]
    _ = ∫⁻ a : I,
        (firstHoldingSet ρ).indicator
          (fun a =>
            ∫⁻ v in freeSimplexSetAt n (remainingFraction ρ a), g a v) a :=
      lintegral_congr hsection
    _ = ∫⁻ a in firstHoldingSet ρ,
        ∫⁻ v in freeSimplexSetAt n (remainingFraction ρ a), g a v := by
      rw [lintegral_indicator (measurableSet_firstHoldingSet ρ)]

/-- At the full remaining fraction, the variable simplex is the standard free
simplex. -/
theorem freeSimplexSetAt_one (n : ℕ) :
    freeSimplexSetAt n (1 : I) = Simplex.freeSimplexSet n := by
  ext u
  simp [freeSimplexSetAt, Simplex.freeSimplexSet]

/-- Arrival mass for `n` jumps when only the fraction `ρ` of the fixed physical
horizon `T` is available. -/
noncomputable def arrivalIntegralAt {n : ℕ} (r : Fin n → NNReal)
    (T : NNReal) (ρ : I) : ℝ≥0∞ :=
  ratePrefixProduct r T *
    ∫⁻ u in freeSimplexSetAt n ρ, cubeExpWeight r T u

/-- Variable-horizon arrival mass along the alternating chain started at `x`. -/
noncomputable def arrivalMassAt
    (T : NNReal) (ρ : I) (x : State) (n : ℕ) : ℝ≥0∞ :=
  arrivalIntegralAt (chainRates x n) T ρ

/-- Residual horizon fraction after all free holding fractions have been used. -/
def residualAt {n : ℕ} (ρ : I) (u : Fin n → I) : ℝ :=
  (ρ : ℝ) - ∑ i, (u i : ℝ)

@[fun_prop]
theorem measurable_residualAt {n : ℕ} (ρ : I) :
    Measurable (residualAt (n := n) ρ) := by
  unfold residualAt
  fun_prop

/-- Exactly-`n`-jump mass on a remaining horizon fraction `ρ`. -/
noncomputable def sectorIntegralAt {n : ℕ} (r : Fin n → NNReal)
    (c : NNReal) (T : NNReal) (ρ : I) : ℝ≥0∞ :=
  ratePrefixProduct r T *
    ∫⁻ u in freeSimplexSetAt n ρ,
      cubeExpWeight r T u *
        ENNReal.ofReal
          (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt ρ u)))

/-- Variable-horizon sector mass along the alternating asymmetric chain. -/
noncomputable def sectorMassAt
    (T : NNReal) (ρ : I) (x : State) (n : ℕ) : ℝ≥0∞ :=
  sectorIntegralAt (chainRates x n) (stateRate (iterateFlip n x)) T ρ

/-- The variable-horizon construction at `ρ = 1` is the existing arrival mass. -/
theorem arrivalMassAt_one (T : NNReal) (x : State) (n : ℕ) :
    arrivalMassAt T (1 : I) x n = arrivalMass T x n := by
  simp [arrivalMassAt, arrivalIntegralAt, arrivalMass, arrivalIntegral,
    freeSimplexSetAt_one]

/-- The variable-horizon sector construction at `ρ = 1` is the existing sector
mass. -/
theorem sectorMassAt_one (T : NNReal) (x : State) (n : ℕ) :
    sectorMassAt T (1 : I) x n = sectorMass T x n := by
  unfold sectorMassAt sectorIntegralAt sectorMass sectorIntegral residualAt
  rw [freeSimplexSetAt_one]

/-- Before any jump is requested, every remaining horizon has arrival mass one. -/
theorem arrivalMassAt_zero (T : NNReal) (ρ : I) (x : State) :
    arrivalMassAt T ρ x 0 = 1 := by
  have hset : freeSimplexSetAt 0 ρ = Set.univ := by
    ext u
    simp [freeSimplexSetAt, ρ.2.1]
  simp [arrivalMassAt, arrivalIntegralAt, ratePrefixProduct,
    cubeExpWeight, hset]

/-- The zero-jump sector is the survival probability over the remaining
fraction of the horizon. -/
theorem sectorMassAt_zero (T : NNReal) (ρ : I) (x : State) :
    sectorMassAt T ρ x 0 =
      ENNReal.ofReal
        (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * (ρ : ℝ)))) := by
  have hset : freeSimplexSetAt 0 ρ = Set.univ := by
    ext u
    simp [freeSimplexSetAt, ρ.2.1]
  simp [sectorMassAt, sectorIntegralAt, ratePrefixProduct,
    cubeExpWeight, residualAt, chainRates, hset]

/-- Iterated flipping commutes with changing the prescribed initial state by one
flip. -/
theorem iterateFlip_flip_start (n : ℕ) (x : State) :
    iterateFlip n (flip x) = flip (iterateFlip n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterateFlip_succ, ih, flip_flip]

/-- Removing the first rate from an alternating rate sequence starts the same
sequence at the flipped state. -/
theorem chainRates_succ (x : State) (n : ℕ) :
    (fun i : Fin n => chainRates x (n + 1) i.succ) =
      chainRates (flip x) n := by
  funext i
  simp [chainRates, iterateFlip_flip_start]

end Renewal
end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
