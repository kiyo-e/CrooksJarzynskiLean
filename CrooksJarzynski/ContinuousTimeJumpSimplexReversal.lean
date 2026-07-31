/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpSimplex
import Mathlib.Data.Fin.Rev

/-!
# Reversal invariance of the free simplex chart

Time reversal of a fixed-horizon holding-time vector acts on the free simplex
coordinates as a shear (exchanging the first coordinate with the residual
coordinate) followed by a coordinate permutation.  This module proves that
this affine involution preserves every Lebesgue integral over the free
simplex, and computes its action on the completed holding-time vectors.

These lemmas are the measure-theoretic core of the path-reversal arguments
used by the continuous-time Crooks constructions; they are independent of any
particular state space or rate structure.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Simplex

/-- Reflection of the initial unit-interval coordinate across a variable
endpoint. The truncation is irrelevant on the interval of integration. -/
def reflectIic (ρ a : I) : I :=
  ⟨max 0 ((ρ : ℝ) - (a : ℝ)), le_max_left _ _,
    max_le (by norm_num) (by linarith [ρ.2.2, a.2.1])⟩

@[fun_prop]
theorem measurable_reflectIic :
    Measurable (fun p : I × I => reflectIic p.1 p.2) := by
  unfold reflectIic
  fun_prop

/-- Lebesgue measure on an initial segment of the unit interval is invariant
under reflection about its endpoint. -/
theorem lintegral_Iic_reflect (ρ : I) (f : I → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ a : I in Set.Iic ρ, f (reflectIic ρ a)) =
      ∫⁻ a : I in Set.Iic ρ, f a := by
  rcases unitInterval.measurableEmbedding_coe.exists_measurable_extend hf
      (fun _ => inferInstance) with ⟨F, hF, hFcoe⟩
  have hpre :
      ((fun a : I => (a : ℝ)) ⁻¹' Set.Icc (0 : ℝ) (ρ : ℝ)) =
        Set.Iic ρ := by
    ext a
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Iic]
    exact ⟨fun h => h.2, fun h => ⟨a.2.1, h⟩⟩
  rw [← hpre]
  have hleft :
      (∫⁻ a : I in (fun a : I => (a : ℝ)) ⁻¹'
          Set.Icc (0 : ℝ) (ρ : ℝ), f (reflectIic ρ a)) =
        ∫⁻ x : ℝ in Set.Icc 0 (ρ : ℝ), F ((ρ : ℝ) - x) := by
    have hcongr : Set.EqOn
        (fun a : I => f (reflectIic ρ a))
        (fun a : I => F ((ρ : ℝ) - (a : ℝ)))
        ((fun a : I => (a : ℝ)) ⁻¹' Set.Icc (0 : ℝ) (ρ : ℝ)) := by
      intro a ha
      dsimp only
      rw [← congrFun hFcoe (reflectIic ρ a)]
      apply congrArg F
      change max 0 ((ρ : ℝ) - (a : ℝ)) = (ρ : ℝ) - (a : ℝ)
      rw [max_eq_right (sub_nonneg.mpr ha.2)]
    rw [setLIntegral_congr_fun
      (measurableSet_Icc.preimage
        unitInterval.measurableEmbedding_coe.measurable) hcongr]
    rw [unitInterval.measurePreserving_coe.setLIntegral_comp_preimage_emb
      unitInterval.measurableEmbedding_coe
      (fun x : ℝ => F ((ρ : ℝ) - x)) (Set.Icc 0 (ρ : ℝ))]
    change (∫⁻ x : ℝ, F ((ρ : ℝ) - x)
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict
          (Set.Icc 0 (ρ : ℝ)))) = _
    rw [Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl ρ.2.2)]
  rw [hleft]
  have hreflect :=
    (volume : Measure ℝ).measurePreserving_sub_left (ρ : ℝ)
  have hpre' :
      (fun x : ℝ => (ρ : ℝ) - x) ⁻¹' Set.Icc 0 (ρ : ℝ) =
        Set.Icc 0 (ρ : ℝ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith
  have hreflint :
      (∫⁻ x : ℝ in Set.Icc 0 (ρ : ℝ), F ((ρ : ℝ) - x)) =
        ∫⁻ x : ℝ in Set.Icc 0 (ρ : ℝ), F x := by
    calc
      (∫⁻ x : ℝ in Set.Icc 0 (ρ : ℝ), F ((ρ : ℝ) - x)) =
          ∫⁻ x : ℝ in (fun x : ℝ => (ρ : ℝ) - x) ⁻¹'
            Set.Icc 0 (ρ : ℝ), F ((ρ : ℝ) - x) := by rw [hpre']
      _ = ∫⁻ x : ℝ in Set.Icc 0 (ρ : ℝ), F x :=
        hreflect.setLIntegral_comp_preimage measurableSet_Icc hF
  rw [hreflint]
  calc
    (∫⁻ x : ℝ in Set.Icc 0 (ρ : ℝ), F x) =
        ∫⁻ x : ℝ, F x
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict
            (Set.Icc 0 (ρ : ℝ))) := by
      rw [Measure.restrict_restrict measurableSet_Icc,
        Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl ρ.2.2)]
    _ = ∫⁻ a : I in (fun a : I => (a : ℝ)) ⁻¹'
          Set.Icc 0 (ρ : ℝ), F (a : ℝ) := by
      exact
        (unitInterval.measurePreserving_coe.setLIntegral_comp_preimage_emb
          unitInterval.measurableEmbedding_coe F
            (Set.Icc 0 (ρ : ℝ))).symm
    _ = ∫⁻ a : I in (fun a : I => (a : ℝ)) ⁻¹'
          Set.Icc 0 (ρ : ℝ), f a := by
      apply setLIntegral_congr_fun
        (measurableSet_Icc.preimage
          unitInterval.measurableEmbedding_coe.measurable)
      intro a _
      exact congrFun hFcoe a

/-- Remaining length after all coordinates except the first have been fixed. -/
def remainingIic {n : ℕ} (v : Fin n → I) : I :=
  ⟨max 0 (1 - ∑ i, (v i : ℝ)), le_max_left _ _,
    max_le (by norm_num)
      (by
        have hsum : 0 ≤ ∑ i, (v i : ℝ) :=
          Finset.sum_nonneg fun i _ => (v i).2.1
        linarith)⟩

/-- Insert a distinguished zeroth coordinate. -/
def consFin {n : ℕ} (p : I × (Fin n → I)) : Fin (n + 1) → I :=
  Fin.cons p.1 p.2

/-- Replace the first free coordinate by the residual holding fraction. -/
def simplexShear {n : ℕ} (u : Fin (n + 1) → I) :
    Fin (n + 1) → I :=
  consFin
    (reflectIic (remainingIic (fun i => u i.succ)) (u 0),
      fun i => u i.succ)

@[fun_prop]
theorem measurable_consFin {n : ℕ} :
    Measurable (consFin (n := n)) := by
  change Measurable (fun p : I × (Fin n → I) =>
    Fin.cons (α := fun _ : Fin (n + 1) => I) p.1 p.2)
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => I) 0).symm.measurable

@[fun_prop]
theorem measurable_remainingIic {n : ℕ} :
    Measurable (remainingIic (n := n)) := by
  unfold remainingIic
  fun_prop

@[fun_prop]
theorem measurable_simplexShear {n : ℕ} :
    Measurable (simplexShear (n := n)) := by
  unfold simplexShear
  fun_prop

/-- The free simplex volume is invariant when its first coordinate is
exchanged with the residual coordinate. -/
theorem lintegral_freeSimplex_shear {n : ℕ}
    (G : (Fin (n + 1) → I) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in Simplex.freeSimplexSet (n + 1), G (simplexShear u)) =
      ∫⁻ u in Simplex.freeSimplexSet (n + 1), G u := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => I) 0
  let s : Set (I × (Fin n → I)) :=
    {p | (p.1 : ℝ) + ∑ i, (p.2 i : ℝ) ≤ 1}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le (by fun_prop) measurable_const
  have he_apply (u : Fin (n + 1) → I) :
      e u = (u 0, fun i => u i.succ) := by
    apply Prod.ext
    · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    · funext i
      rfl
  have hcons (p : I × (Fin n → I)) :
      e.symm p = consFin p := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, consFin, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv]
    · simp [e, consFin, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv]
  have hpre : e ⁻¹' s = Simplex.freeSimplexSet (n + 1) := by
    ext u
    rw [Set.mem_preimage]
    simp only [he_apply, s, Set.mem_setOf_eq, Simplex.freeSimplexSet,
      Simplex.coe_unitNNReal]
    rw [Fin.sum_univ_succ]
  let left : I × (Fin n → I) → ℝ≥0∞ := fun p =>
    s.indicator
      (fun q => G (consFin
        (reflectIic (remainingIic q.2) q.1, q.2))) p
  let right : I × (Fin n → I) → ℝ≥0∞ := fun p =>
    s.indicator (fun q => G (consFin q)) p
  have hleft : Measurable left := by
    dsimp [left]
    apply Measurable.indicator
    · fun_prop
    · exact hs
  have hright : Measurable right := by
    dsimp [right]
    apply Measurable.indicator
    · fun_prop
    · exact hs
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => I) 0
  have htransport_left :
      (∫⁻ u in Simplex.freeSimplexSet (n + 1), G (simplexShear u)) =
        ∫⁻ p, left p := by
    rw [← hpre]
    rw [← lintegral_indicator (hs.preimage e.measurable)]
    calc
      (∫⁻ u, (e ⁻¹' s).indicator (fun u => G (simplexShear u)) u) =
          ∫⁻ u, left (e u) := by
        apply lintegral_congr
        intro u
        by_cases hu : e u ∈ s
        · rw [Set.indicator_of_mem (show u ∈ e ⁻¹' s from hu),
            show left (e u) =
              G (consFin
                (reflectIic (remainingIic (e u).2) (e u).1, (e u).2)) by
              dsimp only [left]
              rw [Set.indicator_of_mem hu]]
          rw [he_apply]
          rfl
        · rw [Set.indicator_of_notMem (show u ∉ e ⁻¹' s from hu),
            show left (e u) = 0 by
              dsimp only [left]
              rw [Set.indicator_of_notMem hu]]
      _ = ∫⁻ p, left p := hmp.lintegral_comp hleft
  have htransport_right :
      (∫⁻ u in Simplex.freeSimplexSet (n + 1), G u) =
        ∫⁻ p, right p := by
    rw [← hpre]
    rw [← lintegral_indicator (hs.preimage e.measurable)]
    calc
      (∫⁻ u, (e ⁻¹' s).indicator G u) =
          ∫⁻ u, right (e u) := by
        apply lintegral_congr
        intro u
        by_cases hu : e u ∈ s
        · rw [Set.indicator_of_mem (show u ∈ e ⁻¹' s from hu),
            show right (e u) = G (consFin (e u)) by
              dsimp only [right]
              rw [Set.indicator_of_mem hu]]
          rw [← hcons (e u), e.symm_apply_apply]
        · rw [Set.indicator_of_notMem (show u ∉ e ⁻¹' s from hu),
            show right (e u) = 0 by
              dsimp only [right]
              rw [Set.indicator_of_notMem hu]]
      _ = ∫⁻ p, right p := hmp.lintegral_comp hright
  rw [htransport_left, htransport_right]
  rw [Measure.volume_eq_prod,
    lintegral_prod_symm left hleft.aemeasurable,
    lintegral_prod_symm right hright.aemeasurable]
  apply lintegral_congr
  intro v
  by_cases hv : v ∈ Simplex.freeSimplexSet n
  · have hsum : (∑ i, (v i : ℝ)) ≤ 1 := by
      simpa [Simplex.freeSimplexSet] using hv
    have hremaining :
        (remainingIic v : ℝ) = 1 - ∑ i, (v i : ℝ) := by
      change max 0 (1 - ∑ i, (v i : ℝ)) = _
      rw [max_eq_right (sub_nonneg.mpr hsum)]
    have hsection :
        {a : I | (a : ℝ) + ∑ i, (v i : ℝ) ≤ 1} =
          Set.Iic (remainingIic v) := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_Iic]
      rw [Subtype.mk_le_mk, hremaining]
      constructor <;> intro h <;> linarith
    have hf : Measurable
        (fun a : I => G (consFin (a, v))) := by fun_prop
    calc
      (∫⁻ a : I, left (a, v)) =
          ∫⁻ a : I in Set.Iic (remainingIic v),
            G (consFin (reflectIic (remainingIic v) a, v)) := by
        rw [← lintegral_indicator measurableSet_Iic]
        apply lintegral_congr
        intro a
        have hiff : (a, v) ∈ s ↔ a ∈ Set.Iic (remainingIic v) := by
          simpa [s] using Set.ext_iff.mp hsection a
        dsimp only [left]
        by_cases ha : a ∈ Set.Iic (remainingIic v)
        · rw [Set.indicator_of_mem ha,
            Set.indicator_of_mem (hiff.mpr ha)]
        · rw [Set.indicator_of_notMem ha,
            Set.indicator_of_notMem (fun h => ha (hiff.mp h))]
      _ = ∫⁻ a : I in Set.Iic (remainingIic v),
            G (consFin (a, v)) :=
        lintegral_Iic_reflect (remainingIic v)
          (fun a => G (consFin (a, v))) hf
      _ = ∫⁻ a : I, right (a, v) := by
        rw [← lintegral_indicator measurableSet_Iic]
        apply lintegral_congr
        intro a
        have hiff : (a, v) ∈ s ↔ a ∈ Set.Iic (remainingIic v) := by
          simpa [s] using Set.ext_iff.mp hsection a
        dsimp only [right]
        by_cases ha : a ∈ Set.Iic (remainingIic v)
        · rw [Set.indicator_of_mem ha,
            Set.indicator_of_mem (hiff.mpr ha)]
        · rw [Set.indicator_of_notMem ha,
            Set.indicator_of_notMem (fun h => ha (hiff.mp h))]
  · have hzero : ∀ a : I, (a, v) ∉ s := by
      intro a ha
      apply hv
      have ha0 : 0 ≤ (a : ℝ) := a.2.1
      have hsum : (a : ℝ) + ∑ i, (v i : ℝ) ≤ 1 := by
        change (a : ℝ) + ∑ i, (v i : ℝ) ≤ 1 at ha
        exact ha
      change ∑ i, (v i : ℝ) ≤ 1
      linarith
    apply lintegral_congr
    intro a
    simp [left, right, Set.indicator_of_notMem (hzero a)]

/-- Reverse all free coordinates except the distinguished residual coordinate. -/
def tailReverseEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.cases 0 (fun i => i.rev.succ)
  invFun := Fin.cases 0 (fun i => i.rev.succ)
  left_inv i := by
    refine Fin.cases rfl (fun j => ?_) i
    simp
  right_inv i := by
    refine Fin.cases rfl (fun j => ?_) i
    simp

def reverseTail {n : ℕ} (u : Fin (n + 1) → I) :
    Fin (n + 1) → I :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) => I) (tailReverseEquiv n) u

@[fun_prop]
theorem measurable_reverseTail {n : ℕ} :
    Measurable (reverseTail (n := n)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) => I) (tailReverseEquiv n)).measurable

/-- Coordinate permutations preserve every measurable integral over the free
simplex. -/
theorem lintegral_freeSimplex_reverseTail {n : ℕ}
    (G : (Fin (n + 1) → I) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in Simplex.freeSimplexSet (n + 1), G (reverseTail u)) =
      ∫⁻ u in Simplex.freeSimplexSet (n + 1), G u := by
  let p := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) => I) (tailReverseEquiv n)
  have hp := MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin (n + 1) => I) (tailReverseEquiv n)
  have hpre : p ⁻¹' Simplex.freeSimplexSet (n + 1) =
      Simplex.freeSimplexSet (n + 1) := by
    ext u
    simp only [Set.mem_preimage, Simplex.freeSimplexSet,
      Simplex.coe_unitNNReal]
    have hsum :
        (∑ i, (p u i : ℝ)) = ∑ i, (u i : ℝ) := by
      calc
        (∑ i, (p u i : ℝ)) =
            ∑ i, (p u ((tailReverseEquiv n) i) : ℝ) :=
          ((tailReverseEquiv n).sum_comp
            (fun i => (p u i : ℝ))).symm
        _ = ∑ i, (u i : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg Subtype.val (by
            simpa [p] using
              (MeasurableEquiv.piCongrLeft_apply_apply
                (β := fun _ : Fin (n + 1) => I)
                (tailReverseEquiv n) u i))
    change (∑ i, (p u i : ℝ) ≤ 1) ↔ ∑ i, (u i : ℝ) ≤ 1
    rw [hsum]
  change (∫⁻ u in Simplex.freeSimplexSet (n + 1), G (p u)) = _
  calc
    (∫⁻ u in Simplex.freeSimplexSet (n + 1), G (p u)) =
        ∫⁻ u in p ⁻¹' Simplex.freeSimplexSet (n + 1), G (p u) := by
      rw [hpre]
    _ = ∫⁻ u in Simplex.freeSimplexSet (n + 1), G u :=
      hp.setLIntegral_comp_preimage
        (Simplex.measurableSet_freeSimplexSet (n + 1)) hG

/-- Free coordinates corresponding to reversal of the completed holding-time
vector. -/
def reverseFree {n : ℕ} (u : Fin (n + 1) → I) :
    Fin (n + 1) → I :=
  reverseTail (simplexShear u)

@[fun_prop]
theorem measurable_reverseFree {n : ℕ} :
    Measurable (reverseFree (n := n)) :=
  measurable_reverseTail.comp measurable_simplexShear

/-- Completed-simplex reversal preserves every measurable integral. -/
theorem lintegral_freeSimplex_reverseFree {n : ℕ}
    (G : (Fin (n + 1) → I) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in Simplex.freeSimplexSet (n + 1), G (reverseFree u)) =
      ∫⁻ u in Simplex.freeSimplexSet (n + 1), G u := by
  unfold reverseFree
  calc
    (∫⁻ u in Simplex.freeSimplexSet (n + 1),
        G (reverseTail (simplexShear u))) =
        ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          G (reverseTail u) := by
      exact lintegral_freeSimplex_shear
        (fun u => G (reverseTail u))
        (hG.comp measurable_reverseTail)
    _ = ∫⁻ u in Simplex.freeSimplexSet (n + 1), G u :=
      lintegral_freeSimplex_reverseTail G hG

theorem reverseFree_zero {n : ℕ} (u : Fin (n + 1) → I)
    (hu : u ∈ Simplex.freeSimplexSet (n + 1)) :
    (reverseFree u 0 : ℝ) = 1 - ∑ i, (u i : ℝ) := by
  have hsum : (∑ i, (u i : ℝ)) ≤ 1 := by
    simpa [Simplex.freeSimplexSet] using hu
  have htail : (∑ i : Fin n, (u i.succ : ℝ)) ≤ 1 := by
    have hzero : 0 ≤ (u 0 : ℝ) := (u 0).2.1
    rw [Fin.sum_univ_succ] at hsum
    linarith
  unfold reverseFree reverseTail simplexShear
  change (consFin
    (reflectIic (remainingIic (fun i => u i.succ)) (u 0),
      fun i => u i.succ) ((tailReverseEquiv n).symm 0) : ℝ) = _
  change (reflectIic (remainingIic (fun i => u i.succ)) (u 0) : ℝ) = _
  change max 0
    ((max 0 (1 - ∑ i : Fin n, (u i.succ : ℝ))) - (u 0 : ℝ)) = _
  rw [max_eq_right (sub_nonneg.mpr htail)]
  rw [max_eq_right]
  · rw [Fin.sum_univ_succ]
    ring
  · rw [Fin.sum_univ_succ] at hsum
    linarith

theorem reverseFree_succ {n : ℕ} (u : Fin (n + 1) → I)
    (i : Fin n) :
    reverseFree u i.succ = u i.rev.succ := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (n + 1) => I)
    (tailReverseEquiv n) (simplexShear u) i.rev.succ
  simpa [reverseFree, reverseTail, tailReverseEquiv,
    simplexShear, consFin] using h

theorem sum_reverseFree {n : ℕ} (u : Fin (n + 1) → I)
    (hu : u ∈ Simplex.freeSimplexSet (n + 1)) :
    ∑ i, (reverseFree u i : ℝ) = 1 - (u 0 : ℝ) := by
  rw [Fin.sum_univ_succ, reverseFree_zero u hu]
  simp_rw [reverseFree_succ]
  have hrev :
      (∑ i : Fin n, (u i.rev.succ : ℝ)) =
        ∑ i : Fin n, (u i.succ : ℝ) := by
    exact Fintype.sum_equiv Fin.revPerm
      (fun i : Fin n => (u i.rev.succ : ℝ))
      (fun i : Fin n => (u i.succ : ℝ)) (fun _ => rfl)
  rw [hrev]
  rw [Fin.sum_univ_succ]
  ring

/-- Completing the free coordinates and then reversing them reverses the
completed holding-time vector. -/
theorem holdingTimesOfFree_reverseFree {n : ℕ} (T : NNReal)
    (u : Fin (n + 1) → I)
    (hu : u ∈ Simplex.freeSimplexSet (n + 1)) :
    Simplex.holdingTimesOfFree T (reverseFree u) =
      fun i => Simplex.holdingTimesOfFree T u i.rev := by
  have hsum :
      (∑ i, Simplex.unitNNReal (u i)) ≤ (1 : NNReal) := by
    have hu' := hu
    change (∑ i, (u i : ℝ)) ≤ 1 at hu'
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sum]
    simpa only [Simplex.coe_unitNNReal, NNReal.coe_one] using hu'
  have hscaled :
      (∑ i, T * Simplex.unitNNReal (u i)) ≤ T := by
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_right hsum T
  have hsumReverse :
      (∑ i, Simplex.unitNNReal (reverseFree u i)) ≤ (1 : NNReal) := by
    have hsumReverse' :
        (∑ i, (reverseFree u i : ℝ)) ≤ 1 := by
      rw [sum_reverseFree u hu]
      exact sub_le_self 1 (u 0).2.1
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sum]
    simpa only [Simplex.coe_unitNNReal, NNReal.coe_one] using hsumReverse'
  have hscaledReverse :
      (∑ i, T * Simplex.unitNNReal (reverseFree u i)) ≤ T := by
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_right hsumReverse T
  funext i
  apply NNReal.eq
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Simplex.holdingTimesOfFree, Fin.snoc_last, Fin.rev_last,
      Fin.snoc_apply_zero, NNReal.coe_sub hscaledReverse, NNReal.coe_sum,
      NNReal.coe_mul, Simplex.coe_unitNNReal]
    rw [← Finset.mul_sum]
    rw [sum_reverseFree u hu]
    ring
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Simplex.holdingTimesOfFree, Fin.snoc_castSucc,
        Fin.rev_castSucc, Fin.rev_zero, NNReal.coe_mul,
        Simplex.coe_unitNNReal, reverseFree_zero u hu]
      rw [Fin.succ_last, Fin.snoc_last, NNReal.coe_sub hscaled,
        NNReal.coe_sum]
      simp only [NNReal.coe_mul, Simplex.coe_unitNNReal]
      rw [← Finset.mul_sum]
      ring
    · simp only [Simplex.holdingTimesOfFree, Fin.snoc_castSucc,
        Fin.rev_castSucc, Fin.rev_succ, NNReal.coe_mul,
        Simplex.coe_unitNNReal, reverseFree_succ]
      rw [show j.rev.castSucc.succ = (j.rev.succ).castSucc by rfl,
        Fin.snoc_castSucc]
      simp only [NNReal.coe_mul, Simplex.coe_unitNNReal]

end Simplex
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
