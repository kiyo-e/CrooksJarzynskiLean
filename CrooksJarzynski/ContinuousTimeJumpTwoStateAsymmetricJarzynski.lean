/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetric
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricNormalization
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

/-! ### Reversal of the free simplex chart -/

/-- Reflection of the initial unit-interval coordinate across a variable
endpoint. The truncation is irrelevant on the interval of integration. -/
private def reflectIic (ρ a : I) : I :=
  ⟨max 0 ((ρ : ℝ) - (a : ℝ)), le_max_left _ _,
    max_le (by norm_num) (by linarith [ρ.2.2, a.2.1])⟩

@[fun_prop]
private theorem measurable_reflectIic :
    Measurable (fun p : I × I => reflectIic p.1 p.2) := by
  unfold reflectIic
  fun_prop

/-- Lebesgue measure on an initial segment of the unit interval is invariant
under reflection about its endpoint. -/
private theorem lintegral_Iic_reflect (ρ : I) (f : I → ℝ≥0∞)
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
private def remainingIic {n : ℕ} (v : Fin n → I) : I :=
  ⟨max 0 (1 - ∑ i, (v i : ℝ)), le_max_left _ _,
    max_le (by norm_num)
      (by
        have hsum : 0 ≤ ∑ i, (v i : ℝ) :=
          Finset.sum_nonneg fun i _ => (v i).2.1
        linarith)⟩

/-- Insert a distinguished zeroth coordinate. -/
private def consFin {n : ℕ} (p : I × (Fin n → I)) : Fin (n + 1) → I :=
  Fin.cons p.1 p.2

/-- Replace the first free coordinate by the residual holding fraction. -/
private def simplexShear {n : ℕ} (u : Fin (n + 1) → I) :
    Fin (n + 1) → I :=
  consFin
    (reflectIic (remainingIic (fun i => u i.succ)) (u 0),
      fun i => u i.succ)

@[fun_prop]
private theorem measurable_consFin {n : ℕ} :
    Measurable (consFin (n := n)) := by
  change Measurable (fun p : I × (Fin n → I) =>
    Fin.cons (α := fun _ : Fin (n + 1) => I) p.1 p.2)
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => I) 0).symm.measurable

@[fun_prop]
private theorem measurable_remainingIic {n : ℕ} :
    Measurable (remainingIic (n := n)) := by
  unfold remainingIic
  fun_prop

@[fun_prop]
private theorem measurable_simplexShear {n : ℕ} :
    Measurable (simplexShear (n := n)) := by
  unfold simplexShear
  fun_prop

/-- The free simplex volume is invariant when its first coordinate is
exchanged with the residual coordinate. -/
private theorem lintegral_freeSimplex_shear {n : ℕ}
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
private def tailReverseEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.cases 0 (fun i => i.rev.succ)
  invFun := Fin.cases 0 (fun i => i.rev.succ)
  left_inv i := by
    refine Fin.cases rfl (fun j => ?_) i
    simp
  right_inv i := by
    refine Fin.cases rfl (fun j => ?_) i
    simp

private def reverseTail {n : ℕ} (u : Fin (n + 1) → I) :
    Fin (n + 1) → I :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) => I) (tailReverseEquiv n) u

@[fun_prop]
private theorem measurable_reverseTail {n : ℕ} :
    Measurable (reverseTail (n := n)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) => I) (tailReverseEquiv n)).measurable

/-- Coordinate permutations preserve every measurable integral over the free
simplex. -/
private theorem lintegral_freeSimplex_reverseTail {n : ℕ}
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
private def reverseFree {n : ℕ} (u : Fin (n + 1) → I) :
    Fin (n + 1) → I :=
  reverseTail (simplexShear u)

@[fun_prop]
private theorem measurable_reverseFree {n : ℕ} :
    Measurable (reverseFree (n := n)) :=
  measurable_reverseTail.comp measurable_simplexShear

/-- Completed-simplex reversal preserves every measurable integral. -/
private theorem lintegral_freeSimplex_reverseFree {n : ℕ}
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

private theorem reverseFree_zero {n : ℕ} (u : Fin (n + 1) → I)
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

private theorem reverseFree_succ {n : ℕ} (u : Fin (n + 1) → I)
    (i : Fin n) :
    reverseFree u i.succ = u i.rev.succ := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (n + 1) => I)
    (tailReverseEquiv n) (simplexShear u) i.rev.succ
  simpa [reverseFree, reverseTail, tailReverseEquiv,
    simplexShear, consFin] using h

private theorem sum_reverseFree {n : ℕ} (u : Fin (n + 1) → I)
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
private theorem holdingTimesOfFree_reverseFree {n : ℕ} (T : NNReal)
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
          reverseFree u) := by
  apply Prod.ext
  · exact reverse_alternatingStates (n + 1) x
  · exact (holdingTimesOfFree_reverseFree T u hu).symm

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
              reverseFree u)) := by
      apply setLIntegral_congr_fun
        (Simplex.measurableSet_freeSimplexSet (n + 1))
      intro u hu
      dsimp only
      rw [reverse_assemblePath T x u hu]
    _ = ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          G (Simplex.assemblePath T
            (alternatingStates (n + 1) (iterateFlip (n + 1) x), u)) := by
      exact lintegral_freeSimplex_reverseFree
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
                (T : ℝ) * residual u))) := by
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
        (T : ℝ) * residual u := by
    rw [NNReal.coe_sub hscaled]
    rw [NNReal.coe_sum]
    simp only [residual, NNReal.coe_mul, Simplex.coe_unitNNReal]
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
                (T : ℝ) * residual u)))) := by
    fun_prop
  have hreorder : Set.EqOn
      (fun u =>
        (w x * cubeExpWeight (chainRates x n) T u *
            ∏ i, (chainRates x n i : ℝ≥0∞)) *
          ENNReal.ofReal
            (Real.exp
              (-((stateRate (iterateFlip n x) : ℝ) *
                (T : ℝ) * residual u))))
      (fun u =>
        (w x * ∏ i, (chainRates x n i : ℝ≥0∞)) *
          (cubeExpWeight (chainRates x n) T u *
            ENNReal.ofReal
              (Real.exp
                (-((stateRate (iterateFlip n x) : ℝ) *
                  (T : ℝ) * residual u)))))
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

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
