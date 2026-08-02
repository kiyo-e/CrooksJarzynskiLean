/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolMarked
import CrooksJarzynski.MeasureProtocolFiniteCrooks

/-!
# Crooks induction for marked transition paths

This module transports a local detailed-balance identity for a transition
kernel carrying a measurable mark through an already generated marked past.
The result is the measure-theoretic step needed to iterate Crooks' relation
when the work increment is evaluated after a transition.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MeasureTheory
namespace Measure

/-- Two finite measures on a right-associated fourfold product that agree on
measurable rectangles are equal. -/
lemma ext_prod₄
    {α β γ δ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
    {μ ν : Measure (α × β × γ × δ)} [IsFiniteMeasure μ]
    (h : ∀ {s : Set α} {t : Set β} {u : Set γ} {v : Set δ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u →
        MeasurableSet v →
      μ (s ×ˢ t ×ˢ u ×ˢ v) = ν (s ×ˢ t ×ˢ u ×ˢ v)) :
    μ = ν := by
  ext s hs
  have h_univ : μ Set.univ = ν Set.univ := by
    simp_rw [← Set.univ_prod_univ]
    exact h .univ .univ .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  let C₃ := Set.image2 (· ×ˢ ·)
    {u : Set γ | MeasurableSet u} {v : Set δ | MeasurableSet v}
  let C₂ := Set.image2 (· ×ˢ ·)
    {t : Set β | MeasurableSet t} C₃
  let C := Set.image2 (· ×ˢ ·)
    {s : Set α | MeasurableSet s} C₂
  refine MeasurableSpace.induction_on_inter (s := C) ?_ ?_ (by simp) ?_ ?_ ?_ s hs
  · refine (generateFrom_eq_prod
      (C := {s : Set α | MeasurableSet s}) (D := C₂) (by simp) ?_
      isCountablySpanning_measurableSet ?_).symm
    · refine generateFrom_eq_prod
        (C := {t : Set β | MeasurableSet t}) (D := C₃) (by simp)
        generateFrom_prod isCountablySpanning_measurableSet ?_
      exact isCountablySpanning_measurableSet.prod
        isCountablySpanning_measurableSet
    · exact isCountablySpanning_measurableSet.prod
        (isCountablySpanning_measurableSet.prod
          isCountablySpanning_measurableSet)
  · exact MeasurableSpace.isPiSystem_measurableSet.prod
      (MeasurableSpace.isPiSystem_measurableSet.prod
        (MeasurableSpace.isPiSystem_measurableSet.prod
          MeasurableSpace.isPiSystem_measurableSet))
  · rintro - ⟨s, hs, -, ⟨t, ht, -, ⟨u, hu, v, hv, rfl⟩, rfl⟩, rfl⟩
    exact h hs ht hu hv
  · intro t ht hcompl
    simp_rw [measure_compl ht (measure_ne_top _ _), hcompl, h_univ]
  · intro f hdisj hf heq
    simp_rw [measure_iUnion hdisj hf, heq]

end Measure
end MeasureTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Marked

universe u v w

variable {Ω : Type u} {Λ : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Reassociate a marked path extension into the right-associated fourfold
product used by the rectangle extensionality theorem. -/
noncomputable def flattenMarkedPastEquiv
    {A : Type w} [MeasurableSpace A] :
    Ω × ((Ω × Λ) × A) ≃ᵐ Ω × Ω × Λ × A where
  toEquiv :=
    { toFun := fun p => (p.1, (p.2.1.1, (p.2.1.2, p.2.2)))
      invFun := fun p => (p.1, ((p.2.1, p.2.2.1), p.2.2.2))
      left_inv := by intro p; rcases p with ⟨y, ⟨x, mark⟩, past⟩; rfl
      right_inv := by intro p; rcases p with ⟨y, x, mark, past⟩; rfl }
  measurable_toFun := by
    show Measurable (fun p : Ω × ((Ω × Λ) × A) =>
      (p.1, (p.2.1.1, (p.2.1.2, p.2.2))))
    fun_prop
  measurable_invFun := by
    show Measurable (fun p : Ω × Ω × Λ × A =>
      (p.1, ((p.2.1, p.2.2.1), p.2.2.2)))
    fun_prop

/-- Put a newly sampled endpoint and transition mark in front of an arbitrary
already generated past. -/
noncomputable def prependPastEquiv
    {A : Type w} [MeasurableSpace A] :
    ((Ω × A) × (Ω × Λ)) ≃ᵐ Ω × ((Ω × Λ) × A) where
  toEquiv :=
    { toFun := fun p => (p.2.1, ((p.1.1, p.2.2), p.1.2))
      invFun := fun p => ((p.2.1.1, p.2.2), (p.1, p.2.1.2))
      left_inv := by intro p; rcases p with ⟨⟨x, past⟩, y, mark⟩; rfl
      right_inv := by intro p; rcases p with ⟨y, ⟨x, mark⟩, past⟩; rfl }
  measurable_toFun := by
    show Measurable (fun p : (Ω × A) × (Ω × Λ) =>
      (p.2.1, ((p.1.1, p.2.2), p.1.2)))
    fun_prop
  measurable_invFun := by
    show Measurable (fun p : Ω × ((Ω × Λ) × A) =>
      ((p.2.1.1, p.2.2), (p.1, p.2.1.2)))
    fun_prop

/-- A marked local detailed-balance identity remains valid after adjoining an
arbitrary Markovian law for the already generated past. -/
theorem liftLocalBalance_past
    {A : Type w} [MeasurableSpace A]
    (μ : Measure Ω)
    (past : ProbabilityTheory.Kernel Ω A)
    (forward reverse : ProbabilityTheory.Kernel Ω (Ω × Λ))
    [IsProbabilityMeasure μ]
    [IsMarkovKernel past] [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (hbalance :
      μ ⊗ₘ forward =
        (μ ⊗ₘ reverse).map (swapEndpointsEquiv (Ω := Ω) (Λ := Λ))) :
    ((μ ⊗ₘ past) ⊗ₘ
        forward.comap (fun p : Ω × A => p.1)
          (measurable_fst : Measurable (fun p : Ω × A => p.1))).map
          (prependPastEquiv (Ω := Ω) (Λ := Λ) (A := A)) =
      μ ⊗ₘ (reverse ⊗ₖ
        ProbabilityTheory.Kernel.prodMkLeft Ω
          (ProbabilityTheory.Kernel.prodMkRight Λ past)) := by
  let forwardPast : ProbabilityTheory.Kernel (Ω × A) (Ω × Λ) :=
    forward.comap (fun p : Ω × A => p.1)
      (measurable_fst : Measurable (fun p : Ω × A => p.1))
  let reversePast : ProbabilityTheory.Kernel Ω ((Ω × Λ) × A) :=
    reverse ⊗ₖ
      ProbabilityTheory.Kernel.prodMkLeft Ω
        (ProbabilityTheory.Kernel.prodMkRight Λ past)
  let source : Measure ((Ω × A) × (Ω × Λ)) :=
    (μ ⊗ₘ past) ⊗ₘ forwardPast
  let prepend := prependPastEquiv (Ω := Ω) (Λ := Λ) (A := A)
  change source.map prepend = μ ⊗ₘ reversePast
  letI : IsMarkovKernel forwardPast := by
    dsimp [forwardPast]
    infer_instance
  letI : IsMarkovKernel reversePast := by
    dsimp [reversePast]
    infer_instance
  letI : IsProbabilityMeasure (μ ⊗ₘ past) := by infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure (source.map prepend) :=
    Measure.isProbabilityMeasure_map prepend.measurable.aemeasurable
  let flatten := flattenMarkedPastEquiv (Ω := Ω) (Λ := Λ) (A := A)
  apply flatten.map_measurableEquiv_injective
  letI : IsProbabilityMeasure ((source.map prepend).map flatten) :=
    Measure.isProbabilityMeasure_map flatten.measurable.aemeasurable
  apply Measure.ext_prod₄
  intro s t v u hs ht hv hu
  let fForward : Ω × A → ℝ≥0∞ := fun p => forward p.1 (s ×ˢ v)
  have hfForward : Measurable fForward :=
    (forward.measurable_coe (hs.prod hv)).comp
      (measurable_fst : Measurable (fun p : Ω × A => p.1))
  let g : Ω × (Ω × Λ) → ℝ≥0∞ := fun p => past p.1 u
  have hg : Measurable g :=
    (past.measurable_coe hu).comp
      (measurable_fst : Measurable (fun p : Ω × (Ω × Λ) => p.1))
  have hpre :
      prepend ⁻¹' (flatten ⁻¹' (s ×ˢ t ×ˢ v ×ˢ u)) =
        (t ×ˢ u) ×ˢ (s ×ˢ v) := by
    ext p
    simp [prepend, flatten, flattenMarkedPastEquiv, prependPastEquiv,
      and_assoc, and_left_comm, and_comm]
  have hpreLocal :
      (swapEndpointsEquiv (Ω := Ω) (Λ := Λ)) ⁻¹'
          (t ×ˢ s ×ˢ v) =
        s ×ˢ t ×ˢ v := by
    ext p
    simp [swapEndpointsEquiv, and_left_comm]
  have hpreFlatten :
      flatten ⁻¹' (s ×ˢ t ×ˢ v ×ˢ u) =
        s ×ˢ ((t ×ˢ v) ×ˢ u) := by
    ext p
    simp [flatten, flattenMarkedPastEquiv, and_assoc]
  calc
    ((source.map prepend).map flatten) (s ×ˢ t ×ˢ v ×ˢ u) =
        source ((t ×ˢ u) ×ˢ (s ×ˢ v)) := by
      rw [Measure.map_apply flatten.measurable
        (hs.prod (ht.prod (hv.prod hu))),
        Measure.map_apply prepend.measurable
          (flatten.measurable (hs.prod (ht.prod (hv.prod hu)))), hpre]
    _ = ∫⁻ p in t ×ˢ u, forward p.1 (s ×ˢ v) ∂(μ ⊗ₘ past) := by
      change (((μ ⊗ₘ past) ⊗ₘ forwardPast)
        ((t ×ˢ u) ×ˢ (s ×ˢ v))) = _
      rw [Measure.compProd_apply_prod (ht.prod hu) (hs.prod hv)]
      rfl
    _ = ∫⁻ p in t ×ˢ (s ×ˢ v), past p.1 u ∂(μ ⊗ₘ forward) := by
      rw [Measure.setLIntegral_compProd hfForward ht hu,
        Measure.setLIntegral_compProd hg ht (hs.prod hv)]
      apply setLIntegral_congr_fun ht
      intro x hx
      simp [fForward, g, mul_comm]
    _ = ∫⁻ p in t ×ˢ (s ×ˢ v), past p.1 u
          ∂((μ ⊗ₘ reverse).map
            (swapEndpointsEquiv (Ω := Ω) (Λ := Λ))) := by
      rw [← hbalance]
    _ = ∫⁻ p in s ×ˢ (t ×ˢ v), past p.2.1 u ∂(μ ⊗ₘ reverse) := by
      rw [setLIntegral_map (ht.prod (hs.prod hv)) hg
        (swapEndpointsEquiv (Ω := Ω) (Λ := Λ)).measurable,
        hpreLocal]
      rfl
    _ = ((μ ⊗ₘ reversePast).map flatten)
          (s ×ˢ t ×ˢ v ×ˢ u) := by
      rw [Measure.map_apply flatten.measurable
        (hs.prod (ht.prod (hv.prod hu))), hpreFlatten,
        Measure.compProd_apply_prod hs ((ht.prod hv).prod hu),
        Measure.setLIntegral_compProd hg hs (ht.prod hv)]
      apply setLIntegral_congr_fun hs
      intro y hy
      change (∫⁻ p in t ×ˢ v, past p.1 u ∂reverse y) =
        reversePast y ((t ×ˢ v) ×ˢ u)
      dsimp [reversePast]
      rw [ProbabilityTheory.Kernel.compProd_apply_prod (ht.prod hv) hu]
      rfl

end Marked
end MeasureProtocol
end CrooksJarzynski
