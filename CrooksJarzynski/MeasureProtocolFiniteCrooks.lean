/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolFinite

/-!
# Finite-horizon Crooks induction on general measurable state spaces

This module supplies the density-transport and one-step extension lemmas used
to iterate the general-state-space Crooks relation over a finite protocol.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Markov

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Density transport lemmas used by finite-horizon induction -/

/-- Reweighting the first marginal before composing with a kernel is the same
as reweighting the composition-product by its first coordinate. -/
theorem compProd_withDensity_fst_general
    {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : ProbabilityTheory.Kernel α β)
    [SFinite μ] [IsSFiniteKernel κ]
    (q : α → ℝ≥0∞) (hq : Measurable q) :
    (μ ⊗ₘ κ).withDensity (fun p => q p.1) = μ.withDensity q ⊗ₘ κ := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  have hqfst : Measurable (fun p : α × β => q p.1) :=
    hq.comp measurable_fst
  rw [Measure.lintegral_compProd (hqfst.indicator hs)]
  rw [lintegral_withDensity_eq_lintegral_mul μ hq
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs)]
  apply lintegral_congr
  intro a
  simp only [Pi.mul_apply]
  have hsection : MeasurableSet (Prod.mk a ⁻¹' s) :=
    measurable_prodMk_left hs
  have hindicator :
      (fun b => s.indicator (fun p => q p.1) (a, b)) =
        (Prod.mk a ⁻¹' s).indicator (fun _ => q a) := by
    funext b
    rfl
  rw [hindicator, lintegral_indicator hsection]
  simp [MeasureTheory.lintegral_const]

/-- Mapping by a measurable equivalence commutes with a density after pulling
that density back along the equivalence. -/
theorem map_withDensity_equiv
    {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (q : β → ℝ≥0∞) (hq : Measurable q) :
    (μ.map e).withDensity q = (μ.withDensity (q ∘ e)).map e := by
  ext s hs
  rw [withDensity_apply _ hs, setLIntegral_map hs hq e.measurable,
    Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs)]
  rfl

/-- Extend a Crooks relation for a reverse-oriented path prefix by one Markov
step. -/
theorem extendReversedPrefix_crooks
    {A : Type*} [MeasurableSpace A]
    (prefixForward : Measure (Ω × A))
    (current next : Measure Ω)
    (past : ProbabilityTheory.Kernel Ω A)
    (forward reverse : ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure prefixForward]
    [IsProbabilityMeasure current] [IsProbabilityMeasure next]
    [IsMarkovKernel past] [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (prefixWork : Ω × A → ℝ≥0∞) (stepWork : Ω → ℝ≥0∞)
    (prefixFactor stepFactor : ℝ≥0∞)
    (hprefixWork : Measurable prefixWork)
    (hstepWork : Measurable stepWork)
    (hprefix : CrooksRelation prefixForward (current ⊗ₘ past)
      prefixWork prefixFactor)
    (hreweight : current.withDensity stepWork = stepFactor • next)
    (hbalance : next ⊗ₘ forward = (next ⊗ₘ reverse).map Prod.swap) :
    CrooksRelation
      ((prefixForward ⊗ₘ
        forward.comap (fun p : Ω × A => p.1) measurable_fst).map
          MeasurableEquiv.prodComm)
      (next ⊗ₘ (reverse ⊗ₖ
        ProbabilityTheory.Kernel.prodMkLeft Ω past))
      (fun z => prefixWork z.2 * stepWork z.2.1)
      (prefixFactor * stepFactor) := by
  haveI : IsMarkovKernel
      (forward.comap (fun p : Ω × A => p.1) measurable_fst) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.comap _ measurable_fst
  unfold CrooksRelation at hprefix ⊢
  have hOutput : Measurable
      (fun z : Ω × (Ω × A) => prefixWork z.2 * stepWork z.2.1) :=
    (hprefixWork.comp measurable_snd).mul
      (hstepWork.comp (measurable_fst.comp measurable_snd))
  rw [map_withDensity_equiv
    (prefixForward ⊗ₘ
      forward.comap (fun p : Ω × A => p.1) measurable_fst)
    MeasurableEquiv.prodComm _ hOutput]
  change
    (((prefixForward ⊗ₘ
        forward.comap (fun p : Ω × A => p.1) measurable_fst).withDensity
      (fun p => prefixWork p.1 * stepWork p.1.1)).map
        MeasurableEquiv.prodComm) =
      (prefixFactor * stepFactor) •
        (next ⊗ₘ (reverse ⊗ₖ
          ProbabilityTheory.Kernel.prodMkLeft Ω past))
  rw [show (fun p : (Ω × A) × Ω => prefixWork p.1 * stepWork p.1.1) =
      (fun p => prefixWork p.1) * (fun p => stepWork p.1.1) by rfl,
    withDensity_mul _
      (hprefixWork.comp measurable_fst)
      (hstepWork.comp (measurable_fst.comp measurable_fst)),
    compProd_withDensity_fst_general prefixForward
      (forward.comap (fun p : Ω × A => p.1) measurable_fst)
      prefixWork hprefixWork,
    hprefix, Measure.compProd_smul_left, withDensity_smul_measure,
    compProd_withDensity_fst_general (current ⊗ₘ past)
      (forward.comap (fun p : Ω × A => p.1) measurable_fst)
      (fun p => stepWork p.1) (hstepWork.comp measurable_fst),
    compProd_withDensity_fst_general current past stepWork hstepWork,
    hreweight, Measure.compProd_smul_left, Measure.compProd_smul_left,
    Measure.map_smul, Measure.map_smul,
    liftLocalBalance_past next past forward reverse hbalance]
  simp [smul_smul]

end Markov
end MeasureProtocol
end CrooksJarzynski
