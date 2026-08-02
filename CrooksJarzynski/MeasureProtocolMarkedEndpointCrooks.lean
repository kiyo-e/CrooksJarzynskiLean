/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolMarkedCrooks

/-!
# Endpoint-work Crooks extension for marked paths

This module extends a Crooks relation for an already generated marked prefix by
one marked transition.  The new work factor is evaluated at the endpoint reached
by the transition, so local detailed balance is applied before the endpoint
Gibbs reweighting.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Marked

universe u v w

variable {Ω : Type u} {Λ : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Extend a reverse-oriented marked prefix by one transition and then apply a
work factor at the newly reached endpoint. -/
theorem extendEndpoint_crooks
    {A : Type w} [MeasurableSpace A]
    (prefixForward : Measure (Ω × A))
    (current next : Measure Ω)
    (past : ProbabilityTheory.Kernel Ω A)
    (forward reverse : ProbabilityTheory.Kernel Ω (Ω × Λ))
    [IsProbabilityMeasure prefixForward]
    [IsProbabilityMeasure current] [IsProbabilityMeasure next]
    [IsMarkovKernel past] [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (prefixWork : Ω × A → ℝ≥0∞) (stepWork : Ω → ℝ≥0∞)
    (prefixFactor stepFactor : ℝ≥0∞)
    (hprefixWork : Measurable prefixWork)
    (hstepWork : Measurable stepWork)
    (hprefix : CrooksRelation prefixForward (current ⊗ₘ past)
      prefixWork prefixFactor)
    (hbalance :
      current ⊗ₘ forward =
        (current ⊗ₘ reverse).map
          (swapEndpointsEquiv (Ω := Ω) (Λ := Λ)))
    (hreweight : current.withDensity stepWork = stepFactor • next) :
    CrooksRelation
      (((prefixForward ⊗ₘ
          forward.comap (fun p : Ω × A => p.1)
            (measurable_fst : Measurable (fun p : Ω × A => p.1))).map
        (prependPastEquiv (Ω := Ω) (Λ := Λ) (A := A))))
      (next ⊗ₘ
        (reverse ⊗ₖ
          ProbabilityTheory.Kernel.prodMkLeft Ω
            (ProbabilityTheory.Kernel.prodMkRight Λ past)))
      (fun z : Ω × ((Ω × Λ) × A) =>
        prefixWork (z.2.1.1, z.2.2) * stepWork z.1)
      (prefixFactor * stepFactor) := by
  unfold CrooksRelation at hprefix ⊢
  let forwardPast : ProbabilityTheory.Kernel (Ω × A) (Ω × Λ) :=
    forward.comap (fun p : Ω × A => p.1)
      (measurable_fst : Measurable (fun p : Ω × A => p.1))
  let reversePast : ProbabilityTheory.Kernel Ω ((Ω × Λ) × A) :=
    reverse ⊗ₖ
      ProbabilityTheory.Kernel.prodMkLeft Ω
        (ProbabilityTheory.Kernel.prodMkRight Λ past)
  let prepend := prependPastEquiv (Ω := Ω) (Λ := Λ) (A := A)
  let outputPrefix : Ω × ((Ω × Λ) × A) → ℝ≥0∞ :=
    fun z => prefixWork (z.2.1.1, z.2.2)
  let outputStep : Ω × ((Ω × Λ) × A) → ℝ≥0∞ :=
    fun z => stepWork z.1
  have hOutputPrefix : Measurable outputPrefix := by
    dsimp [outputPrefix]
    fun_prop
  have hOutputStep : Measurable outputStep := by
    dsimp [outputStep]
    fun_prop
  have hInputPrefix : Measurable
      (fun p : (Ω × A) × (Ω × Λ) => prefixWork p.1) :=
    hprefixWork.comp
      (measurable_fst : Measurable (fun p : (Ω × A) × (Ω × Λ) => p.1))
  rw [withDensity_mul _ hOutputPrefix hOutputStep]
  rw [map_withDensity
    (prefixForward ⊗ₘ forwardPast) prepend outputPrefix
    prepend.measurable hOutputPrefix]
  change
    ((((prefixForward ⊗ₘ forwardPast).withDensity
        (fun p : (Ω × A) × (Ω × Λ) => prefixWork p.1)).map prepend).withDensity
      outputStep =
        (prefixFactor * stepFactor) • (next ⊗ₘ reversePast))
  rw [Markov.compProd_withDensity_fst prefixForward forwardPast
      prefixWork hprefixWork,
    hprefix, Measure.compProd_smul_left, Measure.map_smul,
    liftLocalBalance_past current past forward reverse hbalance,
    withDensity_smul_measure,
    Markov.compProd_withDensity_fst current reversePast stepWork hstepWork,
    hreweight, Measure.compProd_smul_left]
  simp [smul_smul]

end Marked
end MeasureProtocol
end CrooksJarzynski
