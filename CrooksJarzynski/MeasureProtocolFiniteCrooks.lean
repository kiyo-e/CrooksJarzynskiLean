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
        forward.comap (fun p : Ω × A => p.1)
          (measurable_fst : Measurable (fun p : Ω × A => p.1))).map
          (MeasurableEquiv.prodComm :
            ((Ω × A) × Ω) ≃ᵐ Ω × (Ω × A)))
      (next ⊗ₘ (reverse ⊗ₖ
        ProbabilityTheory.Kernel.prodMkLeft Ω past))
      (fun z => prefixWork z.2 * stepWork z.2.1)
      (prefixFactor * stepFactor) := by
  haveI : IsMarkovKernel
      (forward.comap (fun p : Ω × A => p.1)
        (measurable_fst : Measurable (fun p : Ω × A => p.1))) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      (measurable_fst : Measurable (fun p : Ω × A => p.1))
  unfold CrooksRelation at hprefix ⊢
  have hOutput : Measurable
      (fun z : Ω × (Ω × A) => prefixWork z.2 * stepWork z.2.1) :=
    (hprefixWork.comp
      (measurable_snd : Measurable (fun z : Ω × (Ω × A) => z.2))).mul
      (hstepWork.comp
        ((measurable_fst : Measurable (fun p : Ω × A => p.1)).comp
          (measurable_snd : Measurable (fun z : Ω × (Ω × A) => z.2))))
  have hPrefixInput : Measurable
      (fun p : (Ω × A) × Ω => prefixWork p.1) :=
    hprefixWork.comp
      (measurable_fst : Measurable (fun p : (Ω × A) × Ω => p.1))
  have hStepInput : Measurable
      (fun p : (Ω × A) × Ω => stepWork p.1.1) :=
    hstepWork.comp
      ((measurable_fst : Measurable (fun p : Ω × A => p.1)).comp
        (measurable_fst : Measurable (fun p : (Ω × A) × Ω => p.1)))
  rw [map_withDensity_equiv
    (prefixForward ⊗ₘ
      forward.comap (fun p : Ω × A => p.1)
        (measurable_fst : Measurable (fun p : Ω × A => p.1)))
    (MeasurableEquiv.prodComm : ((Ω × A) × Ω) ≃ᵐ Ω × (Ω × A))
    _ hOutput]
  change
    (((prefixForward ⊗ₘ
        forward.comap (fun p : Ω × A => p.1)
          (measurable_fst : Measurable (fun p : Ω × A => p.1))).withDensity
      ((fun p : (Ω × A) × Ω => prefixWork p.1) *
        (fun p : (Ω × A) × Ω => stepWork p.1.1))).map
        (MeasurableEquiv.prodComm : ((Ω × A) × Ω) ≃ᵐ Ω × (Ω × A))) =
      (prefixFactor * stepFactor) •
        (next ⊗ₘ (reverse ⊗ₖ
          ProbabilityTheory.Kernel.prodMkLeft Ω past))
  rw [withDensity_mul _ hPrefixInput hStepInput,
    compProd_withDensity_fst_general prefixForward
      (forward.comap (fun p : Ω × A => p.1)
        (measurable_fst : Measurable (fun p : Ω × A => p.1)))
      prefixWork hprefixWork,
    hprefix, Measure.compProd_smul_left, withDensity_smul_measure,
    compProd_withDensity_fst_general (current ⊗ₘ past)
      (forward.comap (fun p : Ω × A => p.1)
        (measurable_fst : Measurable (fun p : Ω × A => p.1)))
      (fun p => stepWork p.1)
      (hstepWork.comp
        (measurable_fst : Measurable (fun p : Ω × A => p.1))),
    compProd_withDensity_fst_general current past stepWork hstepWork,
    hreweight, Measure.compProd_smul_left, Measure.compProd_smul_left,
    Measure.map_smul, Measure.map_smul,
    liftLocalBalance_past next past forward reverse hbalance]
  simp [smul_smul]

/-- Finite-horizon Crooks relation on an arbitrary measurable state space.
The forward and reverse path measures are represented in reverse chronological
order. Each step follows from equilibrium reweighting and a measure-level local
detailed-balance identity. -/
theorem multiStep_crooks
    {n : ℕ}
    (equilibrium : Fin (n + 1) → Measure Ω)
    (forward reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    (workWeight : Fin n → Ω → ℝ≥0∞)
    (freeEnergyWeight : Fin n → ℝ≥0∞)
    [hEquilibrium : ∀ i, IsProbabilityMeasure (equilibrium i)]
    [hForward : ∀ i, IsMarkovKernel (forward i)]
    [hReverse : ∀ i, IsMarkovKernel (reverse i)]
    (hwork : ∀ i, Measurable (workWeight i))
    (hreweight : ∀ i,
      (equilibrium i.castSucc).withDensity (workWeight i) =
        freeEnergyWeight i • equilibrium i.succ)
    (hbalance : ∀ i,
      equilibrium i.succ ⊗ₘ forward i =
        (equilibrium i.succ ⊗ₘ reverse i).map Prod.swap) :
    CrooksRelation
      (reversedForwardPathMeasure (equilibrium 0) forward)
      (reversePathMeasure (equilibrium (Fin.last n)) reverse)
      (reversedWorkWeight workWeight)
      (accumulatedFreeEnergyWeight freeEnergyWeight) := by
  induction n with
  | zero =>
      have hfr : forward = reverse := Subsingleton.elim _ _
      subst reverse
      simp [CrooksRelation, reversedForwardPathMeasure,
        reversedWorkWeight, accumulatedFreeEnergyWeight]
  | succ n ih =>
      let equilibriumPrefix : Fin (n + 1) → Measure Ω :=
        fun i => equilibrium i.castSucc
      let forwardPrefix : Fin n → ProbabilityTheory.Kernel Ω Ω :=
        fun i => forward i.castSucc
      let reversePrefix : Fin n → ProbabilityTheory.Kernel Ω Ω :=
        fun i => reverse i.castSucc
      let workPrefix : Fin n → Ω → ℝ≥0∞ :=
        fun i => workWeight i.castSucc
      let factorPrefix : Fin n → ℝ≥0∞ :=
        fun i => freeEnergyWeight i.castSucc
      letI : ∀ i, IsProbabilityMeasure (equilibriumPrefix i) :=
        fun i => hEquilibrium i.castSucc
      letI : ∀ i, IsMarkovKernel (forwardPrefix i) :=
        fun i => hForward i.castSucc
      letI : ∀ i, IsMarkovKernel (reversePrefix i) :=
        fun i => hReverse i.castSucc
      have hprefix :
          CrooksRelation
            (reversedForwardPathMeasure (equilibriumPrefix 0) forwardPrefix)
            (reversePathMeasure (equilibriumPrefix (Fin.last n)) reversePrefix)
            (reversedWorkWeight workPrefix)
            (accumulatedFreeEnergyWeight factorPrefix) := by
        apply ih
        · intro i
          exact hwork i.castSucc
        · intro i
          dsimp [equilibriumPrefix, workPrefix, factorPrefix]
          simpa using hreweight i.castSucc
        · intro i
          dsimp [equilibriumPrefix, forwardPrefix, reversePrefix]
          simpa using hbalance i.castSucc
      letI : IsMarkovKernel (forward (Fin.last n)) := hForward (Fin.last n)
      letI : IsMarkovKernel (reverse (Fin.last n)) := hReverse (Fin.last n)
      have hext := extendReversedPrefix_crooks
        (prefixForward :=
          reversedForwardPathMeasure (equilibriumPrefix 0) forwardPrefix)
        (current := equilibriumPrefix (Fin.last n))
        (next := equilibrium ((Fin.last n).succ))
        (past := reverseContinuationKernel reversePrefix)
        (forward := forward (Fin.last n))
        (reverse := reverse (Fin.last n))
        (prefixWork := reversedWorkWeight workPrefix)
        (stepWork := workWeight (Fin.last n))
        (prefixFactor := accumulatedFreeEnergyWeight factorPrefix)
        (stepFactor := freeEnergyWeight (Fin.last n))
        (measurable_reversedWorkWeight workPrefix
          (fun i => hwork i.castSucc))
        (hwork (Fin.last n))
        (by simpa [reversePathMeasure] using hprefix)
        (by
          dsimp [equilibriumPrefix]
          exact hreweight (Fin.last n))
        (hbalance (Fin.last n))
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        ext
        rfl
      rw [hlast] at hext
      simpa [equilibriumPrefix, forwardPrefix, reversePrefix, workPrefix,
        factorPrefix, reversedForwardPathMeasure, endpointKernel,
        reversePathMeasure, reverseContinuationKernel, reversedWorkWeight,
        accumulatedFreeEnergyWeight] using hext

/-- The finite-horizon Jarzynski equality on an arbitrary measurable state
space. -/
theorem multiStep_jarzynski
    {n : ℕ}
    (equilibrium : Fin (n + 1) → Measure Ω)
    (forward reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    (workWeight : Fin n → Ω → ℝ≥0∞)
    (freeEnergyWeight : Fin n → ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (equilibrium i)]
    [∀ i, IsMarkovKernel (forward i)]
    [∀ i, IsMarkovKernel (reverse i)]
    (hwork : ∀ i, Measurable (workWeight i))
    (hreweight : ∀ i,
      (equilibrium i.castSucc).withDensity (workWeight i) =
        freeEnergyWeight i • equilibrium i.succ)
    (hbalance : ∀ i,
      equilibrium i.succ ⊗ₘ forward i =
        (equilibrium i.succ ⊗ₘ reverse i).map Prod.swap) :
    ∫⁻ γ, reversedWorkWeight workWeight γ
      ∂reversedForwardPathMeasure (equilibrium 0) forward =
        accumulatedFreeEnergyWeight freeEnergyWeight := by
  exact jarzynski_lintegral _ _ _ _
    (multiStep_crooks equilibrium forward reverse workWeight freeEnergyWeight
      hwork hreweight hbalance)

end Markov
end MeasureProtocol
end CrooksJarzynski
