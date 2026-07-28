/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocol
import CrooksJarzynski.Probability

/-!
# Finite-horizon path measures on general measurable state spaces

This module builds finite path measures from Mathlib Markov kernels without a
finite-state assumption. Paths are represented by the existing recursive
`Trajectory` type, but are stored in reverse chronological order. This choice
makes adjoining a new endpoint and comparing forward and reverse transitions
compatible with `Measure.compProd`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Markov

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

@[reducible]
private noncomputable def continuationMeasurableSpace
    (Ω : Type u) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (Continuation Ω n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 =>
      letI : MeasurableSpace (Continuation Ω n) :=
        continuationMeasurableSpace Ω n
      inferInstanceAs (MeasurableSpace (Ω × Continuation Ω n))

noncomputable instance (priority := 100) instMeasurableSpaceContinuation (n : ℕ) :
    MeasurableSpace (Continuation Ω n) :=
  continuationMeasurableSpace Ω n

/-- Swap an existing reverse-oriented path prefix with a newly sampled endpoint. -/
noncomputable def prependEquiv (n : ℕ) :
    (Trajectory Ω n × Ω) ≃ᵐ Trajectory Ω (n + 1) where
  toEquiv := Equiv.prodComm _ _
  measurable_toFun := measurable_swap
  measurable_invFun := measurable_swap

/-- Lift a state kernel to a kernel on a reverse-oriented path prefix by reading
its current endpoint. -/
def endpointKernel (K : ProbabilityTheory.Kernel Ω Ω) (n : ℕ) :
    ProbabilityTheory.Kernel (Trajectory Ω n) Ω :=
  K.comap (fun γ : Trajectory Ω n => γ.1) measurable_fst

instance instIsMarkovKernelEndpointKernel
    (K : ProbabilityTheory.Kernel Ω Ω) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (endpointKernel K n) := by
  unfold endpointKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _ measurable_fst

/-- Given an endpoint, generate the earlier states in reverse chronological
order with kernels indexed in forward chronological order. -/
noncomputable def reverseContinuationKernel :
    {n : ℕ} → (Fin n → ProbabilityTheory.Kernel Ω Ω) →
      ProbabilityTheory.Kernel Ω (Continuation Ω n)
  | 0, _ =>
      ProbabilityTheory.Kernel.deterministic (fun _ => PUnit.unit) measurable_const
  | n + 1, K =>
      K (Fin.last n) ⊗ₖ
        ProbabilityTheory.Kernel.prodMkLeft Ω
          (reverseContinuationKernel (fun i => K i.castSucc))

noncomputable instance instIsMarkovKernelReverseContinuationKernel
    {n : ℕ} (K : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [hK : ∀ i, IsMarkovKernel (K i)] :
    IsMarkovKernel (reverseContinuationKernel K) := by
  induction n with
  | zero =>
      simp only [reverseContinuationKernel]
      infer_instance
  | succ n ih =>
      simp only [reverseContinuationKernel]
      letI : ∀ i : Fin n, IsMarkovKernel ((fun j => K j.castSucc) i) :=
        fun i => hK i.castSucc
      haveI : IsMarkovKernel
          (reverseContinuationKernel (fun i => K i.castSucc)) :=
        ih (fun i => K i.castSucc)
      letI : IsMarkovKernel (K (Fin.last n)) := hK (Fin.last n)
      haveI : IsMarkovKernel
          (ProbabilityTheory.Kernel.prodMkLeft Ω
            (reverseContinuationKernel (fun i => K i.castSucc))) := by
        unfold ProbabilityTheory.Kernel.prodMkLeft
        exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _ measurable_snd
      infer_instance

/-- The reverse-experiment path measure, written in reverse chronological order
`(xₙ, xₙ₋₁, …, x₀)`. -/
noncomputable def reversePathMeasure
    {n : ℕ} (final : Measure Ω)
    (reverse : Fin n → ProbabilityTheory.Kernel Ω Ω) :
    Measure (Trajectory Ω n) :=
  final ⊗ₘ reverseContinuationKernel reverse

noncomputable instance instIsProbabilityMeasureReversePathMeasure
    {n : ℕ} (final : Measure Ω)
    (reverse : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure final] [∀ i, IsMarkovKernel (reverse i)] :
    IsProbabilityMeasure (reversePathMeasure final reverse) := by
  unfold reversePathMeasure
  infer_instance

/-- The forward path measure, represented in reverse chronological order. At
each step the new endpoint is sampled from the last forward kernel and moved to
the front of the recursive trajectory. -/
noncomputable def reversedForwardPathMeasure :
    {n : ℕ} → Measure Ω → (Fin n → ProbabilityTheory.Kernel Ω Ω) →
      Measure (Trajectory Ω n)
  | 0, initial, K => reversePathMeasure initial K
  | n + 1, initial, K =>
      ((reversedForwardPathMeasure initial (fun i => K i.castSucc)) ⊗ₘ
        endpointKernel (K (Fin.last n)) n).map (prependEquiv n)

noncomputable instance instIsProbabilityMeasureReversedForwardPathMeasure
    {n : ℕ} (initial : Measure Ω)
    (forward : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure initial] [hK : ∀ i, IsMarkovKernel (forward i)] :
    IsProbabilityMeasure (reversedForwardPathMeasure initial forward) := by
  induction n with
  | zero =>
      simp only [reversedForwardPathMeasure]
      infer_instance
  | succ n ih =>
      simp only [reversedForwardPathMeasure]
      letI : ∀ i : Fin n,
          IsMarkovKernel ((fun j => forward j.castSucc) i) :=
        fun i => hK i.castSucc
      haveI : IsProbabilityMeasure
          (reversedForwardPathMeasure initial
            (fun i => forward i.castSucc)) :=
        ih (fun i => forward i.castSucc)
      letI : IsMarkovKernel (forward (Fin.last n)) := hK (Fin.last n)
      apply Measure.isProbabilityMeasure_map
      exact (prependEquiv (Ω := Ω) n).measurable.aemeasurable

/-- Product of the work factors along a reverse-oriented finite trajectory. -/
noncomputable def reversedWorkWeight :
    {n : ℕ} → (Fin n → Ω → ℝ≥0∞) → Trajectory Ω n → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, q, γ =>
      reversedWorkWeight (fun i => q i.castSucc) γ.2 *
        q (Fin.last n) γ.2.1

/-- Product of the scalar free-energy factors over a finite protocol. -/
noncomputable def accumulatedFreeEnergyWeight :
    {n : ℕ} → (Fin n → ℝ≥0∞) → ℝ≥0∞
  | 0, _ => 1
  | n + 1, c =>
      accumulatedFreeEnergyWeight (fun i => c i.castSucc) * c (Fin.last n)

/-- Measurability of the accumulated work factor. -/
theorem measurable_reversedWorkWeight
    {n : ℕ} (q : Fin n → Ω → ℝ≥0∞)
    (hq : ∀ i, Measurable (q i)) :
    Measurable (reversedWorkWeight q) := by
  induction n with
  | zero =>
      simpa [reversedWorkWeight] using
        (measurable_const : Measurable (fun _ : Trajectory Ω 0 => (1 : ℝ≥0∞)))
  | succ n ih =>
      change Measurable (fun γ : Ω × Trajectory Ω n =>
        reversedWorkWeight (fun i => q i.castSucc) γ.2 *
          q (Fin.last n) γ.2.1)
      exact
        ((ih (fun i => q i.castSucc) (fun i => hq i.castSucc)).comp measurable_snd).mul
          ((hq (Fin.last n)).comp (measurable_fst.comp measurable_snd))

/-! ## Transporting local detailed balance through a generated past -/

/-- Local detailed balance remains valid after adjoining an arbitrary Markovian
law for the already generated past. -/
theorem liftLocalBalance_past
    {A : Type*} [MeasurableSpace A]
    (μ : Measure Ω)
    (past : ProbabilityTheory.Kernel Ω A)
    (forward reverse : ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ]
    [IsMarkovKernel past] [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (hbalance : μ ⊗ₘ forward = (μ ⊗ₘ reverse).map Prod.swap) :
    ((((μ ⊗ₘ past) ⊗ₘ
        forward.comap (fun p : Ω × A => p.1) measurable_fst).map
          MeasurableEquiv.prodComm) =
      μ ⊗ₘ (reverse ⊗ₖ
        ProbabilityTheory.Kernel.prodMkLeft Ω past)) := by
  haveI : IsMarkovKernel
      (forward.comap (fun p : Ω × A => p.1) measurable_fst) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.comap _ measurable_fst
  haveI : IsMarkovKernel
      (ProbabilityTheory.Kernel.prodMkLeft Ω past) := by
    unfold ProbabilityTheory.Kernel.prodMkLeft
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _ measurable_snd
  haveI : IsProbabilityMeasure
      ((((μ ⊗ₘ past) ⊗ₘ
        forward.comap (fun p : Ω × A => p.1) measurable_fst).map
          MeasurableEquiv.prodComm)) :=
    Measure.isProbabilityMeasure_map
      (MeasurableEquiv.prodComm.measurable.aemeasurable)
  apply Measure.ext_prod₃
  intro s t u hs ht hu
  let fForward : Ω × A → ℝ≥0∞ := fun p => forward p.1 s
  have hfForward : Measurable fForward :=
    (forward.measurable_coe hs).comp measurable_fst
  let g : Ω × Ω → ℝ≥0∞ := fun p => past p.1 u
  have hg : Measurable g :=
    (past.measurable_coe hu).comp measurable_fst
  let gswap : Ω × Ω → ℝ≥0∞ := fun p => past p.2 u
  have hgswap : Measurable gswap :=
    (past.measurable_coe hu).comp measurable_snd
  have hpre :
      MeasurableEquiv.prodComm ⁻¹' (s ×ˢ t ×ˢ u) =
        (t ×ˢ u) ×ˢ s := by
    ext p
    simp
  have hpreLocal :
      Prod.swap ⁻¹' (t ×ˢ s) = s ×ˢ t := by
    ext p
    simp
  calc
    ((((μ ⊗ₘ past) ⊗ₘ
        forward.comap (fun p : Ω × A => p.1) measurable_fst).map
          MeasurableEquiv.prodComm) (s ×ˢ t ×ˢ u))
        = ((μ ⊗ₘ past) ⊗ₘ
            forward.comap (fun p : Ω × A => p.1) measurable_fst)
              ((t ×ˢ u) ×ˢ s) := by
          rw [Measure.map_apply MeasurableEquiv.prodComm.measurable
            (hs.prod (ht.prod hu)), hpre]
    _ = ∫⁻ p in t ×ˢ u, forward p.1 s ∂(μ ⊗ₘ past) := by
          rw [Measure.compProd_apply_prod (ht.prod hu) hs]
          rfl
    _ = ∫⁻ p in t ×ˢ s, past p.1 u ∂(μ ⊗ₘ forward) := by
          rw [Measure.setLIntegral_compProd hfForward ht hu,
            Measure.setLIntegral_compProd hg ht hs]
          apply setLIntegral_congr_fun ht
          intro x hx
          simp [fForward, g, setLIntegral_const, mul_comm]
    _ = ∫⁻ p in t ×ˢ s, past p.1 u
          ∂((μ ⊗ₘ reverse).map Prod.swap) := by
          rw [← hbalance]
    _ = ∫⁻ p in s ×ˢ t, past p.2 u ∂(μ ⊗ₘ reverse) := by
          rw [setLIntegral_map (ht.prod hs) hg measurable_swap, hpreLocal]
          rfl
    _ = (μ ⊗ₘ (reverse ⊗ₖ
          ProbabilityTheory.Kernel.prodMkLeft Ω past))
          (s ×ˢ t ×ˢ u) := by
          rw [Measure.setLIntegral_compProd hgswap hs ht,
            Measure.compProd_apply_prod hs (ht.prod hu)]
          apply setLIntegral_congr_fun hs
          intro y hy
          rw [ProbabilityTheory.Kernel.compProd_apply_prod ht hu]
          rfl

end Markov
end MeasureProtocol
end CrooksJarzynski
