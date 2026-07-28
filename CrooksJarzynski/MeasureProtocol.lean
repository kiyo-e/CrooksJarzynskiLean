/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Probability
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Measure-theoretic Crooks–Jarzynski infrastructure

This module contains the state-space-independent core of the development. A
Crooks relation is expressed as an equality of measures on an arbitrary
measurable trajectory space. Evaluating that equality on the whole space gives
the Jarzynski equality as a Lebesgue integral.

For one Markov step, the module derives the Crooks relation from two
measure-theoretic hypotheses: equilibrium reweighting under the quench and local
detailed balance as an equality of composition-product measures. Both results
hold on arbitrary measurable state spaces.

The finite-horizon layer below uses the existing recursive trajectory type, but
replaces all finite sums and point probabilities by Mathlib measures and Markov
kernels. Reverse-oriented prefixes keep the current endpoint first; this makes
one-step extension and time reversal compatible with `Measure.compProd`.

The module also adapts an ordinary time-inhomogeneous family of Mathlib Markov
kernels `K t : ProbabilityTheory.Kernel Ω Ω` to the history-dependent kernels
expected by Mathlib's Ionescu–Tulcea construction. Thus `trajectoryMeasure μ₀ K`
is the law of the full trajectory on `ℕ → Ω` for an arbitrary measurable state
space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski

universe u v w

namespace MeasureProtocol

variable {Γ : Type u} [MeasurableSpace Γ]

/-- A division-free Crooks relation on an arbitrary measurable trajectory
space. `workWeight` is the exponential work factor and `freeEnergyWeight` is
the corresponding equilibrium factor. -/
def CrooksRelation (forward reverse : Measure Γ)
    (workWeight : Γ → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞) : Prop :=
  forward.withDensity workWeight = freeEnergyWeight • reverse

/-- The measure-theoretic Jarzynski equality follows by evaluating the Crooks
measure identity on the whole trajectory space. -/
theorem jarzynski_lintegral
    (forward reverse : Measure Γ) (workWeight : Γ → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞) [IsProbabilityMeasure reverse]
    (h : CrooksRelation forward reverse workWeight freeEnergyWeight) :
    ∫⁻ γ, workWeight γ ∂forward = freeEnergyWeight := by
  have h_univ := congrArg (fun μ : Measure Γ => μ Set.univ) h
  simpa [CrooksRelation, withDensity_apply] using h_univ

/-- The physical exponential form of `jarzynski_lintegral`. -/
theorem jarzynski_exponential
    (forward reverse : Measure Γ) (β ΔF : ℝ) (work : Γ → ℝ)
    [IsProbabilityMeasure reverse]
    (h : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work γ)))
      (ENNReal.ofReal (Real.exp (-β * ΔF)))) :
    ∫⁻ γ, ENNReal.ofReal (Real.exp (-β * work γ)) ∂forward =
      ENNReal.ofReal (Real.exp (-β * ΔF)) :=
  jarzynski_lintegral forward reverse _ _ h

namespace Markov

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Reweighting the first marginal before composing with a kernel is the same
as reweighting the resulting one-step path measure by the first coordinate. -/
theorem compProd_withDensity_fst
    (μ : Measure Ω) (κ : ProbabilityTheory.Kernel Ω Ω)
    [SFinite μ] [IsSFiniteKernel κ]
    (q : Ω → ℝ≥0∞) (hq : Measurable q) :
    (μ ⊗ₘ κ).withDensity (fun p => q p.1) = μ.withDensity q ⊗ₘ κ := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  have hqfst : Measurable (fun p : Ω × Ω => q p.1) :=
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

/-- The first-coordinate density lemma with different source and target spaces. -/
theorem compProd_withDensity_fst_general
    {α : Type v} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
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
    {α : Type v} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (q : β → ℝ≥0∞) (hq : Measurable q) :
    (μ.map e).withDensity q = (μ.withDensity (q ∘ e)).map e := by
  ext s hs
  rw [withDensity_apply _ hs, setLIntegral_map hs hq e.measurable,
    Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs)]
  rfl

/-- A one-step Crooks relation on an arbitrary measurable state space. The
first hypothesis is the Gibbs reweighting identity for the quench. The second
is local detailed balance, stated without point masses as equality between the
forward equilibrium step measure and the swapped reverse equilibrium step
measure. -/
theorem oneStep_crooks
    (initial final : Measure Ω)
    (forward reverse : ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure initial] [IsProbabilityMeasure final]
    [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (workWeight : Ω → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞)
    (hwork : Measurable workWeight)
    (hreweight : initial.withDensity workWeight = freeEnergyWeight • final)
    (hbalance :
      final ⊗ₘ forward = (final ⊗ₘ reverse).map Prod.swap) :
    CrooksRelation (initial ⊗ₘ forward)
      ((final ⊗ₘ reverse).map Prod.swap)
      (fun p => workWeight p.1) freeEnergyWeight := by
  unfold CrooksRelation
  rw [compProd_withDensity_fst initial forward workWeight hwork, hreweight,
    Measure.compProd_smul_left, hbalance]

/-- The one-step Jarzynski equality on an arbitrary measurable state space. -/
theorem oneStep_jarzynski
    (initial final : Measure Ω)
    (forward reverse : ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure initial] [IsProbabilityMeasure final]
    [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (workWeight : Ω → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞)
    (hwork : Measurable workWeight)
    (hreweight : initial.withDensity workWeight = freeEnergyWeight • final)
    (hbalance :
      final ⊗ₘ forward = (final ⊗ₘ reverse).map Prod.swap) :
    ∫⁻ p, workWeight p.1 ∂(initial ⊗ₘ forward) = freeEnergyWeight := by
  letI : IsProbabilityMeasure ((final ⊗ₘ reverse).map Prod.swap) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  exact jarzynski_lintegral _ _ _ _
    (oneStep_crooks initial final forward reverse workWeight freeEnergyWeight
      hwork hreweight hbalance)

/-! ## Finite-horizon path measures -/

@[reducible]
private noncomputable def continuationMeasurableSpace
    (Ω : Type u) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (Continuation Ω n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 =>
      letI : MeasurableSpace (Continuation Ω n) :=
        continuationMeasurableSpace Ω n
      inferInstanceAs (MeasurableSpace (Ω × Continuation Ω n))

noncomputable instance instMeasurableSpaceContinuation (n : ℕ) :
    MeasurableSpace (Continuation Ω n) :=
  continuationMeasurableSpace Ω n

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

/-- The forward path measure, also written in reverse chronological order. At
each step the new endpoint is sampled from the last forward kernel and moved to
the front of the recursive trajectory. -/
noncomputable def reversedForwardPathMeasure :
    {n : ℕ} → Measure Ω → (Fin n → ProbabilityTheory.Kernel Ω Ω) →
      Measure (Trajectory Ω n)
  | 0, initial, K => reversePathMeasure initial K
  | n + 1, initial, K =>
      ((reversedForwardPathMeasure initial (fun i => K i.castSucc)) ⊗ₘ
        (K (Fin.last n)).comap Prod.fst measurable_fst).map Prod.swap

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
      apply Measure.isProbabilityMeasure_map
      exact measurable_swap.aemeasurable

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

/-- The last state in a history indexed by `Finset.Iic t`. -/
def historyLast (t : ℕ) (x : (i : Finset.Iic t) → Ω) : Ω :=
  x ⟨t, Finset.mem_Iic.mpr le_rfl⟩

@[fun_prop]
theorem measurable_historyLast (t : ℕ) :
    Measurable (historyLast (Ω := Ω) t) :=
  measurable_pi_apply _

/-- Regard an ordinary Markov kernel as a history-dependent kernel by reading
only the most recent state. This is the adapter required by Ionescu–Tulcea. -/
def historyKernel (K : ℕ → ProbabilityTheory.Kernel Ω Ω) (t : ℕ) :
    ProbabilityTheory.Kernel ((i : Finset.Iic t) → Ω) Ω :=
  (K t).comap (historyLast t) (measurable_historyLast t)

instance instIsMarkovKernelHistoryKernel
    (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] (t : ℕ) :
    IsMarkovKernel (historyKernel K t) := by
  unfold historyKernel
  infer_instance

/-- The Ionescu–Tulcea trajectory law of a time-inhomogeneous Markov chain on
an arbitrary measurable state space. -/
noncomputable def trajectoryMeasure
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] : Measure (ℕ → Ω) :=
  ProbabilityTheory.Kernel.trajMeasure μ₀ (historyKernel K)

noncomputable instance instIsProbabilityMeasureTrajectoryMeasure
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] :
    IsProbabilityMeasure (trajectoryMeasure μ₀ K) := by
  unfold trajectoryMeasure
  infer_instance

/-- Every finite prefix of `trajectoryMeasure` is extended by the prescribed
next-step Markov kernel. -/
theorem trajectoryMeasure_step
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (t : ℕ) :
    (trajectoryMeasure μ₀ K).map (Preorder.frestrictLe t) ⊗ₘ historyKernel K t =
      (trajectoryMeasure μ₀ K).map
        (fun x => (Preorder.frestrictLe t x, x (t + 1))) := by
  exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end Markov

end MeasureProtocol

end CrooksJarzynski