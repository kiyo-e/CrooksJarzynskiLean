/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolPaths

/-!
# Finite path measures with transition marks

This module extends the finite-horizon Markov construction with a measurable
mark attached to every transition.  The reverse-oriented carrier keeps the
current endpoint at the front and stores pairs consisting of the preceding
state and the transition mark.  The construction is independent of the
continuous-time interpretation; the driven jump protocol instantiates the mark
with a complete fixed-horizon jump path.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Marked

universe u v

variable {Ω : Type u} {Λ : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Earlier transition marks in reverse chronological order. -/
abbrev MarkedContinuation (Ω : Type u) (Λ : Type v)
    [MeasurableSpace Ω] [MeasurableSpace Λ] (n : ℕ) :=
  Continuation (Ω × Λ) n

/-- A reverse-oriented marked path.  Its first component is the current
endpoint; every continuation entry stores the preceding state and the mark of
the transition from that state. -/
abbrev MarkedPath (Ω : Type u) (Λ : Type v)
    [MeasurableSpace Ω] [MeasurableSpace Λ] (n : ℕ) :=
  Ω × MarkedContinuation Ω Λ n

/-- Move a newly sampled endpoint and mark to the front of a reverse-oriented
marked prefix. -/
noncomputable def prependEquiv (n : ℕ) :
    (MarkedPath Ω Λ n × (Ω × Λ)) ≃ᵐ MarkedPath Ω Λ (n + 1) where
  toEquiv :=
    { toFun := fun p => (p.2.1, ((p.1.1, p.2.2), p.1.2))
      invFun := fun p => ((p.2.1.1, p.2.2), (p.1, p.2.1.2))
      left_inv := by
        intro p
        rcases p with ⟨⟨x, past⟩, y, mark⟩
        rfl
      right_inv := by
        intro p
        rcases p with ⟨y, ⟨x, mark⟩, past⟩
        rfl }
  measurable_toFun := by
    show Measurable (fun p : MarkedPath Ω Λ n × (Ω × Λ) =>
      (p.2.1, ((p.1.1, p.2.2), p.1.2)))
    fun_prop
  measurable_invFun := by
    show Measurable (fun p : MarkedPath Ω Λ (n + 1) =>
      ((p.2.1.1, p.2.2), (p.1, p.2.1.2)))
    fun_prop

/-- Swap the two endpoint coordinates of a marked transition while leaving the
already aligned mark unchanged. -/
noncomputable def swapEndpointsEquiv :
    (Ω × (Ω × Λ)) ≃ᵐ Ω × (Ω × Λ) where
  toEquiv :=
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun p => (p.2.1, (p.1, p.2.2))
      left_inv := by intro p; rcases p with ⟨x, y, mark⟩; rfl
      right_inv := by intro p; rcases p with ⟨x, y, mark⟩; rfl }
  measurable_toFun := by
    show Measurable (fun p : Ω × (Ω × Λ) => (p.2.1, (p.1, p.2.2)))
    fun_prop
  measurable_invFun := by
    show Measurable (fun p : Ω × (Ω × Λ) => (p.2.1, (p.1, p.2.2)))
    fun_prop

/-- Read the current endpoint of a marked prefix before applying a marked
transition kernel. -/
noncomputable def endpointKernel
    (K : ProbabilityTheory.Kernel Ω (Ω × Λ)) (n : ℕ) :
    ProbabilityTheory.Kernel (MarkedPath Ω Λ n) (Ω × Λ) :=
  K.comap (fun γ : MarkedPath Ω Λ n => γ.1)
    (measurable_fst : Measurable (fun γ : MarkedPath Ω Λ n => γ.1))

instance instIsMarkovKernelEndpointKernel
    (K : ProbabilityTheory.Kernel Ω (Ω × Λ)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (endpointKernel K n) := by
  unfold endpointKernel
  infer_instance

/-- Given the final endpoint, generate preceding states and aligned marks in
reverse chronological order. -/
noncomputable def reverseContinuationKernel :
    {n : ℕ} → (Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ)) →
      ProbabilityTheory.Kernel Ω (MarkedContinuation Ω Λ n)
  | 0, _ =>
      ProbabilityTheory.Kernel.deterministic
        (fun _ => (PUnit.unit : MarkedContinuation Ω Λ 0)) measurable_const
  | n + 1, K =>
      K (Fin.last n) ⊗ₖ
        ProbabilityTheory.Kernel.prodMkLeft Ω
          (ProbabilityTheory.Kernel.prodMkRight Λ
            (reverseContinuationKernel (fun i => K i.castSucc)))

noncomputable instance instIsMarkovKernelReverseContinuationKernel
    {n : ℕ} (K : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [hK : ∀ i, IsMarkovKernel (K i)] :
    IsMarkovKernel (reverseContinuationKernel K) := by
  induction n with
  | zero =>
      simp only [reverseContinuationKernel]
      infer_instance
  | succ n ih =>
      letI : ∀ i : Fin n, IsMarkovKernel ((fun j => K j.castSucc) i) :=
        fun i => hK i.castSucc
      haveI : IsMarkovKernel
          (reverseContinuationKernel (fun i => K i.castSucc)) :=
        ih (fun i => K i.castSucc)
      letI : IsMarkovKernel (K (Fin.last n)) := hK (Fin.last n)
      change IsMarkovKernel
        (K (Fin.last n) ⊗ₖ
          ProbabilityTheory.Kernel.prodMkLeft Ω
            (ProbabilityTheory.Kernel.prodMkRight Λ
              (reverseContinuationKernel (fun i => K i.castSucc))))
      infer_instance

/-- The reverse-experiment marked path law in aligned reverse chronological
coordinates. -/
noncomputable def reversePathMeasure
    {n : ℕ} (final : Measure Ω)
    (reverse : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ)) :
    Measure (MarkedPath Ω Λ n) :=
  final ⊗ₘ reverseContinuationKernel reverse

noncomputable instance instIsProbabilityMeasureReversePathMeasure
    {n : ℕ} (final : Measure Ω)
    (reverse : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [IsProbabilityMeasure final] [∀ i, IsMarkovKernel (reverse i)] :
    IsProbabilityMeasure (reversePathMeasure final reverse) := by
  unfold reversePathMeasure
  infer_instance

/-- The forward marked path law, represented in reverse chronological order. -/
noncomputable def reversedForwardPathMeasure :
    {n : ℕ} → Measure Ω →
      (Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ)) →
      Measure (MarkedPath Ω Λ n)
  | 0, initial, K => reversePathMeasure initial K
  | n + 1, initial, K =>
      ((reversedForwardPathMeasure initial (fun i => K i.castSucc)) ⊗ₘ
        endpointKernel (K (Fin.last n)) n).map (prependEquiv n)

/-- A measurable cylinder added at the final marked transition has the
expected product mass when the final kernel mass is constant on the earlier
cylinder. -/
theorem reversedForwardPathMeasure_succ_apply_image_prod
    {n : ℕ} (initial : Measure Ω)
    (K : Fin (n + 1) → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [SFinite (reversedForwardPathMeasure initial (fun i => K i.castSucc))]
    [IsSFiniteKernel (endpointKernel (K (Fin.last n)) n)]
    {s : Set (MarkedPath Ω Λ n)} (hs : MeasurableSet s)
    {t : Set (Ω × Λ)} (ht : MeasurableSet t) (c : ℝ≥0∞)
    (hc : ∀ p ∈ s, endpointKernel (K (Fin.last n)) n p t = c) :
    reversedForwardPathMeasure initial K
        ((prependEquiv n) '' (s ×ˢ t)) =
      c * reversedForwardPathMeasure initial (fun i => K i.castSucc) s := by
  let e := prependEquiv (Ω := Ω) (Λ := Λ) n
  have himage : MeasurableSet (e '' (s ×ˢ t)) :=
    e.measurableEmbedding.measurableSet_image.mpr (hs.prod ht)
  simp only [reversedForwardPathMeasure]
  rw [Measure.map_apply e.measurable himage]
  rw [show e ⁻¹' (e '' (s ×ˢ t)) = s ×ˢ t from
    e.toEquiv.preimage_image (s ×ˢ t)]
  rw [Measure.compProd_apply_prod hs ht,
    setLIntegral_congr_fun hs hc, setLIntegral_const]

noncomputable instance instIsProbabilityMeasureReversedForwardPathMeasure
    {n : ℕ} (initial : Measure Ω)
    (forward : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
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
      exact (prependEquiv (Ω := Ω) (Λ := Λ) n).measurable.aemeasurable

/-- Product of endpoint work factors along a reverse-oriented marked path.
The factor for a transition is evaluated at the endpoint reached by that
transition. -/
noncomputable def reversedEndpointWorkWeight :
    {n : ℕ} → (Fin n → Ω → ℝ≥0∞) → MarkedPath Ω Λ n → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, q, γ =>
      reversedEndpointWorkWeight (fun i => q i.castSucc)
          (γ.2.1.1, γ.2.2) *
        q (Fin.last n) γ.1

/-- Recursive sum of real endpoint observables on a reverse-oriented marked
path. -/
noncomputable def reversedEndpointSum :
    {n : ℕ} → (Fin n → Ω → ℝ) → MarkedPath Ω Λ n → ℝ
  | 0, _, _ => 0
  | n + 1, work, γ =>
      reversedEndpointSum (fun i => work i.castSucc)
          (γ.2.1.1, γ.2.2) +
        work (Fin.last n) γ.1

/-- Measurability of the accumulated endpoint work factor. -/
theorem measurable_reversedEndpointWorkWeight
    {n : ℕ} (q : Fin n → Ω → ℝ≥0∞)
    (hq : ∀ i, Measurable (q i)) :
    Measurable (reversedEndpointWorkWeight (Λ := Λ) q) := by
  induction n with
  | zero =>
      simp [reversedEndpointWorkWeight]
  | succ n ih =>
      change Measurable (fun γ : Ω × ((Ω × Λ) × MarkedContinuation Ω Λ n) =>
        reversedEndpointWorkWeight (fun i => q i.castSucc)
            (γ.2.1.1, γ.2.2) *
          q (Fin.last n) γ.1)
      have hpast : Measurable
          (fun γ : Ω × ((Ω × Λ) × MarkedContinuation Ω Λ n) =>
            (γ.2.1.1, γ.2.2)) := by fun_prop
      exact
        ((ih (fun i => q i.castSucc) (fun i => hq i.castSucc)).comp hpast).mul
          ((hq (Fin.last n)).comp measurable_fst)

/-- Measurability of the accumulated real endpoint observable. -/
theorem measurable_reversedEndpointSum
    {n : ℕ} (work : Fin n → Ω → ℝ)
    (hwork : ∀ i, Measurable (work i)) :
    Measurable (reversedEndpointSum (Λ := Λ) work) := by
  induction n with
  | zero =>
      simp [reversedEndpointSum]
  | succ n ih =>
      change Measurable (fun γ : Ω × ((Ω × Λ) × MarkedContinuation Ω Λ n) =>
        reversedEndpointSum (fun i => work i.castSucc)
            (γ.2.1.1, γ.2.2) +
          work (Fin.last n) γ.1)
      have hpast : Measurable
          (fun γ : Ω × ((Ω × Λ) × MarkedContinuation Ω Λ n) =>
            (γ.2.1.1, γ.2.2)) := by fun_prop
      exact
        ((ih (fun i => work i.castSucc)
          (fun i => hwork i.castSucc)).comp hpast).add
          ((hwork (Fin.last n)).comp measurable_fst)

/-- Endpoint exponential factors multiply to the exponential of the recursive
endpoint sum. -/
theorem reversedEndpointWorkWeight_eq_exp_sum
    {n : ℕ} (β : ℝ) (work : Fin n → Ω → ℝ)
    (γ : MarkedPath Ω Λ n) :
    reversedEndpointWorkWeight
        (fun i x => ENNReal.ofReal (Real.exp (-β * work i x))) γ =
      ENNReal.ofReal
        (Real.exp (-β * reversedEndpointSum work γ)) := by
  induction n with
  | zero =>
      simp [reversedEndpointWorkWeight, reversedEndpointSum]
  | succ n ih =>
      change
        reversedEndpointWorkWeight
            (fun i x => ENNReal.ofReal
              (Real.exp (-β * work i.castSucc x)))
            (γ.2.1.1, γ.2.2) *
          ENNReal.ofReal (Real.exp (-β * work (Fin.last n) γ.1)) =
        ENNReal.ofReal (Real.exp (-β *
          (reversedEndpointSum (fun i => work i.castSucc)
              (γ.2.1.1, γ.2.2) +
            work (Fin.last n) γ.1)))
      rw [ih (work := fun i => work i.castSucc)
        (γ := (γ.2.1.1, γ.2.2))]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

end Marked
end MeasureProtocol
end CrooksJarzynski
