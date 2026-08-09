/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolMarked
import CrooksJarzynski.MeasureProtocolPaths

/-!
# Endpoint marginal of the marked transition kernels

The marked path construction folds a transition mark into every step.  This
module erases those marks, collapsing each marked kernel `Ω → Ω × Λ` to its
marginal `Ω → Ω` by applying the measurable function `Prod.fst`.  The main
result is a commutation theorem: erasing marks after building the reverseoriented forward marked path law is the same as building the corresponding
unmarked law from the endpoint marginals of the marked kernels.  This gives
the driven leap from complete-path marks to the terminal-state Markov chain
that would be obtained by keeping only window endpoint states.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Marked

universe u v

variable {Ω : Type u} {Λ : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Forget the transition marks of a marked continuation, keeping only the
preceding endpoint of every step. -/
def eraseMarksContinuation : {n : ℕ} → MarkedContinuation Ω Λ n → Continuation Ω n
  | 0, _ => PUnit.unit
  | _ + 1, ((x, _), rest) => (x, eraseMarksContinuation rest)

/-- Forget the transition marks of a reverse-oriented marked path, keeping the
state sequence. -/
def eraseMarks {n : ℕ} (γ : MarkedPath Ω Λ n) : Trajectory Ω n :=
  (γ.1, eraseMarksContinuation γ.2)

@[fun_prop]
theorem measurable_eraseMarksContinuation {n : ℕ} :
    Measurable (@eraseMarksContinuation Ω Λ _ _ n) := by
  induction n with
  | zero =>
      change Measurable (fun _ : MarkedContinuation Ω Λ 0 => PUnit.unit)
      fun_prop
  | succ n ih =>
      change Measurable (fun γ : (Ω × Λ) × MarkedContinuation Ω Λ n =>
        (γ.1.1, eraseMarksContinuation γ.2))
      exact
        ((measurable_fst.comp measurable_fst :
          Measurable (fun γ : (Ω × Λ) × MarkedContinuation Ω Λ n => γ.1.1)).prodMk
          (ih.comp measurable_snd))
/-- Erasing the marks of a reverse-oriented marked path is measurable. -/
@[fun_prop]
theorem measurable_eraseMarks {n : ℕ} :
    Measurable (@eraseMarks Ω Λ _ _ n) := by
  change Measurable (fun γ : Ω × MarkedContinuation Ω Λ n =>
    (γ.1, eraseMarksContinuation γ.2))
  exact (measurable_fst : Measurable (fun γ : Ω × MarkedContinuation Ω Λ n => γ.1)).prodMk
    (measurable_eraseMarksContinuation.comp measurable_snd)

/-- Erasing marks preserves the current (front) endpoint of a reverse-oriented
path. -/
@[simp]
theorem eraseMarks_fst {n : ℕ} (γ : MarkedPath Ω Λ n) :
    (eraseMarks γ).1 = γ.1 := by
  rfl

/-- The endpoint marginal of a marked transition kernel: forget the mark and
keep the next state. -/
noncomputable def endpointMarginalKernel
    (K : ProbabilityTheory.Kernel Ω (Ω × Λ)) :
    ProbabilityTheory.Kernel Ω Ω :=
  K.map Prod.fst

instance instIsMarkovKernelEndpointMarginalKernel
    (K : ProbabilityTheory.Kernel Ω (Ω × Λ)) [IsMarkovKernel K] :
    IsMarkovKernel (endpointMarginalKernel K) := by
  unfold endpointMarginalKernel
  exact Kernel.IsMarkovKernel.map K measurable_fst


/-- Erasing marks commutes with the prepend step that adjoins a new endpoint
and mark: erasing the extended marked path is the same as erasing the old
prefix and keeping the new state. This is definitional per constructor case. -/
theorem eraseMarks_comp_prependEquiv (n : ℕ) :
    eraseMarks ∘ prependEquiv (Ω := Ω) (Λ := Λ) n =
      Markov.prependEquiv (Ω := Ω) n ∘
        (Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω)) := by
  funext p
  rcases p with ⟨γ, x, mark⟩
  simp [eraseMarks, prependEquiv, Markov.prependEquiv, eraseMarksContinuation,
    Prod.map]
  change (x, (γ.1, eraseMarksContinuation γ.2)) =
    (x, (γ.1, eraseMarksContinuation γ.2))
  rfl


/-- Erasing marks and marginalizing the transition mark commute with the
composition-product construction: pushing `eraseMarks` through the first
coordinate and `Prod.fst` through the second gives the composition-product of
the erased prefix law with the endpoint-marginal kernel. -/
private lemma erase_prod_comm
    {n : ℕ} (μ : Measure (MarkedPath Ω Λ n)) [SFinite μ]
    (K : ProbabilityTheory.Kernel Ω (Ω × Λ)) [IsMarkovKernel K] :
    (μ ⊗ₘ Marked.endpointKernel K n).map
        (Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω)) =
      μ.map eraseMarks ⊗ₘ
        Markov.endpointKernel (endpointMarginalKernel K) n := by
  let Mker : ProbabilityTheory.Kernel (Trajectory Ω n) Ω :=
    Markov.endpointKernel (endpointMarginalKernel K) n
  apply Measure.ext
  intro q hq
  calc
    (μ ⊗ₘ Marked.endpointKernel K n).map
        (Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω)) q
        = (μ ⊗ₘ Marked.endpointKernel K n)
            ((Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω)) ⁻¹' q) := by
          rw [Measure.map_apply (measurable_eraseMarks.prodMap measurable_fst) hq]
    _ = ∫⁻ a, (Marked.endpointKernel K n) a
            (Prod.mk a ⁻¹'
              ((Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω)) ⁻¹' q)) ∂μ := by
          rw [Measure.compProd_apply
            ((measurable_eraseMarks.prodMap measurable_fst) hq)]
    _ = ∫⁻ a, Mker (eraseMarks a) (Prod.mk (eraseMarks a) ⁻¹' q) ∂μ := by
          apply lintegral_congr
          intro a
          have hslice : Prod.mk a ⁻¹'
                ((Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω)) ⁻¹' q) =
              Prod.fst ⁻¹' (Prod.mk (eraseMarks a) ⁻¹' q) := by
            ext w
            simp [Prod.map]
          simp only [Marked.endpointKernel, Kernel.comap_apply]
          rw [hslice]
          rw [← Measure.map_apply measurable_fst (measurable_prodMk_left hq)]
          congr 1
          unfold Mker endpointMarginalKernel Markov.endpointKernel
          rw [Kernel.comap_apply (K.map Prod.fst) measurable_fst (eraseMarks a)]
          rw [eraseMarks_fst, ← Kernel.map_apply K measurable_fst a.1]
    _ = ∫⁻ b, Mker b (Prod.mk b ⁻¹' q) ∂(μ.map eraseMarks) := by
          exact (lintegral_map
            (Kernel.measurable_kernel_prodMk_left hq) measurable_eraseMarks).symm
    _ = (μ.map eraseMarks ⊗ₘ Mker) q := by
          rw [Measure.compProd_apply hq]


/-- The reversed forward marked path law is σ-finite in the sense of the
`SFinite` typeclass whenever the initial law is and all kernels are s-finite
kernels. -/
noncomputable instance instSFiniteReversedForwardPathMeasure
    {n : ℕ} (initial : Measure Ω) [SFinite initial]
    (K : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [∀ i, IsSFiniteKernel (K i)] :
    SFinite (Marked.reversedForwardPathMeasure initial K) := by
  induction n with
  | zero =>
      simp only [Marked.reversedForwardPathMeasure, Marked.reversePathMeasure,
        Marked.reverseContinuationKernel]
      infer_instance
  | succ n ih =>
      haveI : SFinite (Marked.reversedForwardPathMeasure initial
          (fun i => K i.castSucc)) := ih (fun i => K i.castSucc)
      haveI : IsSFiniteKernel (Marked.endpointKernel (K (Fin.last n)) n) :=
        by unfold Marked.endpointKernel; infer_instance
      haveI : SFinite (Marked.reversedForwardPathMeasure initial
          (fun i => K i.castSucc) ⊗ₘ Marked.endpointKernel (K (Fin.last n)) n) :=
        by infer_instance
      simpa only [Marked.reversedForwardPathMeasure] using
        (inferInstance : SFinite
          ((Marked.reversedForwardPathMeasure initial (fun i => K i.castSucc) ⊗ₘ
            Marked.endpointKernel (K (Fin.last n)) n).map (Marked.prependEquiv n)))

/-! ### Main commutation theorem
Applying `eraseMarks` to the *marked* reversed forward-path measure yields the
*Markov* (mark-erased) reversed forward-path measure driven by the endpoint
marginal kernels. The size-`0` base and the induction step are handled below.-/
theorem map_reversedForwardPathMeasure_eraseMarks
    {n : ℕ} (initial : Measure Ω) [SFinite initial]
    (K : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    [∀ i, IsMarkovKernel (K i)] :
    (Marked.reversedForwardPathMeasure initial K).map eraseMarks =
      Markov.reversedForwardPathMeasure initial
        (fun i => endpointMarginalKernel (K i)) := by
  induction n with
  | zero =>
      calc
        (Marked.reversedForwardPathMeasure initial K).map eraseMarks
            = (Marked.reversePathMeasure initial K).map eraseMarks := by
                rw [Marked.reversedForwardPathMeasure]
        _ = (initial ⊗ₘ Marked.reverseContinuationKernel K).map eraseMarks := by
                rw [Marked.reversePathMeasure]
        _ = Markov.reversePathMeasure initial
            (fun i => endpointMarginalKernel (K i)) := by
                simp only [Marked.reverseContinuationKernel]
                rw [Measure.compProd_deterministic measurable_const]
                have hm : Measurable (fun a : Ω =>
                      ((a, (PUnit.unit : MarkedContinuation Ω Λ 0)) : MarkedPath Ω Λ 0)) := by
                  fun_prop
                rw [Measure.map_map measurable_eraseMarks hm]
                have hgh : (eraseMarks : MarkedPath Ω Λ 0 → Trajectory Ω 0) ∘
                      (fun a : Ω => ((a, (PUnit.unit : MarkedContinuation Ω Λ 0)) : MarkedPath Ω Λ 0))
                    = (fun x : Ω => (x, (PUnit.unit : Continuation Ω 0))) := by
                  funext a
                  rfl
                rw [hgh]
                simp only [Markov.reversePathMeasure]
                simp [Markov.reverseContinuationKernel]
                exact (Measure.compProd_deterministic measurable_const).symm
        _ = Markov.reversedForwardPathMeasure initial
            (fun i => endpointMarginalKernel (K i)) := by
                rw [Markov.reversedForwardPathMeasure]
  | succ n ih =>
      let K' : Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ) := fun i => K i.castSucc
      haveI : SFinite (Marked.reversedForwardPathMeasure initial K') :=
        instSFiniteReversedForwardPathMeasure initial K'
      calc
        (Marked.reversedForwardPathMeasure initial K).map eraseMarks
            = ((Marked.reversedForwardPathMeasure initial K' ⊗ₘ
                  Marked.endpointKernel (K (Fin.last n)) n).map
                  (Marked.prependEquiv n)).map eraseMarks := by
                rw [Marked.reversedForwardPathMeasure]
        _ = (Marked.reversedForwardPathMeasure initial K' ⊗ₘ
                  Marked.endpointKernel (K (Fin.last n)) n).map
                  (eraseMarks ∘ Marked.prependEquiv n) := by
                rw [Measure.map_map measurable_eraseMarks (Marked.prependEquiv n).measurable]
        _ = (Marked.reversedForwardPathMeasure initial K' ⊗ₘ
                  Marked.endpointKernel (K (Fin.last n)) n).map
                  (Markov.prependEquiv n ∘
                    (Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω))) := by
                rw [eraseMarks_comp_prependEquiv]
        _ = ((Marked.reversedForwardPathMeasure initial K' ⊗ₘ
                  Marked.endpointKernel (K (Fin.last n)) n).map
                  (Prod.map eraseMarks (Prod.fst : Ω × Λ → Ω))).map
                  (Markov.prependEquiv n) := by
                rw [Measure.map_map (Markov.prependEquiv n).measurable
                  (measurable_eraseMarks.prodMap measurable_fst)]
        _ = ((Marked.reversedForwardPathMeasure initial K').map eraseMarks ⊗ₘ
                  Markov.endpointKernel (endpointMarginalKernel (K (Fin.last n))) n).map
                  (Markov.prependEquiv n) := by
                rw [erase_prod_comm (Marked.reversedForwardPathMeasure initial K')
                  (K (Fin.last n))]
        _ = (Markov.reversedForwardPathMeasure initial
                  (fun i : Fin n => endpointMarginalKernel (K i.castSucc)) ⊗ₘ
                  Markov.endpointKernel (endpointMarginalKernel (K (Fin.last n))) n).map
                  (Markov.prependEquiv n) := by
                rw [ih K']
        _ = Markov.reversedForwardPathMeasure initial
                  (fun i => endpointMarginalKernel (K i)) := by
                simp only [Markov.reversedForwardPathMeasure]
