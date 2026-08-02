/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenBoundary

/-!
# Structurally connected driven paths

The raw marked carrier is convenient for kernel recursion. This module adds
the corresponding subtype in which every complete window path has the states
stored at that boundary as its actual initial and terminal endpoints.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Boundary matching for every complete window path in a reverse-oriented
driven path. -/
def IsBoundaryConsistent :
    {M : ℕ} → Path Ω M → Prop
  | 0, _ => True
  | _ + 1, γ =>
      FullPath.initialState γ.2.1.2 = γ.2.1.1 ∧
      FullPath.terminalState γ.2.1.2 = γ.1 ∧
      IsBoundaryConsistent (γ.2.1.1, γ.2.2)

/-- A driven path whose window boundaries match by construction. -/
abbrev ConnectedPath (Ω : Type u) [MeasurableSpace Ω] (M : ℕ) :=
  {γ : Path Ω M // IsBoundaryConsistent γ}

@[simp]
theorem isBoundaryConsistent_zero (γ : Path Ω 0) :
    IsBoundaryConsistent γ :=
  trivial

@[simp]
theorem isBoundaryConsistent_succ_iff
    {M : ℕ} (γ : Path Ω (M + 1)) :
    IsBoundaryConsistent γ ↔
      FullPath.initialState γ.2.1.2 = γ.2.1.1 ∧
      FullPath.terminalState γ.2.1.2 = γ.1 ∧
      IsBoundaryConsistent (γ.2.1.1, γ.2.2) :=
  Iff.rfl

/-- Add a complete window path to a connected prefix while discharging its two
endpoint equations explicitly. -/
def ConnectedPath.prepend
    {M : ℕ} (past : ConnectedPath Ω M)
    (endpoint : Ω) (window : FullPath Ω)
    (hinitial : FullPath.initialState window = past.1.1)
    (hterminal : FullPath.terminalState window = endpoint) :
    ConnectedPath Ω (M + 1) :=
  ⟨(endpoint, ((past.1.1, window), past.1.2)),
    hinitial, hterminal, past.2⟩

@[simp]
theorem ConnectedPath.prepend_current
    {M : ℕ} (past : ConnectedPath Ω M)
    (endpoint : Ω) (window : FullPath Ω)
    (hinitial : FullPath.initialState window = past.1.1)
    (hterminal : FullPath.terminalState window = endpoint) :
    (past.prepend endpoint window hinitial hterminal).1.1 = endpoint :=
  rfl

@[simp]
theorem ConnectedPath.prepend_window
    {M : ℕ} (past : ConnectedPath Ω M)
    (endpoint : Ω) (window : FullPath Ω)
    (hinitial : FullPath.initialState window = past.1.1)
    (hterminal : FullPath.terminalState window = endpoint) :
    (past.prepend endpoint window hinitial hterminal).1.2.1.2 = window :=
  rfl

section MeasureSupport

variable [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]

/-- Boundary consistency is a measurable property of the raw marked carrier. -/
theorem measurableSet_isBoundaryConsistent :
    ∀ M : ℕ, MeasurableSet {γ : Path Ω M | IsBoundaryConsistent γ}
  | 0 => by simp
  | M + 1 => by
      have hinitial : Measurable
          (fun γ : Path Ω (M + 1) =>
            FullPath.initialState γ.2.1.2) := by
        fun_prop
      have hstoredInitial : Measurable
          (fun γ : Path Ω (M + 1) => γ.2.1.1) := by
        fun_prop
      have hterminal : Measurable
          (fun γ : Path Ω (M + 1) =>
            FullPath.terminalState γ.2.1.2) := by
        fun_prop
      have hcurrent : Measurable
          (fun γ : Path Ω (M + 1) => γ.1) := by
        fun_prop
      have hpast : Measurable
          (fun γ : Path Ω (M + 1) => (γ.2.1.1, γ.2.2)) := by
        fun_prop
      exact
        (hinitial.eq hstoredInitial).setOf.inter
          ((hterminal.eq hcurrent).setOf.inter
            ((measurableSet_isBoundaryConsistent M).preimage hpast))

/-- The recursively constructed forward law is concentrated on paths whose
stored complete-window endpoints match every recorded protocol boundary. -/
theorem forwardDrivenLaw_ae_isBoundaryConsistent :
    ∀ {M : ℕ} (initial : Measure Ω)
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal),
      ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
        IsBoundaryConsistent γ
  | 0, initial, generator, duration => by
      simp [IsBoundaryConsistent]
  | M + 1, initial, generator, duration => by
      have hpast :
          ∀ᵐ past ∂Marked.reversedForwardPathMeasure initial
              (fun i : Fin M =>
                (generator i.castSucc).forwardWindowKernel
                  (duration i.castSucc)),
            IsBoundaryConsistent past := by
        simpa [forwardDrivenLaw] using
          (forwardDrivenLaw_ae_isBoundaryConsistent initial
            (fun i : Fin M => generator i.castSucc)
            (fun i : Fin M => duration i.castSucc))
      simp only [forwardDrivenLaw, Marked.reversedForwardPathMeasure]
      let prepend :=
        Marked.prependEquiv (Ω := Ω) (Λ := FullPath Ω) M
      refine (ae_map_iff (f := prepend)
        prepend.measurable.aemeasurable
        (measurableSet_isBoundaryConsistent (Ω := Ω) (M + 1))).2 ?_
      apply Measure.ae_compProd_of_ae_ae
      · exact
          (measurableSet_isBoundaryConsistent (Ω := Ω) (M + 1)).preimage
            prepend.measurable
      · filter_upwards [hpast] with past hpast
        change ∀ᵐ window ∂
            (generator (Fin.last M)).forwardWindowKernel
              (duration (Fin.last M)) past.1,
          FullPath.initialState window.2 = past.1 ∧
            FullPath.terminalState window.2 = window.1 ∧
            IsBoundaryConsistent past
        filter_upwards
          [(generator (Fin.last M)).forwardWindowKernel_ae_boundary
            (duration (Fin.last M)) past.1] with window hwindow
        exact ⟨hwindow.1, hwindow.2, hpast⟩

private theorem reverseContinuationKernel_ae_isBoundaryConsistent :
    ∀ {M : ℕ}
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal) (endpoint : Ω),
      ∀ᵐ past ∂Marked.reverseContinuationKernel
          (fun i => (generator i).reverseWindowKernel (duration i)) endpoint,
        IsBoundaryConsistent (endpoint, past)
  | 0, generator, duration, endpoint => by
      simp [Marked.reverseContinuationKernel, IsBoundaryConsistent]
  | M + 1, generator, duration, endpoint => by
      simp only [Marked.reverseContinuationKernel]
      apply Kernel.ae_compProd_of_ae_ae
      · exact
          (measurableSet_isBoundaryConsistent (Ω := Ω) (M + 1)).preimage
            (measurable_const.prodMk measurable_id)
      · filter_upwards
          [(generator (Fin.last M)).reverseWindowKernel_ae_boundary
            (duration (Fin.last M)) endpoint] with window hwindow
        have hpast :=
          reverseContinuationKernel_ae_isBoundaryConsistent
            (fun i : Fin M => generator i.castSucc)
            (fun i : Fin M => duration i.castSucc) window.1
        change ∀ᵐ past ∂Marked.reverseContinuationKernel
            (fun i : Fin M =>
              (generator i.castSucc).reverseWindowKernel
                (duration i.castSucc)) window.1,
          FullPath.initialState window.2 = window.1 ∧
            FullPath.terminalState window.2 = endpoint ∧
            IsBoundaryConsistent (window.1, past)
        filter_upwards [hpast] with past hpast
        exact ⟨hwindow.1, hwindow.2, hpast⟩

/-- The recursively constructed reverse law is concentrated on the same
forward-aligned boundary-consistent carrier. -/
theorem reverseDrivenLaw_ae_isBoundaryConsistent
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseDrivenLaw final generator duration,
      IsBoundaryConsistent γ := by
  unfold reverseDrivenLaw Marked.reversePathMeasure
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_isBoundaryConsistent (Ω := Ω) M
  · filter_upwards [] with endpoint
    exact reverseContinuationKernel_ae_isBoundaryConsistent
      generator duration endpoint

end MeasureSupport

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
