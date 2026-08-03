/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenBoundary
import CrooksJarzynski.ContinuousTimeJumpDrivenWorkSum

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

/-- A physically valid driven path has matching stored boundaries and a valid
real-time chart in every protocol window. -/
def IsProtocolValid {M : ℕ} (duration : Fin M → NNReal)
    (γ : Path Ω M) : Prop :=
  IsBoundaryConsistent γ ∧
    ∀ i, FullPath.IsValid (duration i) (windowAt γ i)

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

omit [DecidableEq Ω] in
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

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
/-- Simultaneous validity of the stored charts is measurable. -/
theorem measurableSet_windowsValid
    {M : ℕ} (duration : Fin M → NNReal) :
    MeasurableSet {γ : Path Ω M |
      ∀ i, FullPath.IsValid (duration i) (windowAt γ i)} := by
  rw [show {γ : Path Ω M |
      ∀ i, FullPath.IsValid (duration i) (windowAt γ i)} =
      ⋂ i, (fun γ => windowAt (Ω := Ω) (M := M) γ i) ⁻¹'
        {w | FullPath.IsValid (duration i) w} by ext; simp]
  exact MeasurableSet.iInter fun i =>
    (FullPath.measurableSet_isValid (duration i)).preimage
      (measurable_windowAt i)

omit [DecidableEq Ω] in
/-- Protocol validity is a measurable property of the raw marked carrier. -/
theorem measurableSet_isProtocolValid
    {M : ℕ} (duration : Fin M → NNReal) :
    MeasurableSet {γ : Path Ω M | IsProtocolValid duration γ} := by
  unfold IsProtocolValid
  exact (measurableSet_isBoundaryConsistent (Ω := Ω) M).inter
    (measurableSet_windowsValid duration)

private theorem forwardDrivenLaw_ae_windowsValid :
    ∀ {M : ℕ} (initial : Measure Ω)
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal),
      ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
        ∀ i, FullPath.IsValid (duration i) (windowAt γ i)
  | 0, initial, generator, duration => by simp
  | M + 1, initial, generator, duration => by
      have hpast := forwardDrivenLaw_ae_windowsValid initial
        (fun i : Fin M => generator i.castSucc)
        (fun i : Fin M => duration i.castSucc)
      simp only [forwardDrivenLaw, Marked.reversedForwardPathMeasure]
      let prepend := Marked.prependEquiv (Ω := Ω) (Λ := FullPath Ω) M
      have hset := measurableSet_windowsValid (Ω := Ω) duration
      refine (ae_map_iff prepend.measurable.aemeasurable hset).2 ?_
      apply Measure.ae_compProd_of_ae_ae
      · exact hset.preimage prepend.measurable
      · filter_upwards [hpast] with past hpast
        filter_upwards
          [(generator (Fin.last M)).forwardWindowKernel_ae_isValid
            (duration (Fin.last M)) past.1] with window hwindow
        change ∀ i, FullPath.IsValid (duration i)
          (windowAt ((window.1,
            (((past.1, window.2), past.2) :
              Marked.MarkedContinuation Ω (FullPath Ω) (M + 1))) :
                Path Ω (M + 1)) i)
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [windowAt_last]
          exact hwindow
        · rw [windowAt_castSucc]
          exact hpast j

private theorem reverseContinuationKernel_ae_windowsValid :
    ∀ {M : ℕ}
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal) (endpoint : Ω),
      ∀ᵐ past ∂Marked.reverseContinuationKernel
          (fun i => (generator i).reverseWindowKernel (duration i)) endpoint,
        ∀ i, FullPath.IsValid (duration i)
          (windowAt (endpoint, past) i)
  | 0, generator, duration, endpoint => by simp
  | M + 1, generator, duration, endpoint => by
      simp only [Marked.reverseContinuationKernel]
      have hrecord : Measurable
          (fun past : Marked.MarkedContinuation Ω (FullPath Ω) (M + 1) =>
            (endpoint, past)) := by fun_prop
      have hset := (measurableSet_windowsValid (Ω := Ω) duration).preimage hrecord
      apply Kernel.ae_compProd_of_ae_ae
      · exact hset
      · filter_upwards
          [(generator (Fin.last M)).reverseWindowKernel_ae_isValid
            (duration (Fin.last M)) endpoint] with window hwindow
        have hpast := reverseContinuationKernel_ae_windowsValid
          (fun i : Fin M => generator i.castSucc)
          (fun i : Fin M => duration i.castSucc) window.1
        filter_upwards [hpast] with past hpast
        change ∀ i, FullPath.IsValid (duration i)
          (windowAt ((endpoint,
            (((window.1, window.2), past) :
              Marked.MarkedContinuation Ω (FullPath Ω) (M + 1))) :
                Path Ω (M + 1)) i)
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [windowAt_last]
          exact hwindow
        · rw [windowAt_castSucc]
          exact hpast j

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

/-- The forward driven law is concentrated on boundary-consistent paths whose
complete mark in every window is a valid real-time trajectory chart. -/
theorem forwardDrivenLaw_ae_isProtocolValid
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
      IsProtocolValid duration γ :=
  (forwardDrivenLaw_ae_isBoundaryConsistent initial generator duration).and
    (forwardDrivenLaw_ae_windowsValid initial generator duration)

/-- The reverse driven law, after storing each sampled window in
forward-aligned coordinates, has the same all-window physical support. -/
theorem reverseDrivenLaw_ae_isProtocolValid
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseDrivenLaw final generator duration,
      IsProtocolValid duration γ := by
  apply (reverseDrivenLaw_ae_isBoundaryConsistent final generator duration).and
  unfold reverseDrivenLaw Marked.reversePathMeasure
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_windowsValid (Ω := Ω) duration
  · filter_upwards [] with endpoint
    exact reverseContinuationKernel_ae_windowsValid generator duration endpoint

end MeasureSupport

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
