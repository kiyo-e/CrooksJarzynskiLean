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

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
