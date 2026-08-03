/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTrajectory

/-!
# Reversal of complete finite-jump paths

Path reversal within a fixed jump-count sector lifts to the full path space
without changing the sector index.  This module packages that lift, its
endpoint exchange laws, and the induced measurable equivalence.  It sits below
the driven-protocol layer so that the stationarity and window-balance modules
can reverse full paths without depending on any marked-kernel machinery.
-/

open MeasureTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Reverse a complete finite-jump path without changing its jump-count
sector. -/
def reverse : FullPath Ω → FullPath Ω
  | ⟨n, γ⟩ => ⟨n, JumpPath.reverse γ⟩

@[fun_prop]
theorem measurable_reverse :
    Measurable (reverse : FullPath Ω → FullPath Ω) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet
    ((fun γ : JumpPath Ω n => Sigma.mk n (JumpPath.reverse γ)) ⁻¹' s)
  exact ((measurable_mk n).comp JumpPath.measurable_reverse) hs

omit [MeasurableSpace Ω] in
@[simp]
theorem reverse_reverse (γ : FullPath Ω) : reverse (reverse γ) = γ := by
  rcases γ with ⟨n, γ⟩
  simp [reverse]

omit [MeasurableSpace Ω] in
@[simp]
theorem initialState_reverse (γ : FullPath Ω) :
    initialState (reverse γ) = terminalState γ := by
  rcases γ with ⟨n, γ⟩
  change γ.1 ((0 : Fin (n + 1)).rev) = γ.1 (Fin.last n)
  rw [Fin.rev_zero]

omit [MeasurableSpace Ω] in
@[simp]
theorem terminalState_reverse (γ : FullPath Ω) :
    terminalState (reverse γ) = initialState γ := by
  rcases γ with ⟨n, γ⟩
  simp [reverse, initialState, terminalState, JumpPath.reverse]

/-- Full-path reversal as a measurable equivalence. -/
noncomputable def reverseEquiv : FullPath Ω ≃ᵐ FullPath Ω where
  toEquiv :=
    { toFun := reverse
      invFun := reverse
      left_inv := fun γ => reverse_reverse γ
      right_inv := fun γ => reverse_reverse γ }
  measurable_toFun := measurable_reverse
  measurable_invFun := measurable_reverse

end FullPath

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
