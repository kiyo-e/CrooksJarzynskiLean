/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcat
import CrooksJarzynski.ContinuousTimeJumpDrivenConnectedPath

/-!
# Concatenation of driven continuous-time jump windows

The reverse-oriented driven carrier stores its latest marked transition at the
front.  This module reads the marks with `windowAt`, which restores
chronological order, and glues every complete window path into one global
real-time chart.
-/

open MeasureTheory
open scoped BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Concatenate every window mark of a driven path, in chronological order,
into one global real-time complete path. The `M = 0` protocol contributes the
jump-free path resting at the recorded state. -/
def concatenateWindows : {M : ℕ} → Path Ω M → FullPath Ω
  | 0, γ => FullPath.rest γ.1
  | _ + 1, γ =>
      FullPath.concat (concatenateWindows (γ.2.1.1, γ.2.2)) γ.2.1.2

/-- The global chart's total holding time is the sum of the holding times of
the chronologically ordered window marks. -/
theorem totalHoldingTime_concatenateWindows :
    ∀ {M : ℕ} (γ : Path Ω M),
      FullPath.totalHoldingTime (concatenateWindows γ) =
        ∑ i, FullPath.totalHoldingTime (windowAt γ i)
  | 0, γ => by
      simp [concatenateWindows]
  | M + 1, γ => by
      rw [concatenateWindows, FullPath.totalHoldingTime_concat,
        totalHoldingTime_concatenateWindows (γ.2.1.1, γ.2.2),
        Fin.sum_univ_castSucc]
      simp

/-- Valid window charts concatenate into a chart for the summed horizon when
every complete holding time fits its window duration. The latter bounds are
required because `IsValid` controls only the last jump time, not the residual
terminal holding interval, which becomes part of a later jump time after
concatenation. -/
theorem isValid_concatenateWindows :
    ∀ {M : ℕ} (duration : Fin M → NNReal) (γ : Path Ω M),
      (∀ i, FullPath.IsValid (duration i) (windowAt γ i)) →
      (∀ i, FullPath.totalHoldingTime (windowAt γ i) ≤ duration i) →
      FullPath.IsValid (∑ i, duration i) (concatenateWindows γ)
  | 0, duration, γ, _, _ => by
      change JumpPath.IsValid 0 (fun _ => γ.1, fun _ => 0)
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      rw [show Fin.last 0 = (0 : Fin 1) from rfl, JumpPath.jumpTimes_zero]
      exact le_rfl
  | M + 1, duration, γ, hvalid, htotal => by
      have hpast := isValid_concatenateWindows
        (fun i : Fin M => duration i.castSucc) (γ.2.1.1, γ.2.2)
        (fun i => by simpa using hvalid i.castSucc)
        (fun i => by simpa using htotal i.castSucc)
      have hlast : FullPath.IsValid (duration (Fin.last M)) γ.2.1.2 := by
        simpa using hvalid (Fin.last M)
      have hpastTotal :
          FullPath.totalHoldingTime (concatenateWindows (γ.2.1.1, γ.2.2)) ≤
            ∑ i : Fin M, duration i.castSucc := by
        rw [totalHoldingTime_concatenateWindows]
        exact Finset.sum_le_sum fun i _ => by
          simpa using htotal i.castSucc
      have hlastTotal :
          FullPath.totalHoldingTime γ.2.1.2 ≤ duration (Fin.last M) := by
        simpa using htotal (Fin.last M)
      rw [Fin.sum_univ_castSucc]
      exact FullPath.isValid_concat hpast hlast hpastTotal hlastTotal

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
