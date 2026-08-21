/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatPathLawBridge
import CrooksJarzynski.MeasureProtocolPaths

/-!
# Finite-dimensional distributions of continuous-time jump paths

This module identifies the finite-dimensional marginals of the fixed-initial
continuous-time path law with the chronological finite-path measures generated
by its transition kernels.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Sample a complete continuous-time path at finitely many observation times. -/
noncomputable def sampleAt {n : ℕ} (time : Fin (n + 1) → NNReal) :
    FullPath Ω → Trajectory Ω n :=
  fun γ => Trajectory.ofFn fun i => trajectory γ (time i)

@[fun_prop]
theorem measurable_sampleAt {n : ℕ} (time : Fin (n + 1) → NNReal) :
    Measurable (sampleAt (Ω := Ω) time) := by
  apply Trajectory.measurable_ofFn.comp
  refine measurable_pi_iff.2 ?_
  intro i
  exact measurable_trajectory (time i)

end FullPath

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
