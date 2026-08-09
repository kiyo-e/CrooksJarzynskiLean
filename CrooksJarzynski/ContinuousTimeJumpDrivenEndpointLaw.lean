/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDriven
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorBridge
import CrooksJarzynski.MeasureProtocolMarkedEndpoints

/-!
# Driven endpoint law: erasing complete-path marks recovers the terminal chain

Every driven window stores the complete sampled jump path as its mark.  The
endpoint marginal of one such window kernel is exactly the finite generator's
transition kernel, and erasing all marks from the driven forward law produces
the Markov chain on recordable window endpoints.  The construction is the
specialization of `MeasureProtocol.Marked.map_reversedForwardPathMeasure_eraseMarks`
to the driven instantiation `Λ = FullPath Ω`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Forgetting the complete jump-path mark of a window leaves exactly the
transition kernel of the finite generator. -/
theorem endpointMarginal_forwardWindowKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    Marked.endpointMarginalKernel (G.forwardWindowKernel T) =
      G.transitionKernel T := by
  ext (x : Ω) (s : Set Ω) hs
  simp only [Marked.endpointMarginalKernel]
  rw [Kernel.map_apply (G.forwardWindowKernel T) measurable_fst x]
  rw [G.forwardWindowKernel_apply, G.transitionKernel_apply]
  rw [Measure.map_map measurable_fst
    (by fun_prop : Measurable (fun γ : FullPath Ω =>
      (FullPath.terminalState γ, γ)))]
  rfl

end FiniteJumpGenerator

namespace Driven

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The endpoint law for driven protocols: erasing the complete jump-path
marks from the forward driven law reproduces the endpoint Markov chain built
from the windows' transition kernels. -/
theorem map_forwardDrivenLaw_endpoints
    {M : ℕ} (initial : Measure Ω) [SFinite initial]
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    (forwardDrivenLaw initial generator duration).map Marked.eraseMarks =
      Markov.reversedForwardPathMeasure initial
        (fun i => (generator i).transitionKernel (duration i)) := by
  change (Marked.reversedForwardPathMeasure initial
      (fun i => (generator i).forwardWindowKernel (duration i))).map
        Marked.eraseMarks =
      Markov.reversedForwardPathMeasure initial
        (fun i => (generator i).transitionKernel (duration i))
  rw [Marked.map_reversedForwardPathMeasure_eraseMarks]
  congr 1
  funext i
  exact (FiniteJumpGenerator.endpointMarginal_forwardWindowKernel
    (generator i) (duration i))

end Driven

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski