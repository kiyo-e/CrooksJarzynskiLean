/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatPathLaw
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorBridge

/-!
# Terminal fidelity of path-law concatenation

The transition-kernel semigroup law below is obtained by pushing the
path-level concatenation theorem through the terminal-state observable.
-/

open MeasureTheory ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- **Fidelity anchor.**  Pushing positive-horizon path concatenation through
the terminal state recovers Chapman--Kolmogorov for the transition kernel. -/
theorem transitionKernel_add_from_pathLawFrom_add
    (G : FiniteJumpGenerator Ω) (S T : NNReal)
    (hS : 0 < S) (hT : 0 < T) :
    G.transitionKernel (S + T) =
      G.transitionKernel T ∘ₖ G.transitionKernel S := by
  apply ProbabilityTheory.Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  have hy : MeasurableSet ({y} : Set Ω) := measurableSet_singleton y
  have hf : Measurable
      (fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2) :=
    FullPath.measurable_concat_prod_of_point x
  rw [G.transitionKernel_apply]
  rw [G.pathLawFrom_add S T hS hT x]
  rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hy]
  rw [Measure.map_apply FullPath.measurable_terminalState hy]
  rw [Measure.map_apply hf
    (FullPath.measurable_terminalState hy)]
  rw [Measure.compProd_apply
    (hf (FullPath.measurable_terminalState hy))]
  rw [G.transitionKernel_apply]
  rw [lintegral_map
    (ProbabilityTheory.Kernel.measurable_coe _ hy)
    FullPath.measurable_terminalState]
  apply lintegral_congr
  intro γ
  rw [continuationPathKernel_apply]
  change G.pathLawFrom T (FullPath.terminalState γ)
      {δ | FullPath.terminalState (FullPath.concat γ δ) = y} =
    (G.pathLawFrom T (FullPath.terminalState γ)).map
      FullPath.terminalState {y}
  rw [Measure.map_apply FullPath.measurable_terminalState hy]
  apply measure_congr
  filter_upwards [G.pathLawFrom_ae_initialState T
    (FullPath.terminalState γ)] with δ hδ
  apply propext
  change (FullPath.terminalState (FullPath.concat γ δ) = y) ↔
    FullPath.terminalState δ = y
  rw [FullPath.terminalState_concat γ δ hδ.symm]

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
