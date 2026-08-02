/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenStationary

/-!
# Boundary consistency of driven jump windows

The marked window kernels retain complete fixed-horizon paths. These lemmas
record that their endpoint coordinates agree almost surely with the initial and
terminal states stored by those paths. Thus consecutive windows are connected
by the state passed through the recursive kernel construction.
-/

open MeasureTheory ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- A forward window starts at its kernel input and records its path terminal
state as the next endpoint. -/
theorem forwardWindowKernel_ae_boundary
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ p ∂G.forwardWindowKernel T x,
      FullPath.initialState p.2 = x ∧
        FullPath.terminalState p.2 = p.1 := by
  have hset : MeasurableSet
      {p : Ω × FullPath Ω |
        FullPath.initialState p.2 = x ∧
          FullPath.terminalState p.2 = p.1} := by
    exact
      ((FullPath.measurable_initialState.comp measurable_snd).eq_const x).setOf.inter
        ((FullPath.measurable_terminalState.comp measurable_snd).eq
          measurable_fst).setOf
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T x),
    FullPath.initialState p.2 = x ∧
      FullPath.terminalState p.2 = p.1
  refine (ae_map_iff (f := record) ?_ hset).2 ?_
  · simpa [record] using
      (FullPath.measurable_terminalState.prodMk measurable_id).aemeasurable
  · filter_upwards [G.pathLawFrom_ae_initialState T x] with γ hγ
    exact ⟨hγ, rfl⟩

/-- A reverse-experiment window is stored in forward-aligned coordinates: its
reversed mark starts at the recorded preceding endpoint and ends at the kernel
input. -/
theorem reverseWindowKernel_ae_boundary
    (G : FiniteJumpGenerator Ω) (T : NNReal) (y : Ω) :
    ∀ᵐ p ∂G.reverseWindowKernel T y,
      FullPath.initialState p.2 = p.1 ∧
        FullPath.terminalState p.2 = y := by
  have hset : MeasurableSet
      {p : Ω × FullPath Ω |
        FullPath.initialState p.2 = p.1 ∧
          FullPath.terminalState p.2 = y} := by
    exact
      ((FullPath.measurable_initialState.comp measurable_snd).eq
        measurable_fst).setOf.inter
        ((FullPath.measurable_terminalState.comp measurable_snd).eq_const y).setOf
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, FullPath.reverse γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T y),
    FullPath.initialState p.2 = p.1 ∧
      FullPath.terminalState p.2 = y
  refine (ae_map_iff (f := record) ?_ hset).2 ?_
  · simpa [record] using
      (FullPath.measurable_terminalState.prodMk
        FullPath.measurable_reverse).aemeasurable
  · filter_upwards [G.pathLawFrom_ae_initialState T y] with γ hγ
    exact ⟨FullPath.initialState_reverse γ, by simpa using hγ⟩

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
