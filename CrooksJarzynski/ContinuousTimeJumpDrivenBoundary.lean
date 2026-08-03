/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDriven
import CrooksJarzynski.ContinuousTimeJumpDrivenBalance

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
    refine ⟨FullPath.initialState_reverse γ, ?_⟩
    change FullPath.terminalState (FullPath.reverse γ) = y
    rw [FullPath.terminalState_reverse]
    exact hγ

/-- A forward window retains an almost-surely valid fixed-horizon path chart. -/
theorem forwardWindowKernel_ae_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ p ∂G.forwardWindowKernel T x,
      FullPath.IsValid T p.2 := by
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T x),
    FullPath.IsValid T p.2
  refine (ae_map_iff
    (FullPath.measurable_terminalState.prodMk measurable_id).aemeasurable
    ((FullPath.measurableSet_isValid T).preimage measurable_snd)).2 ?_
  simpa [record] using G.pathLawFrom_ae_isValid T x

private theorem sectorLawFrom_ae_reverse_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    ∀ᵐ γ ∂G.sectorLawFrom T x n,
      JumpPath.IsValid T (JumpPath.reverse γ) := by
  have hraw : ∀ᵐ γ ∂G.rawCountingReference T n,
      JumpPath.IsValid T (JumpPath.reverse γ) := by
    have hvalid := G.rawCountingReference_ae_isValid T n
    have hmapped : ∀ᵐ γ ∂(G.rawCountingReference T n).map JumpPath.reverse,
        JumpPath.IsValid T γ := by
      rw [G.map_rawCountingReference_reverse T n]
      exact hvalid
    rw [ae_map_iff JumpPath.measurable_reverse.aemeasurable
      (JumpPath.measurableSet_isValid T)] at hmapped
    exact hmapped
  unfold sectorLawFrom pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hraw

private theorem pathLawFrom_ae_reverse_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ γ ∂G.pathLawFrom T x,
      FullPath.IsValid T (FullPath.reverse γ) := by
  unfold pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  refine (ae_map_iff (FullPath.measurable_mk n).aemeasurable
    ((FullPath.measurableSet_isValid T).preimage
      FullPath.measurable_reverse)).2 ?_
  simpa [FullPath.reverse, FullPath.IsValid] using
    G.sectorLawFrom_ae_reverse_isValid T x n

/-- A reverse window stores the sampled chart after reversal. Reversal
invariance of the raw counting chart removes the zero-measure boundary on
which the sampled terminal holding time would become a zero first interval. -/
theorem reverseWindowKernel_ae_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (y : Ω) :
    ∀ᵐ p ∂G.reverseWindowKernel T y,
      FullPath.IsValid T p.2 := by
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, FullPath.reverse γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T y),
    FullPath.IsValid T p.2
  refine (ae_map_iff
    (FullPath.measurable_terminalState.prodMk
      FullPath.measurable_reverse).aemeasurable
    ((FullPath.measurableSet_isValid T).preimage measurable_snd)).2 ?_
  simpa [record] using G.pathLawFrom_ae_reverse_isValid T y

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
