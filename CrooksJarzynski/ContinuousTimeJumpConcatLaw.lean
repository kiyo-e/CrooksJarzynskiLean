/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatDensity

/-!
# Concatenation law for finite-generator path measures

This module proves the path-level Chapman--Kolmogorov law for the normalized
fixed-initial law of a finite jump generator.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The total holding time is a measurable complete-path observable. -/
@[fun_prop]
theorem measurable_totalHoldingTime :
    Measurable (totalHoldingTime : FullPath Ω → NNReal) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact JumpPath.measurable_totalHoldingTime hs

end FullPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
/-- The raw counting reference is concentrated on paths that exactly fill the
prescribed horizon. -/
theorem rawCountingReference_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.rawCountingReference T n, γ.totalHoldingTime = T := by
  unfold rawCountingReference
  apply Measure.ae_smul_measure
  simpa [JumpPath.horizonSet] using
    (Simplex.rawPathProbability_ae_horizon T
      (G.stateSequenceCountingReference n))

omit [MeasurableSingletonClass Ω] in
/-- Every fixed-initial sector law exactly fills its prescribed horizon. -/
theorem sectorLawFrom_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    ∀ᵐ γ ∂G.sectorLawFrom T x n, γ.totalHoldingTime = T := by
  have hraw := G.rawCountingReference_ae_totalHoldingTime T n
  unfold sectorLawFrom pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hraw

omit [MeasurableSingletonClass Ω] in
/-- **Exact-horizon support.**  Almost every complete path sampled from the
fixed-initial path law has total holding time equal to its horizon. -/
theorem pathLawFrom_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    (fun γ => FullPath.totalHoldingTime γ) =ᵐ[G.pathLawFrom T x]
      fun _ => T := by
  have hset : MeasurableSet
      {γ : FullPath Ω | FullPath.totalHoldingTime γ = T} :=
    (FullPath.measurable_totalHoldingTime.eq_const T).setOf
  unfold pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable hset]
  exact G.sectorLawFrom_ae_totalHoldingTime T x n

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
