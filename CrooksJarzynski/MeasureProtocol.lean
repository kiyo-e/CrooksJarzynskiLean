/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Measure-theoretic Crooks–Jarzynski infrastructure

This module contains the state-space-independent core of the development.  A
Crooks relation is expressed as an equality of measures on an arbitrary
measurable trajectory space.  Evaluating that equality on the whole space gives
the Jarzynski equality as a Lebesgue integral.

The module also adapts an ordinary time-inhomogeneous family of Mathlib Markov
kernels `K t : Kernel Ω Ω` to the history-dependent kernels expected by
Mathlib's Ionescu–Tulcea construction.  Thus `trajectoryMeasure μ₀ K` is the law
of the full trajectory on `ℕ → Ω` for an arbitrary measurable state space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski

universe u

namespace MeasureProtocol

variable {Γ : Type u} [MeasurableSpace Γ]

/-- A division-free Crooks relation on an arbitrary measurable trajectory
space.  `workWeight` is the exponential work factor and `freeEnergyWeight` is
the corresponding equilibrium factor. -/
def CrooksRelation (forward reverse : Measure Γ)
    (workWeight : Γ → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞) : Prop :=
  forward.withDensity workWeight = freeEnergyWeight • reverse

/-- The measure-theoretic Jarzynski equality follows by evaluating the Crooks
measure identity on the whole trajectory space. -/
theorem jarzynski_lintegral
    (forward reverse : Measure Γ) (workWeight : Γ → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞) [IsProbabilityMeasure reverse]
    (h : CrooksRelation forward reverse workWeight freeEnergyWeight) :
    ∫⁻ γ, workWeight γ ∂forward = freeEnergyWeight := by
  have h_univ := congrArg (fun μ : Measure Γ => μ Set.univ) h
  simpa [CrooksRelation, withDensity_apply] using h_univ

/-- The physical exponential form of `jarzynski_lintegral`. -/
theorem jarzynski_exponential
    (forward reverse : Measure Γ) (β ΔF : ℝ) (work : Γ → ℝ)
    [IsProbabilityMeasure reverse]
    (h : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work γ)))
      (ENNReal.ofReal (Real.exp (-β * ΔF)))) :
    ∫⁻ γ, ENNReal.ofReal (Real.exp (-β * work γ)) ∂forward =
      ENNReal.ofReal (Real.exp (-β * ΔF)) :=
  jarzynski_lintegral forward reverse _ _ h

namespace Markov

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The last state in a history indexed by `Set.Iic t`. -/
def historyLast (t : ℕ) (x : (i : Set.Iic t) → Ω) : Ω :=
  x ⟨t, Set.mem_Iic.mpr le_rfl⟩

@[fun_prop]
theorem measurable_historyLast (t : ℕ) :
    Measurable (historyLast (Ω := Ω) t) :=
  measurable_pi_apply _

/-- Regard an ordinary Markov kernel as a history-dependent kernel by reading
only the most recent state.  This is the adapter required by Ionescu–Tulcea. -/
def historyKernel (K : ℕ → Kernel Ω Ω) (t : ℕ) :
    Kernel ((i : Set.Iic t) → Ω) Ω :=
  (K t).comap (historyLast t) (measurable_historyLast t)

instance instIsMarkovKernelHistoryKernel
    (K : ℕ → Kernel Ω Ω) [∀ t, IsMarkovKernel (K t)] (t : ℕ) :
    IsMarkovKernel (historyKernel K t) := by
  unfold historyKernel
  infer_instance

/-- The Ionescu–Tulcea trajectory law of a time-inhomogeneous Markov chain on
an arbitrary measurable state space. -/
noncomputable def trajectoryMeasure
    (μ₀ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] : Measure (ℕ → Ω) :=
  Kernel.trajMeasure μ₀ (historyKernel K)

noncomputable instance instIsProbabilityMeasureTrajectoryMeasure
    (μ₀ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] :
    IsProbabilityMeasure (trajectoryMeasure μ₀ K) := by
  unfold trajectoryMeasure
  infer_instance

/-- Every finite prefix of `trajectoryMeasure` is extended by the prescribed
next-step Markov kernel. -/
theorem trajectoryMeasure_step
    (μ₀ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (t : ℕ) :
    (trajectoryMeasure μ₀ K).map (frestrictLe t) ⊗ₘ historyKernel K t =
      (trajectoryMeasure μ₀ K).map
        (fun x => (frestrictLe t x, x (t + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end Markov

end MeasureProtocol

end CrooksJarzynski
