/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolMarkedCrooks

/-!
# Finite marked protocols with endpoint work

This module iterates the endpoint-work Crooks extension over a finite family of
marked transition kernels.  The forward and reverse measures are the marked
path measures constructed by kernel composition, rather than auxiliary sums or
marginals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Marked

universe u v

variable {Ω : Type u} {Λ : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Finite-horizon Crooks relation for marked transitions whose work increment
is evaluated at the endpoint reached by each transition. -/
theorem multiStep_endpoint_crooks
    {n : ℕ}
    (equilibrium : Fin (n + 1) → Measure Ω)
    (forward reverse :
      Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    (workWeight : Fin n → Ω → ℝ≥0∞)
    (freeEnergyWeight : Fin n → ℝ≥0∞)
    [hEquilibrium : ∀ i, IsProbabilityMeasure (equilibrium i)]
    [hForward : ∀ i, IsMarkovKernel (forward i)]
    [hReverse : ∀ i, IsMarkovKernel (reverse i)]
    (hwork : ∀ i, Measurable (workWeight i))
    (hbalance : ∀ i,
      equilibrium i.castSucc ⊗ₘ forward i =
        (equilibrium i.castSucc ⊗ₘ reverse i).map
          (swapEndpointsEquiv (Ω := Ω) (Λ := Λ)))
    (hreweight : ∀ i,
      (equilibrium i.castSucc).withDensity (workWeight i) =
        freeEnergyWeight i • equilibrium i.succ) :
    CrooksRelation
      (reversedForwardPathMeasure (equilibrium 0) forward)
      (reversePathMeasure (equilibrium (Fin.last n)) reverse)
      (reversedEndpointWorkWeight workWeight)
      (Markov.accumulatedFreeEnergyWeight freeEnergyWeight) := by
  induction n with
  | zero =>
      have hfr : forward = reverse := Subsingleton.elim _ _
      subst reverse
      simp [CrooksRelation, reversedForwardPathMeasure,
        reversedEndpointWorkWeight, Markov.accumulatedFreeEnergyWeight]
  | succ n ih =>
      let equilibriumPrefix : Fin (n + 1) → Measure Ω :=
        fun i => equilibrium i.castSucc
      let forwardPrefix :
          Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ) :=
        fun i => forward i.castSucc
      let reversePrefix :
          Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ) :=
        fun i => reverse i.castSucc
      let workPrefix : Fin n → Ω → ℝ≥0∞ :=
        fun i => workWeight i.castSucc
      let factorPrefix : Fin n → ℝ≥0∞ :=
        fun i => freeEnergyWeight i.castSucc
      letI : ∀ i, IsProbabilityMeasure (equilibriumPrefix i) :=
        fun i => hEquilibrium i.castSucc
      letI : ∀ i, IsMarkovKernel (forwardPrefix i) :=
        fun i => hForward i.castSucc
      letI : ∀ i, IsMarkovKernel (reversePrefix i) :=
        fun i => hReverse i.castSucc
      have hprefix :
          CrooksRelation
            (reversedForwardPathMeasure (equilibriumPrefix 0) forwardPrefix)
            (reversePathMeasure
              (equilibriumPrefix (Fin.last n)) reversePrefix)
            (reversedEndpointWorkWeight workPrefix)
            (Markov.accumulatedFreeEnergyWeight factorPrefix) := by
        apply ih
        · intro i
          exact hwork i.castSucc
        · intro i
          dsimp [equilibriumPrefix, forwardPrefix, reversePrefix]
          simpa using hbalance i.castSucc
        · intro i
          dsimp [equilibriumPrefix, workPrefix, factorPrefix]
          simpa using hreweight i.castSucc
      letI : IsMarkovKernel (forward (Fin.last n)) :=
        hForward (Fin.last n)
      letI : IsMarkovKernel (reverse (Fin.last n)) :=
        hReverse (Fin.last n)
      have hext := extendEndpoint_crooks
        (prefixForward :=
          reversedForwardPathMeasure (equilibriumPrefix 0) forwardPrefix)
        (current := equilibriumPrefix (Fin.last n))
        (next := equilibrium ((Fin.last n).succ))
        (past := reverseContinuationKernel reversePrefix)
        (forward := forward (Fin.last n))
        (reverse := reverse (Fin.last n))
        (prefixWork := reversedEndpointWorkWeight workPrefix)
        (stepWork := workWeight (Fin.last n))
        (prefixFactor :=
          Markov.accumulatedFreeEnergyWeight factorPrefix)
        (stepFactor := freeEnergyWeight (Fin.last n))
        (measurable_reversedEndpointWorkWeight workPrefix
          (fun i => hwork i.castSucc))
        (hwork (Fin.last n))
        (by simpa [reversePathMeasure] using hprefix)
        (by
          dsimp [equilibriumPrefix]
          exact hbalance (Fin.last n))
        (by
          dsimp [equilibriumPrefix]
          exact hreweight (Fin.last n))
      rw [Fin.succ_last] at hext
      have hendpoint :
          (forward (Fin.last n)).comap
              (fun p : MarkedPath Ω Λ n => p.1)
              (measurable_fst : Measurable
                (fun p : MarkedPath Ω Λ n => p.1)) =
            endpointKernel (forward (Fin.last n)) n := by
        rfl
      rw [hendpoint] at hext
      change @CrooksRelation
        (Ω × ((Ω × Λ) × MarkedContinuation Ω Λ n)) _ _ _ _ _
      exact hext

/-- The Jarzynski equality for the constructed finite marked path measures. -/
theorem multiStep_endpoint_jarzynski
    {n : ℕ}
    (equilibrium : Fin (n + 1) → Measure Ω)
    (forward reverse :
      Fin n → ProbabilityTheory.Kernel Ω (Ω × Λ))
    (workWeight : Fin n → Ω → ℝ≥0∞)
    (freeEnergyWeight : Fin n → ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (equilibrium i)]
    [∀ i, IsMarkovKernel (forward i)]
    [∀ i, IsMarkovKernel (reverse i)]
    (hwork : ∀ i, Measurable (workWeight i))
    (hbalance : ∀ i,
      equilibrium i.castSucc ⊗ₘ forward i =
        (equilibrium i.castSucc ⊗ₘ reverse i).map
          (swapEndpointsEquiv (Ω := Ω) (Λ := Λ)))
    (hreweight : ∀ i,
      (equilibrium i.castSucc).withDensity (workWeight i) =
        freeEnergyWeight i • equilibrium i.succ) :
    ∫⁻ γ, reversedEndpointWorkWeight workWeight γ
        ∂reversedForwardPathMeasure (equilibrium 0) forward =
      Markov.accumulatedFreeEnergyWeight freeEnergyWeight := by
  exact jarzynski_lintegral _ _ _ _
    (multiStep_endpoint_crooks equilibrium forward reverse
      workWeight freeEnergyWeight hwork hbalance hreweight)

end Marked
end MeasureProtocol
end CrooksJarzynski
