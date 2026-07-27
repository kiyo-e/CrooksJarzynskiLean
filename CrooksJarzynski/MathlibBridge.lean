/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Protocol
import Mathlib.Probability.Kernel.Basic

/-!
# Bridge to Mathlib probability kernels

This module embeds the elementary finite distributions and transition kernels
used by the Crooks–Jarzynski development into Mathlib's measure-theoretic
`ProbabilityTheory.Kernel` API.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CrooksJarzynski

universe u

namespace FiniteDistribution

variable {Ω : Type u} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The probability measure associated with a finite real-valued distribution. -/
noncomputable def toMeasure (μ : FiniteDistribution Ω) : Measure Ω :=
  ∑ x : Ω, ENNReal.ofReal (μ x) • Measure.dirac x

/-- Evaluation of the associated measure on a measurable set. -/
theorem toMeasure_apply (μ : FiniteDistribution Ω) {s : Set Ω}
    (hs : MeasurableSet s) :
    μ.toMeasure s =
      ∑ x : Ω, ENNReal.ofReal (μ x) * s.indicator 1 x := by
  simp [toMeasure, hs, Measure.dirac_apply']

@[simp]
theorem toMeasure_univ (μ : FiniteDistribution Ω) :
    μ.toMeasure Set.univ = 1 := by
  rw [toMeasure_apply μ MeasurableSet.univ]
  simp only [Set.indicator_of_mem, Set.mem_univ, Pi.one_apply, mul_one]
  calc
    (∑ x : Ω, ENNReal.ofReal (μ x)) =
        ENNReal.ofReal (∑ x : Ω, μ x) := by
      simpa using
        (ENNReal.ofReal_sum_of_nonneg
          (s := (Finset.univ : Finset Ω))
          (f := fun x => μ x)
          (by intro x _; exact μ.nonneg x)).symm
    _ = 1 := by simp [μ.sum_prob]

noncomputable instance (μ : FiniteDistribution Ω) :
    IsProbabilityMeasure μ.toMeasure where
  measure_univ := μ.toMeasure_univ

@[simp]
theorem toMeasure_singleton (μ : FiniteDistribution Ω) (x : Ω) :
    μ.toMeasure {x} = ENNReal.ofReal (μ x) := by
  classical
  rw [toMeasure_apply μ (measurableSet_singleton x)]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

end FiniteDistribution

namespace MathlibBridge

variable {Ω : Type u} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Embed an elementary finite transition kernel into Mathlib's kernel type. -/
noncomputable def toKernel (K : CrooksJarzynski.Kernel Ω) :
    ProbabilityTheory.Kernel Ω Ω :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x => (K x).toMeasure

@[simp]
theorem toKernel_apply (K : CrooksJarzynski.Kernel Ω) (x : Ω) :
    toKernel K x = (K x).toMeasure :=
  rfl

noncomputable instance (K : CrooksJarzynski.Kernel Ω) :
    ProbabilityTheory.IsMarkovKernel (toKernel K) := by
  constructor
  intro x
  change IsProbabilityMeasure ((K x).toMeasure)
  infer_instance

/-- The mass of a singleton is exactly the original transition probability. -/
@[simp]
theorem toKernel_singleton (K : CrooksJarzynski.Kernel Ω) (x y : Ω) :
    toKernel K x {y} = ENNReal.ofReal (K x y) := by
  rw [toKernel_apply]
  exact FiniteDistribution.toMeasure_singleton (K x) y

end MathlibBridge

namespace Protocol

variable {Ω : Type u} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every protocol transition kernel has a canonical Mathlib Markov-kernel view. -/
noncomputable def forwardMathlibKernel
    {n : ℕ} (P : Protocol Ω n) (t : Fin n) :
    ProbabilityTheory.Kernel Ω Ω :=
  MathlibBridge.toKernel (P.forwardKernel t)

/-- Every reverse transition kernel has a canonical Mathlib Markov-kernel view. -/
noncomputable def reverseMathlibKernel
    {n : ℕ} (P : Protocol Ω n) (t : Fin n) :
    ProbabilityTheory.Kernel Ω Ω :=
  MathlibBridge.toKernel (P.reverseKernel t)

@[simp]
theorem forwardMathlibKernel_singleton
    {n : ℕ} (P : Protocol Ω n) (t : Fin n) (x y : Ω) :
    P.forwardMathlibKernel t x {y} =
      ENNReal.ofReal (P.forwardKernel t x y) := by
  exact MathlibBridge.toKernel_singleton (P.forwardKernel t) x y

@[simp]
theorem reverseMathlibKernel_singleton
    {n : ℕ} (P : Protocol Ω n) (t : Fin n) (x y : Ω) :
    P.reverseMathlibKernel t x {y} =
      ENNReal.ofReal (P.reverseKernel t x y) := by
  exact MathlibBridge.toKernel_singleton (P.reverseKernel t) x y

end Protocol

end CrooksJarzynski
