/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricFixedInitial
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parity evaluation for the asymmetric two-state chain

This module evaluates the parity-filtered sums of the asymmetric jump-sector
masses.  The proof uses a first-jump renewal equation on a variable remaining
fraction of the fixed physical horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample
namespace Renewal

/-- The free simplex with total available fraction `ρ` instead of one. -/
def freeSimplexSetAt (n : ℕ) (ρ : I) : Set (Fin n → I) :=
  {u | ∑ i, (u i : ℝ) ≤ (ρ : ℝ)}

/-- The variable-horizon free simplex is measurable. -/
theorem measurableSet_freeSimplexSetAt (n : ℕ) (ρ : I) :
    MeasurableSet (freeSimplexSetAt n ρ) := by
  unfold freeSimplexSetAt
  exact measurableSet_le (by fun_prop) measurable_const

/-- The fraction of the horizon remaining after a first holding fraction `a`. -/
def remainingFraction (ρ a : I) : I :=
  ⟨max ((ρ : ℝ) - (a : ℝ)) 0,
    le_max_right _ _,
    max_le (by linarith [ρ.2.2, a.2.1]) (by norm_num)⟩

@[simp]
theorem coe_remainingFraction_of_le (ρ a : I)
    (ha : (a : ℝ) ≤ (ρ : ℝ)) :
    (remainingFraction ρ a : ℝ) = (ρ : ℝ) - (a : ℝ) := by
  simp [remainingFraction, max_eq_left (sub_nonneg.mpr ha)]

/-- At the full remaining fraction, the variable simplex is the standard free
simplex. -/
theorem freeSimplexSetAt_one (n : ℕ) :
    freeSimplexSetAt n (1 : I) = Simplex.freeSimplexSet n := by
  ext u
  simp [freeSimplexSetAt, Simplex.freeSimplexSet]

/-- Arrival mass for `n` jumps when only the fraction `ρ` of the fixed physical
horizon `T` is available. -/
noncomputable def arrivalIntegralAt {n : ℕ} (r : Fin n → NNReal)
    (T : NNReal) (ρ : I) : ℝ≥0∞ :=
  ratePrefixProduct r T *
    ∫⁻ u in freeSimplexSetAt n ρ, cubeExpWeight r T u

/-- Variable-horizon arrival mass along the alternating chain started at `x`. -/
noncomputable def arrivalMassAt
    (T : NNReal) (ρ : I) (x : State) (n : ℕ) : ℝ≥0∞ :=
  arrivalIntegralAt (chainRates x n) T ρ

/-- Residual horizon fraction after all free holding fractions have been used. -/
def residualAt {n : ℕ} (ρ : I) (u : Fin n → I) : ℝ :=
  (ρ : ℝ) - ∑ i, (u i : ℝ)

@[fun_prop]
theorem measurable_residualAt {n : ℕ} (ρ : I) :
    Measurable (residualAt (n := n) ρ) := by
  unfold residualAt
  fun_prop

/-- Exactly-`n`-jump mass on a remaining horizon fraction `ρ`. -/
noncomputable def sectorIntegralAt {n : ℕ} (r : Fin n → NNReal)
    (c : NNReal) (T : NNReal) (ρ : I) : ℝ≥0∞ :=
  ratePrefixProduct r T *
    ∫⁻ u in freeSimplexSetAt n ρ,
      cubeExpWeight r T u *
        ENNReal.ofReal
          (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt ρ u)))

/-- Variable-horizon sector mass along the alternating asymmetric chain. -/
noncomputable def sectorMassAt
    (T : NNReal) (ρ : I) (x : State) (n : ℕ) : ℝ≥0∞ :=
  sectorIntegralAt (chainRates x n) (stateRate (iterateFlip n x)) T ρ

/-- The variable-horizon construction at `ρ = 1` is the existing arrival mass. -/
theorem arrivalMassAt_one (T : NNReal) (x : State) (n : ℕ) :
    arrivalMassAt T (1 : I) x n = arrivalMass T x n := by
  simp [arrivalMassAt, arrivalIntegralAt, arrivalMass, arrivalIntegral,
    freeSimplexSetAt_one]

/-- The variable-horizon sector construction at `ρ = 1` is the existing sector
mass. -/
theorem sectorMassAt_one (T : NNReal) (x : State) (n : ℕ) :
    sectorMassAt T (1 : I) x n = sectorMass T x n := by
  unfold sectorMassAt sectorIntegralAt sectorMass sectorIntegral residualAt
  rw [freeSimplexSetAt_one]

/-- Before any jump is requested, every remaining horizon has arrival mass one. -/
theorem arrivalMassAt_zero (T : NNReal) (ρ : I) (x : State) :
    arrivalMassAt T ρ x 0 = 1 := by
  have hset : freeSimplexSetAt 0 ρ = Set.univ := by
    ext u
    simp [freeSimplexSetAt, ρ.2.1]
  simp [arrivalMassAt, arrivalIntegralAt, ratePrefixProduct,
    cubeExpWeight, hset]

/-- The zero-jump sector is the survival probability over the remaining
fraction of the horizon. -/
theorem sectorMassAt_zero (T : NNReal) (ρ : I) (x : State) :
    sectorMassAt T ρ x 0 =
      ENNReal.ofReal
        (Real.exp (-((stateRate x : ℝ) * (T : ℝ) * (ρ : ℝ)))) := by
  have hset : freeSimplexSetAt 0 ρ = Set.univ := by
    ext u
    simp [freeSimplexSetAt, ρ.2.1]
  simp [sectorMassAt, sectorIntegralAt, ratePrefixProduct,
    cubeExpWeight, residualAt, chainRates, hset]

/-- Iterated flipping commutes with changing the prescribed initial state by one
flip. -/
theorem iterateFlip_flip_start (n : ℕ) (x : State) :
    iterateFlip n (flip x) = flip (iterateFlip n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterateFlip_succ, ih, flip_flip]

/-- Removing the first rate from an alternating rate sequence starts the same
sequence at the flipped state. -/
theorem chainRates_succ (x : State) (n : ℕ) :
    (fun i : Fin n => chainRates x (n + 1) i.succ) =
      chainRates (flip x) n := by
  funext i
  simp [chainRates, iterateFlip_flip_start]

end Renewal
end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
