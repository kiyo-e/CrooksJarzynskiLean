/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Probability

/-!
# Finite canonical equilibrium

This module defines finite Gibbs distributions, partition functions, free
energy, and the one-step algebraic identity that combines an energy quench with
local detailed balance.
-/

open scoped BigOperators

namespace CrooksJarzynski

universe u

/-- An energy landscape on a finite state space. -/
abbrev Energy (Ω : Type u) := Ω → ℝ

/-- The unnormalized Boltzmann weight. -/
noncomputable def boltzmannWeight {Ω : Type u}
    (β : ℝ) (E : Energy Ω) (x : Ω) : ℝ :=
  Real.exp (-β * E x)

/-- The finite canonical partition function. -/
noncomputable def partitionFunction {Ω : Type u} [Fintype Ω]
    (β : ℝ) (E : Energy Ω) : ℝ :=
  ∑ x, boltzmannWeight β E x

/-- The Gibbs probability of a microstate. -/
noncomputable def gibbsProbability {Ω : Type u} [Fintype Ω]
    (β : ℝ) (E : Energy Ω) (x : Ω) : ℝ :=
  boltzmannWeight β E x / partitionFunction β E

/-- The Helmholtz free energy in units where the Boltzmann constant is one. -/
noncomputable def freeEnergy {Ω : Type u} [Fintype Ω]
    (β : ℝ) (E : Energy Ω) : ℝ :=
  -Real.log (partitionFunction β E) / β

@[simp]
theorem boltzmannWeight_pos {Ω : Type u}
    (β : ℝ) (E : Energy Ω) (x : Ω) :
    0 < boltzmannWeight β E x :=
  Real.exp_pos _

@[simp]
theorem partitionFunction_pos {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (E : Energy Ω) :
    0 < partitionFunction β E := by
  unfold partitionFunction
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

@[simp]
theorem partitionFunction_ne_zero {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (E : Energy Ω) :
    partitionFunction β E ≠ 0 :=
  (partitionFunction_pos β E).ne'

@[simp]
theorem gibbsProbability_nonneg {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (E : Energy Ω) (x : Ω) :
    0 ≤ gibbsProbability β E x := by
  exact div_nonneg (le_of_lt (boltzmannWeight_pos β E x))
    (le_of_lt (partitionFunction_pos β E))

@[simp]
theorem sum_gibbsProbability {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (E : Energy Ω) :
    ∑ x, gibbsProbability β E x = 1 := by
  unfold gibbsProbability
  rw [← Finset.sum_div]
  change partitionFunction β E / partitionFunction β E = 1
  exact div_self (partitionFunction_ne_zero β E)

/-- The Gibbs law bundled as a finite distribution. -/
noncomputable def gibbsDistribution {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (E : Energy Ω) : FiniteDistribution Ω where
  prob := gibbsProbability β E
  nonneg := gibbsProbability_nonneg β E
  sum_prob := sum_gibbsProbability β E

/-- Exponentiating a free-energy difference gives the partition-function ratio. -/
theorem exp_beta_mul_freeEnergy_sub {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (hβ : β ≠ 0) (E₀ E₁ : Energy Ω) :
    Real.exp (β * (freeEnergy β E₁ - freeEnergy β E₀)) =
      partitionFunction β E₀ / partitionFunction β E₁ := by
  have hZ₀ : 0 < partitionFunction β E₀ := partitionFunction_pos β E₀
  have hZ₁ : 0 < partitionFunction β E₁ := partitionFunction_pos β E₁
  have harg :
      β * (freeEnergy β E₁ - freeEnergy β E₀) =
        Real.log (partitionFunction β E₀) - Real.log (partitionFunction β E₁) := by
    unfold freeEnergy
    field_simp [hβ]
    ring
  rw [harg, Real.exp_sub, Real.exp_log hZ₀, Real.exp_log hZ₁]

/-- The negative-exponent form used by the Jarzynski equality. -/
theorem exp_neg_beta_mul_freeEnergy_sub {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (hβ : β ≠ 0) (E₀ E₁ : Energy Ω) :
    Real.exp (-β * (freeEnergy β E₁ - freeEnergy β E₀)) =
      partitionFunction β E₁ / partitionFunction β E₀ := by
  convert exp_beta_mul_freeEnergy_sub β hβ E₁ E₀ using 1
  ring_nf

/-- A change of energy can be moved from the Boltzmann weight into an
exponential work factor. -/
theorem boltzmann_quench_identity {Ω : Type u}
    (β : ℝ) (E₀ E₁ : Energy Ω) (x : Ω) :
    boltzmannWeight β E₀ x =
      boltzmannWeight β E₁ x * Real.exp (β * (E₁ x - E₀ x)) := by
  unfold boltzmannWeight
  rw [← Real.exp_add]
  congr 1
  ring

/-- One-step, unnormalized Crooks identity derived from local detailed balance.

The hypothesis is division-free and remains meaningful when either transition
probability is zero.
-/
theorem boltzmann_local_crooks {Ω : Type u}
    (β : ℝ) (E₀ E₁ : Energy Ω) (Kf Kr : ℝ) (x y : Ω)
    (hbalance : boltzmannWeight β E₁ x * Kf = boltzmannWeight β E₁ y * Kr) :
    boltzmannWeight β E₀ x * Kf =
      boltzmannWeight β E₁ y * Kr * Real.exp (β * (E₁ x - E₀ x)) := by
  calc
    boltzmannWeight β E₀ x * Kf
        = (boltzmannWeight β E₁ x * Real.exp (β * (E₁ x - E₀ x))) * Kf := by
            rw [boltzmann_quench_identity]
    _ = (boltzmannWeight β E₁ x * Kf) * Real.exp (β * (E₁ x - E₀ x)) := by ring
    _ = (boltzmannWeight β E₁ y * Kr) * Real.exp (β * (E₁ x - E₀ x)) := by
          rw [hbalance]

end CrooksJarzynski
