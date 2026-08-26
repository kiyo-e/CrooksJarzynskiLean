/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoState
import CrooksJarzynski.ContinuousTimeJumpRenewalIntegrals

/-!
# Normalization of the asymmetric two-state jump law

The asymmetric chain has state-dependent escape rates, so its sector masses are
not the Poisson masses of the symmetric chain.  This module proves that they
still sum to one, by a telescoping argument that stays entirely inside
finite-dimensional simplex integrals.

For a fixed initial state, `arrivalIntegral` is the probability that the first
`n` jumps all occur before the horizon, written as a weighted integral over the
free-coordinate simplex.  `sectorIntegral` is the probability of seeing exactly
`n` jumps.  Integrating out the last free coordinate shows that consecutive
arrival integrals differ by exactly one sector integral, so the partial sums of
the sector integrals telescope to `1 - arrivalIntegral`.  The arrival integrals
are dominated by `(2T)^n / n!` and vanish, hence the sector integrals sum to
one.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

export Renewal (ratePrefixProduct arrivalIntegral sectorIntegral arrivalIntegral_zero
  lintegral_cubeExpWeight_succ sectorIntegral_add_arrivalIntegral_succ arrivalIntegral_le
  tendsto_pow_mul_factorial_inv)

/-! ### The alternating two-state chain -/

/-- The state-dependent total escape rate of the asymmetric chain. -/
def stateRate : State → NNReal
  | .zero => 2
  | .one => 1

theorem stateRate_le_two (x : State) : stateRate x ≤ 2 := by
  cases x <;> norm_num [stateRate]

/-- Rates seen along the alternating chain started at `x`. -/
def chainRates (x : State) (n : ℕ) : Fin n → NNReal :=
  fun i => stateRate (iterateFlip i.1 x)

theorem chainRates_castSucc (x : State) (n : ℕ) :
    (fun i : Fin n => chainRates x (n + 1) i.castSucc) = chainRates x n := by
  funext i
  simp [chainRates]

theorem chainRates_last (x : State) (n : ℕ) :
    chainRates x (n + 1) (Fin.last n) = stateRate (iterateFlip n x) := by
  simp [chainRates]

/-- Arrival mass of the asymmetric chain started at `x`. -/
noncomputable def arrivalMass (T : NNReal) (x : State) (n : ℕ) : ℝ≥0∞ :=
  arrivalIntegral (chainRates x n) T

/-- Sector mass of the asymmetric chain started at `x`. -/
noncomputable def sectorMass (T : NNReal) (x : State) (n : ℕ) : ℝ≥0∞ :=
  sectorIntegral (chainRates x n) (stateRate (iterateFlip n x)) T

theorem sectorMass_add_arrivalMass_succ (T : NNReal) (x : State) (n : ℕ) :
    sectorMass T x n + arrivalMass T x (n + 1) = arrivalMass T x n := by
  have h := sectorIntegral_add_arrivalIntegral_succ (chainRates x (n + 1)) T
  rw [chainRates_castSucc, chainRates_last] at h
  exact h

theorem arrivalMass_zero (T : NNReal) (x : State) :
    arrivalMass T x 0 = 1 :=
  arrivalIntegral_zero _ T

/-- Partial sums of sector masses telescope against the arrival mass. -/
theorem sum_sectorMass_add_arrivalMass (T : NNReal) (x : State) (N : ℕ) :
    (∑ n ∈ Finset.range N, sectorMass T x n) + arrivalMass T x N = 1 := by
  induction N with
  | zero => simp [arrivalMass_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc,
        sectorMass_add_arrivalMass_succ]
      exact ih

theorem tendsto_arrivalMass (T : NNReal) (x : State) :
    Filter.Tendsto (fun n => arrivalMass T x n) Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n : ℕ =>
      ((2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
        ENNReal.ofReal (1 / (n.factorial : ℝ)))
    tendsto_const_nhds (by
      simpa using tendsto_pow_mul_factorial_inv T 2)
    (fun n => bot_le)
    (fun n => by
      simpa [arrivalMass] using arrivalIntegral_le (chainRates x n) T 2
        (fun i => stateRate_le_two _))

/-- The sector masses of the asymmetric chain sum to one for every initial
state. -/
theorem tsum_sectorMass (T : NNReal) (x : State) :
    ∑' n, sectorMass T x n = 1 := by
  have hpartial :
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, sectorMass T x n)
        Filter.atTop (nhds (∑' n, sectorMass T x n)) :=
    ENNReal.tendsto_nat_tsum _
  have hsum :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, sectorMass T x n) + arrivalMass T x N)
        Filter.atTop (nhds ((∑' n, sectorMass T x n) + 0)) :=
    hpartial.add (tendsto_arrivalMass T x)
  rw [add_zero] at hsum
  have hone :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, sectorMass T x n) + arrivalMass T x N)
        Filter.atTop (nhds 1) := by
    simp only [sum_sectorMass_add_arrivalMass]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hone
