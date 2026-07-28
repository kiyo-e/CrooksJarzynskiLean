/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.TimeReversal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous-time limit of the two discrete work conventions

This module separates the comparison of the quench-then-transition and
transition-then-quench work conventions from the stochastic protocol. It
works with only an energy schedule and a path through the state space.

For the quench increment

`q_t(x) = E_{t+1}(x) - E_t(x)`,

the convention discrepancy is

`D = ∑ t, (q_t(x_{t+1}) - q_t(x_t))`.

A discrete summation-by-parts identity rewrites this as two boundary terms
plus temporal differences of `q_t` at the same state. Consequently, if
`|q_t| ≤ M h` and `|q_{t+1} - q_t| ≤ L h²` on a uniform mesh of width
`h = T / N`, then every path satisfies

`|D| ≤ (2 M T + L T²) / N`.

The estimate is independent of the transition kernels and of the path law.
It therefore gives path-uniform convergence of the two conventions as the
mesh is refined. This is a finite-variation time-discretization result, not
an Itô--Stratonovich conversion theorem.
-/

open Filter Topology
open scoped BigOperators

namespace CrooksJarzynski

universe u

namespace WorkConvention

/-- An energy landscape at each of the `n + 1` vertices of a time mesh. -/
abbrev EnergySchedule (Ω : Type u) (n : ℕ) := Fin (n + 1) → Ω → ℝ

/-- A state at each of the `n + 1` vertices of a time mesh. -/
abbrev Path (Ω : Type u) (n : ℕ) := Fin (n + 1) → Ω

/-- The energy change caused by the quench across edge `t`, evaluated at `x`. -/
def quenchIncrement {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω n) (t : Fin n) (x : Ω) : ℝ :=
  E t.succ x - E t.castSucc x

/-- Work obtained by evaluating each quench before the corresponding state transition. -/
noncomputable def quenchThenTransitionWork {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω n) (x : Path Ω n) : ℝ :=
  ∑ t : Fin n, quenchIncrement E t (x t.castSucc)

/-- Work obtained by evaluating each quench after the corresponding state transition. -/
noncomputable def transitionThenQuenchWork {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω n) (x : Path Ω n) : ℝ :=
  ∑ t : Fin n, quenchIncrement E t (x t.succ)

/-- The transition-then-quench work minus the quench-then-transition work. -/
noncomputable def discrepancy {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω n) (x : Path Ω n) : ℝ :=
  transitionThenQuenchWork E x - quenchThenTransitionWork E x

/-- The discrepancy is the sum of the change of each quench increment across its edge. -/
theorem discrepancy_eq_sum {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω n) (x : Path Ω n) :
    discrepancy E x =
      ∑ t : Fin n,
        (quenchIncrement E t (x t.succ) -
          quenchIncrement E t (x t.castSucc)) := by
  unfold discrepancy transitionThenQuenchWork quenchThenTransitionWork
  rw [← Finset.sum_sub_distrib]

private theorem castSucc_succ_eq_succ_castSucc {n : ℕ} (t : Fin n) :
    t.castSucc.succ = t.succ.castSucc := by
  apply Fin.ext
  rfl

private theorem last_succ_eq_last (n : ℕ) :
    (Fin.last n).succ = Fin.last (n + 1) := by
  apply Fin.ext
  rfl

private theorem zero_castSucc_eq_zero {n : ℕ} :
    (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
  rfl

private theorem sum_sub_sum_summation_by_parts {n : ℕ}
    (a b : Fin (n + 1) → ℝ) :
    (∑ t, a t) - ∑ t, b t =
      a (Fin.last n) - b 0 +
        ∑ t : Fin n, (a t.castSucc - b t.succ) := by
  rw [Fin.sum_univ_castSucc a, Fin.sum_univ_succ b,
    Finset.sum_sub_distrib]
  ring

/-- Discrete summation by parts for the work-convention discrepancy.

The right-hand side contains no state increment: the interior terms compare
successive quench increments at the same occupied state. -/
theorem discrepancy_summation_by_parts {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω (n + 1)) (x : Path Ω (n + 1)) :
    discrepancy E x =
      quenchIncrement E (Fin.last n) (x (Fin.last (n + 1))) -
        quenchIncrement E 0 (x 0) +
      ∑ t : Fin n,
        (quenchIncrement E t.castSucc (x t.succ.castSucc) -
          quenchIncrement E t.succ (x t.succ.castSucc)) := by
  unfold discrepancy transitionThenQuenchWork quenchThenTransitionWork
  simpa only [castSucc_succ_eq_succ_castSucc, last_succ_eq_last,
    zero_castSucc_eq_zero] using
    (sum_sub_sum_summation_by_parts
      (a := fun t : Fin (n + 1) => quenchIncrement E t (x t.succ))
      (b := fun t : Fin (n + 1) => quenchIncrement E t (x t.castSucc)))

/-- A path-uniform finite-difference estimate.

If every quench increment is bounded by `A` and every temporal difference of
successive quench increments is bounded by `B`, then an `(n + 1)`-edge path
has discrepancy at most `2 A + n B`. -/
theorem discrepancy_abs_le {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω (n + 1)) (x : Path Ω (n + 1))
    {A B : ℝ}
    (hA : ∀ t z, |quenchIncrement E t z| ≤ A)
    (hB : ∀ (t : Fin n) z,
      |quenchIncrement E t.castSucc z - quenchIncrement E t.succ z| ≤ B) :
    |discrepancy E x| ≤ 2 * A + (n : ℝ) * B := by
  rw [discrepancy_summation_by_parts]
  have hBoundary :
      |quenchIncrement E (Fin.last n) (x (Fin.last (n + 1))) -
          quenchIncrement E 0 (x 0)| ≤ 2 * A := by
    calc
      |quenchIncrement E (Fin.last n) (x (Fin.last (n + 1))) -
          quenchIncrement E 0 (x 0)| ≤
          |quenchIncrement E (Fin.last n) (x (Fin.last (n + 1)))| +
            |quenchIncrement E 0 (x 0)| := abs_sub _ _
      _ ≤ A + A := add_le_add (hA _ _) (hA _ _)
      _ = 2 * A := by ring
  have hInterior :
      |∑ t : Fin n,
          (quenchIncrement E t.castSucc (x t.succ.castSucc) -
            quenchIncrement E t.succ (x t.succ.castSucc))| ≤
        (n : ℝ) * B := by
    calc
      |∑ t : Fin n,
          (quenchIncrement E t.castSucc (x t.succ.castSucc) -
            quenchIncrement E t.succ (x t.succ.castSucc))| ≤
          ∑ t : Fin n,
            |quenchIncrement E t.castSucc (x t.succ.castSucc) -
              quenchIncrement E t.succ (x t.succ.castSucc)| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun t : Fin n =>
              quenchIncrement E t.castSucc (x t.succ.castSucc) -
                quenchIncrement E t.succ (x t.succ.castSucc))
            Finset.univ)
      _ ≤ ∑ _t : Fin n, B := by
        apply Finset.sum_le_sum
        intro t _
        exact hB t _
      _ = (n : ℝ) * B := by simp
  exact (abs_add_le _ _).trans (add_le_add hBoundary hInterior)

/-- The finite-difference estimate with bounds scaled by a mesh width `h`. -/
theorem discrepancy_abs_le_of_mesh {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω (n + 1)) (x : Path Ω (n + 1))
    {M L h : ℝ}
    (hIncrement : ∀ t z, |quenchIncrement E t z| ≤ M * h)
    (hVariation : ∀ (t : Fin n) z,
      |quenchIncrement E t.castSucc z - quenchIncrement E t.succ z| ≤ L * h ^ 2) :
    |discrepancy E x| ≤
      2 * (M * h) + (n : ℝ) * (L * h ^ 2) :=
  discrepancy_abs_le E x hIncrement hVariation

/-- On a uniform `N = n + 1` step mesh, the two work conventions differ by `O(1/N)`
uniformly over all paths. -/
theorem discrepancy_uniform_grid_abs_le {Ω : Type u} {n : ℕ}
    (E : EnergySchedule Ω (n + 1)) (x : Path Ω (n + 1))
    {T M L : ℝ} (hL : 0 ≤ L)
    (hIncrement : ∀ t z,
      |quenchIncrement E t z| ≤ M * (T / ((n + 1 : ℕ) : ℝ)))
    (hVariation : ∀ (t : Fin n) z,
      |quenchIncrement E t.castSucc z - quenchIncrement E t.succ z| ≤
        L * (T / ((n + 1 : ℕ) : ℝ)) ^ 2) :
    |discrepancy E x| ≤
      (2 * M * T + L * T ^ 2) / ((n + 1 : ℕ) : ℝ) := by
  have hSharp := discrepancy_abs_le_of_mesh E x hIncrement hVariation
  have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  have hCoefficient :
      0 ≤ L * (T / ((n + 1 : ℕ) : ℝ)) ^ 2 :=
    mul_nonneg hL (sq_nonneg _)
  calc
    |discrepancy E x| ≤
        2 * (M * (T / ((n + 1 : ℕ) : ℝ))) +
          (n : ℝ) * (L * (T / ((n + 1 : ℕ) : ℝ)) ^ 2) := hSharp
    _ ≤ 2 * (M * (T / ((n + 1 : ℕ) : ℝ))) +
          ((n + 1 : ℕ) : ℝ) *
            (L * (T / ((n + 1 : ℕ) : ℝ)) ^ 2) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hn hCoefficient) _
    _ = (2 * M * T + L * T ^ 2) / ((n + 1 : ℕ) : ℝ) := by
      have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hne]

/-- The discrepancy tends to zero uniformly over all paths on each mesh. -/
theorem discrepancy_uniform_tendsto_zero {Ω : Type u}
    (E : ∀ n, EnergySchedule Ω (n + 1))
    {T M L : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hIncrement : ∀ n t z,
      |quenchIncrement (E n) t z| ≤ M * (T / ((n + 1 : ℕ) : ℝ)))
    (hVariation : ∀ n (t : Fin n) z,
      |quenchIncrement (E n) t.castSucc z -
          quenchIncrement (E n) t.succ z| ≤
        L * (T / ((n + 1 : ℕ) : ℝ)) ^ 2) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ x : Path Ω (n + 1), |discrepancy (E n) x| < ε := by
  have hC : 0 ≤ 2 * M * T + L * T ^ 2 := by positivity
  have hMajorant :
      Tendsto
        (fun n : ℕ =>
          (2 * M * T + L * T ^ 2) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa using
      ((tendsto_add_atTop_iff_nat 1).2
        (tendsto_const_div_atTop_nhds_zero_nat
          (𝕜 := ℝ) (2 * M * T + L * T ^ 2)))
  intro ε hε
  rw [Metric.tendsto_atTop] at hMajorant
  obtain ⟨N, hN⟩ := hMajorant ε hε
  rw [eventually_atTop]
  refine ⟨N, fun n hn x => ?_⟩
  have hBound := discrepancy_uniform_grid_abs_le
    (E := E n) (x := x) hL (hIncrement n) (hVariation n)
  have hMajorantLt := hN n hn
  rw [Real.dist_eq, sub_zero] at hMajorantLt
  have hMajorantNonneg :
      0 ≤ (2 * M * T + L * T ^ 2) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg hC (by positivity)
  rw [abs_of_nonneg hMajorantNonneg] at hMajorantLt
  exact lt_of_le_of_lt hBound hMajorantLt

/-- For any choice of one path on every uniform mesh, the discrepancy tends to zero. -/
theorem discrepancy_tendsto_zero {Ω : Type u}
    (E : ∀ n, EnergySchedule Ω (n + 1))
    (x : ∀ n, Path Ω (n + 1))
    {T M L : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hIncrement : ∀ n t z,
      |quenchIncrement (E n) t z| ≤ M * (T / ((n + 1 : ℕ) : ℝ)))
    (hVariation : ∀ n (t : Fin n) z,
      |quenchIncrement (E n) t.castSucc z -
          quenchIncrement (E n) t.succ z| ≤
        L * (T / ((n + 1 : ℕ) : ℝ)) ^ 2) :
    Tendsto (fun n => discrepancy (E n) (x n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hUniform :=
    discrepancy_uniform_tendsto_zero E hT hM hL hIncrement hVariation ε hε
  rw [eventually_atTop] at hUniform
  obtain ⟨N, hN⟩ := hUniform
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn (x n)⟩

/-- The energy schedule underlying a stochastic protocol, without its kernels. -/
def ofProtocol {Ω : Type u} [Fintype Ω] {n : ℕ}
    (P : Protocol Ω n) : EnergySchedule Ω n :=
  fun t => P.energy t.val

@[simp]
theorem quenchIncrement_ofProtocol {Ω : Type u} [Fintype Ω] {n : ℕ}
    (P : Protocol Ω n) (t : Fin n) (z : Ω) :
    quenchIncrement (ofProtocol P) t z =
      P.energy (t.val + 1) z - P.energy t.val z :=
  rfl

/-- The generic quench-then-transition work specializes to the existing protocol work. -/
@[simp]
theorem quenchThenTransitionWork_ofProtocol
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (P : Protocol Ω n) (γ : Trajectory Ω n) :
    quenchThenTransitionWork (ofProtocol P) (Trajectory.stateAt γ) = P.work γ := by
  rw [P.work_eq_sum_quenchThenTransitionIncrement γ]
  rfl

/-- The generic transition-then-quench work specializes to the existing protocol convention. -/
@[simp]
theorem transitionThenQuenchWork_ofProtocol
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (P : Protocol Ω n) (γ : Trajectory Ω n) :
    transitionThenQuenchWork (ofProtocol P) (Trajectory.stateAt γ) =
      P.transitionThenQuenchWork γ :=
  rfl

/-- The generic discrepancy is exactly the protocol-level convention difference. -/
@[simp]
theorem discrepancy_ofProtocol
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (P : Protocol Ω n) (γ : Trajectory Ω n) :
    discrepancy (ofProtocol P) (Trajectory.stateAt γ) =
      P.transitionThenQuenchWork γ - P.work γ := by
  unfold discrepancy
  rw [transitionThenQuenchWork_ofProtocol, quenchThenTransitionWork_ofProtocol]

end WorkConvention

end CrooksJarzynski
