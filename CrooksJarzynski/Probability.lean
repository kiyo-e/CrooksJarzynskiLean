import Mathlib

/-!
# Finite probability and trajectory infrastructure

This module defines finite distributions, finite-state Markov kernels, and a
recursive representation of finite trajectories. The recursive representation
makes trajectory normalization an elementary induction over the number of time
steps.
-/

open scoped BigOperators

namespace CrooksJarzynski

universe u

/-- A probability distribution on a finite type, represented by real weights. -/
structure FiniteDistribution (Ω : Type u) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_prob : ∑ x, prob x = 1

instance {Ω : Type u} [Fintype Ω] :
    CoeFun (FiniteDistribution Ω) (fun _ => Ω → ℝ) :=
  ⟨FiniteDistribution.prob⟩

@[simp]
theorem FiniteDistribution.sum_apply {Ω : Type u} [Fintype Ω]
    (μ : FiniteDistribution Ω) : ∑ x, μ x = 1 :=
  μ.sum_prob

/-- A finite-state Markov kernel. Every row is a finite distribution. -/
abbrev Kernel (Ω : Type u) [Fintype Ω] := Ω → FiniteDistribution Ω

/-- The states after a specified initial state in an `n`-step trajectory. -/
def Continuation (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Ω × Continuation Ω n

@[reducible]
private noncomputable def continuationFintype
    (Ω : Type u) [Fintype Ω] : (n : ℕ) → Fintype (Continuation Ω n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
      letI : Fintype (Continuation Ω n) := continuationFintype Ω n
      inferInstanceAs (Fintype (Ω × Continuation Ω n))

noncomputable instance {Ω : Type u} [Fintype Ω] (n : ℕ) :
    Fintype (Continuation Ω n) :=
  continuationFintype Ω n

/-- A complete trajectory, consisting of its initial state and continuation. -/
abbrev Trajectory (Ω : Type u) (n : ℕ) := Ω × Continuation Ω n

/-- The terminal state of a trajectory continuation. -/
def finalState {Ω : Type u} : {n : ℕ} → Ω → Continuation Ω n → Ω
  | 0, x, _ => x
  | _ + 1, _, (y, rest) => finalState y rest

/-- Product of forward transition probabilities along a continuation. -/
def transitionWeight {Ω : Type u} [Fintype Ω] :
    {n : ℕ} → (Fin n → Kernel Ω) → Ω → Continuation Ω n → ℝ
  | 0, _, _, _ => 1
  | _ + 1, K, x, (y, rest) =>
      K 0 x y * transitionWeight (fun i => K i.succ) y rest

/-- Product of reverse transition probabilities on the reversed trajectory.

For a forward edge `x → y`, the reverse experiment uses `y → x`.
-/
def reverseTransitionWeight {Ω : Type u} [Fintype Ω] :
    {n : ℕ} → (Fin n → Kernel Ω) → Ω → Continuation Ω n → ℝ
  | 0, _, _, _ => 1
  | _ + 1, K, x, (y, rest) =>
      K 0 y x * reverseTransitionWeight (fun i => K i.succ) y rest

@[simp]
theorem finalState_zero {Ω : Type u} (x : Ω) (c : Continuation Ω 0) :
    finalState x c = x := by
  cases c
  rfl

@[simp]
theorem transitionWeight_zero {Ω : Type u} [Fintype Ω]
    (K : Fin 0 → Kernel Ω) (x : Ω) (c : Continuation Ω 0) :
    transitionWeight K x c = 1 := by
  cases c
  rfl

@[simp]
theorem reverseTransitionWeight_zero {Ω : Type u} [Fintype Ω]
    (K : Fin 0 → Kernel Ω) (x : Ω) (c : Continuation Ω 0) :
    reverseTransitionWeight K x c = 1 := by
  cases c
  rfl

/-- Forward transition products are nonnegative. -/
theorem transitionWeight_nonneg {Ω : Type u} [Fintype Ω]
    {n : ℕ} (K : Fin n → Kernel Ω) (x : Ω) (c : Continuation Ω n) :
    0 ≤ transitionWeight K x c := by
  induction n generalizing x with
  | zero =>
      cases c
      simp [transitionWeight]
  | succ n ih =>
      rcases c with ⟨y, rest⟩
      simp only [transitionWeight]
      exact mul_nonneg ((K 0 x).nonneg y)
        (ih (fun i => K i.succ) y rest)

/-- Reverse transition products are nonnegative. -/
theorem reverseTransitionWeight_nonneg {Ω : Type u} [Fintype Ω]
    {n : ℕ} (K : Fin n → Kernel Ω) (x : Ω) (c : Continuation Ω n) :
    0 ≤ reverseTransitionWeight K x c := by
  induction n generalizing x with
  | zero =>
      cases c
      simp [reverseTransitionWeight]
  | succ n ih =>
      rcases c with ⟨y, rest⟩
      simp only [reverseTransitionWeight]
      exact mul_nonneg ((K 0 y).nonneg x)
        (ih (fun i => K i.succ) y rest)

/-- Conditional forward trajectory weights sum to one from every starting state. -/
theorem sum_transitionWeight {Ω : Type u} [Fintype Ω]
    (n : ℕ) (K : Fin n → Kernel Ω) (x : Ω) :
    ∑ c : Continuation Ω n, transitionWeight K x c = 1 := by
  induction n generalizing x with
  | zero =>
      change (∑ _ : PUnit, (1 : ℝ)) = 1
      simp
  | succ n ih =>
      change
        (∑ c : Ω × Continuation Ω n,
          transitionWeight (n := n + 1) K x c) = 1
      rw [Fintype.sum_prod_type]
      simp only [transitionWeight]
      calc
        (∑ y : Ω, ∑ rest : Continuation Ω n,
            K 0 x y * transitionWeight (fun i => K i.succ) y rest)
            = ∑ y : Ω, K 0 x y *
                (∑ rest : Continuation Ω n,
                  transitionWeight (fun i => K i.succ) y rest) := by
                apply Finset.sum_congr rfl
                intro y _
                rw [Finset.mul_sum]
        _ = ∑ y : Ω, K 0 x y := by
              apply Finset.sum_congr rfl
              intro y _
              rw [ih]
              simp
        _ = 1 := (K 0 x).sum_prob

/-- Reverse trajectory weights, with an arbitrary terminal distribution, sum to one. -/
theorem sum_reverseTransitionWeight {Ω : Type u} [Fintype Ω]
    (n : ℕ) (K : Fin n → Kernel Ω) (ν : FiniteDistribution Ω) :
    ∑ x : Ω, ∑ c : Continuation Ω n,
      ν (finalState x c) * reverseTransitionWeight K x c = 1 := by
  induction n with
  | zero =>
      change (∑ x : Ω, ∑ _ : PUnit, ν x * (1 : ℝ)) = 1
      simpa using ν.sum_prob
  | succ n ih =>
      change
        (∑ x : Ω, ∑ c : Ω × Continuation Ω n,
          ν (finalState (n := n + 1) x c) *
            reverseTransitionWeight (n := n + 1) K x c) = 1
      simp only [Fintype.sum_prod_type, finalState, reverseTransitionWeight]
      calc
        (∑ x : Ω, ∑ y : Ω, ∑ rest : Continuation Ω n,
            ν (finalState y rest) *
              (K 0 y x * reverseTransitionWeight (fun i => K i.succ) y rest))
            = ∑ y : Ω, ∑ rest : Continuation Ω n, ∑ x : Ω,
                ν (finalState y rest) *
                  (K 0 y x * reverseTransitionWeight (fun i => K i.succ) y rest) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro y _
                rw [Finset.sum_comm]
        _ = ∑ y : Ω, ∑ rest : Continuation Ω n,
              (ν (finalState y rest) *
                reverseTransitionWeight (fun i => K i.succ) y rest) *
                (∑ x : Ω, K 0 y x) := by
              apply Finset.sum_congr rfl
              intro y _
              apply Finset.sum_congr rfl
              intro rest _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = ∑ y : Ω, ∑ rest : Continuation Ω n,
              ν (finalState y rest) *
                reverseTransitionWeight (fun i => K i.succ) y rest := by
              apply Finset.sum_congr rfl
              intro y _
              apply Finset.sum_congr rfl
              intro rest _
              rw [(K 0 y).sum_prob]
              simp
        _ = 1 := ih (fun i => K i.succ)

end CrooksJarzynski
