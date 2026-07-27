/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Equilibrium

open scoped BigOperators

namespace CrooksJarzynski

universe u

/-- A finite, time-inhomogeneous stochastic thermodynamic protocol. -/
structure Protocol (Ω : Type u) [Fintype Ω] (n : ℕ) where
  β : ℝ
  β_pos : 0 < β
  energy : ℕ → Energy Ω
  forwardKernel : Fin n → Kernel Ω
  reverseKernel : Fin n → Kernel Ω
  localBalance : ∀ t x y,
    boltzmannWeight β (energy (t.val + 1)) x * forwardKernel t x y =
      boltzmannWeight β (energy (t.val + 1)) y * reverseKernel t y x

namespace Protocol

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]
variable {n : ℕ}

/-- The initial energy landscape. -/
def initialEnergy (P : Protocol Ω n) : Energy Ω :=
  P.energy 0

/-- The final energy landscape. -/
def finalEnergy (P : Protocol Ω n) : Energy Ω :=
  P.energy n

/-- The equilibrium free-energy change. -/
noncomputable def deltaFreeEnergy (P : Protocol Ω n) : ℝ :=
  freeEnergy P.β P.finalEnergy - freeEnergy P.β P.initialEnergy

/-- Work performed on the system along a continuation. -/
def workAux {Ω : Type u} :
    {n : ℕ} → (ℕ → Energy Ω) → Ω → Continuation Ω n → ℝ
  | 0, _, _, _ => 0
  | _ + 1, E, x, (y, rest) =>
      (E 1 x - E 0 x) + workAux (fun t => E (t + 1)) y rest

/-- Work performed on the system along a complete trajectory. -/
def work (P : Protocol Ω n) (γ : Trajectory Ω n) : ℝ :=
  workAux P.energy γ.1 γ.2

/-- Forward path probability. -/
noncomputable def forwardWeight (P : Protocol Ω n) (γ : Trajectory Ω n) : ℝ :=
  gibbsProbability P.β P.initialEnergy γ.1 *
    transitionWeight P.forwardKernel γ.1 γ.2

/-- Probability of the reversed trajectory in the reverse experiment. -/
noncomputable def reverseWeight (P : Protocol Ω n) (γ : Trajectory Ω n) : ℝ :=
  gibbsProbability P.β P.finalEnergy (finalState γ.1 γ.2) *
    reverseTransitionWeight P.reverseKernel γ.1 γ.2

/-- The protocol obtained after dropping its first time step. -/
def tail (P : Protocol Ω (n + 1)) : Protocol Ω n where
  β := P.β
  β_pos := P.β_pos
  energy := fun t => P.energy (t + 1)
  forwardKernel := fun t => P.forwardKernel t.succ
  reverseKernel := fun t => P.reverseKernel t.succ
  localBalance := by
    intro t x y
    simpa [Nat.add_assoc] using P.localBalance t.succ x y

/-- Forward path probabilities are nonnegative. -/
theorem forwardWeight_nonneg (P : Protocol Ω n) (γ : Trajectory Ω n) :
    0 ≤ P.forwardWeight γ := by
  exact mul_nonneg (gibbsProbability_nonneg _ _ _)
    (transitionWeight_nonneg P.forwardKernel γ.1 γ.2)

/-- Reverse path probabilities are nonnegative. -/
theorem reverseWeight_nonneg (P : Protocol Ω n) (γ : Trajectory Ω n) :
    0 ≤ P.reverseWeight γ := by
  exact mul_nonneg (gibbsProbability_nonneg _ _ _)
    (reverseTransitionWeight_nonneg P.reverseKernel γ.1 γ.2)

/-- Forward path probabilities sum to one. -/
theorem sum_forwardWeight (P : Protocol Ω n) :
    ∑ γ : Trajectory Ω n, P.forwardWeight γ = 1 := by
  unfold forwardWeight
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Ω, ∑ c : Continuation Ω n,
        gibbsProbability P.β P.initialEnergy x *
          transitionWeight P.forwardKernel x c)
        = ∑ x : Ω, gibbsProbability P.β P.initialEnergy x *
            (∑ c : Continuation Ω n,
              transitionWeight P.forwardKernel x c) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
    _ = ∑ x : Ω, gibbsProbability P.β P.initialEnergy x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sum_transitionWeight]
          simp
    _ = 1 := sum_gibbsProbability _ _

/-- Reverse path probabilities sum to one. -/
theorem sum_reverseWeight (P : Protocol Ω n) :
    ∑ γ : Trajectory Ω n, P.reverseWeight γ = 1 := by
  unfold reverseWeight
  rw [Fintype.sum_prod_type]
  exact sum_reverseTransitionWeight n P.reverseKernel
    (gibbsDistribution P.β P.finalEnergy)

/-- Unnormalized pathwise Crooks identity. -/
theorem boltzmann_crooks (P : Protocol Ω n) (γ : Trajectory Ω n) :
    boltzmannWeight P.β P.initialEnergy γ.1 *
        transitionWeight P.forwardKernel γ.1 γ.2 =
      boltzmannWeight P.β P.finalEnergy (finalState γ.1 γ.2) *
        reverseTransitionWeight P.reverseKernel γ.1 γ.2 *
          Real.exp (P.β * P.work γ) := by
  induction n with
  | zero =>
      rcases γ with ⟨x, c⟩
      cases c
      simp [initialEnergy, finalEnergy, work, workAux,
        transitionWeight, reverseTransitionWeight, finalState]
  | succ n ih =>
      rcases γ with ⟨x, ⟨y, rest⟩⟩
      have hlocal := boltzmann_local_crooks P.β (P.energy 0) (P.energy 1)
        (P.forwardKernel 0 x y) (P.reverseKernel 0 y x) x y
        (P.localBalance 0 x y)
      have htail :
          boltzmannWeight P.β (P.energy 1) y *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest =
            boltzmannWeight P.β (P.energy (n + 1)) (finalState y rest) *
              reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest *
                Real.exp (P.β * workAux (fun t => P.energy (t + 1)) y rest) := by
        simpa [tail, initialEnergy, finalEnergy, work, workAux] using
          ih P.tail (y, rest)
      change
        boltzmannWeight P.β (P.energy 0) x *
            (P.forwardKernel 0 x y *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest) =
          boltzmannWeight P.β (P.energy (n + 1)) (finalState y rest) *
            (P.reverseKernel 0 y x *
              reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest) *
            Real.exp (P.β *
              ((P.energy 1 x - P.energy 0 x) +
                workAux (fun t => P.energy (t + 1)) y rest))
      calc
        boltzmannWeight P.β (P.energy 0) x *
            (P.forwardKernel 0 x y *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest)
            = (boltzmannWeight P.β (P.energy 0) x * P.forwardKernel 0 x y) *
                transitionWeight (fun i => P.forwardKernel i.succ) y rest := by ring
        _ = (boltzmannWeight P.β (P.energy 1) y * P.reverseKernel 0 y x *
                Real.exp (P.β * (P.energy 1 x - P.energy 0 x))) *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest := by
              rw [hlocal]
        _ = P.reverseKernel 0 y x *
              Real.exp (P.β * (P.energy 1 x - P.energy 0 x)) *
              (boltzmannWeight P.β (P.energy 1) y *
                transitionWeight (fun i => P.forwardKernel i.succ) y rest) := by ring
        _ = P.reverseKernel 0 y x *
              Real.exp (P.β * (P.energy 1 x - P.energy 0 x)) *
              (boltzmannWeight P.β (P.energy (n + 1)) (finalState y rest) *
                reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest *
                  Real.exp (P.β * workAux (fun t => P.energy (t + 1)) y rest)) := by
              rw [htail]
        _ = boltzmannWeight P.β (P.energy (n + 1)) (finalState y rest) *
              (P.reverseKernel 0 y x *
                reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest) *
              Real.exp (P.β *
                ((P.energy 1 x - P.energy 0 x) +
                  workAux (fun t => P.energy (t + 1)) y rest)) := by
              rw [mul_add, Real.exp_add]
              ring

/-- Crooks' path identity in division-free partition-function form. -/
theorem crooks_partition_ratio (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.forwardWeight γ *
        (partitionFunction P.β P.initialEnergy /
          partitionFunction P.β P.finalEnergy) =
      P.reverseWeight γ * Real.exp (P.β * P.work γ) := by
  have hraw := P.boltzmann_crooks γ
  have hZ₀ : partitionFunction P.β P.initialEnergy ≠ 0 :=
    partitionFunction_ne_zero _ _
  have hZₙ : partitionFunction P.β P.finalEnergy ≠ 0 :=
    partitionFunction_ne_zero _ _
  unfold forwardWeight reverseWeight gibbsProbability
  field_simp [hZ₀, hZₙ]
  ring_nf at hraw ⊢
  exact hraw

/-- Crooks' fluctuation theorem in the usual free-energy form. -/
theorem crooks (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.forwardWeight γ * Real.exp (P.β * P.deltaFreeEnergy) =
      P.reverseWeight γ * Real.exp (P.β * P.work γ) := by
  unfold deltaFreeEnergy
  rw [exp_beta_mul_freeEnergy_sub P.β P.β_pos.ne'
    P.initialEnergy P.finalEnergy]
  exact P.crooks_partition_ratio γ

/-- Ratio form of Crooks' theorem, valid when the reverse path weight is nonzero. -/
theorem crooks_ratio (P : Protocol Ω n) (γ : Trajectory Ω n)
    (hR : P.reverseWeight γ ≠ 0) :
    P.forwardWeight γ / P.reverseWeight γ =
      Real.exp (P.β * (P.work γ - P.deltaFreeEnergy)) := by
  have hexp :
      Real.exp (P.β * (P.work γ - P.deltaFreeEnergy)) =
        Real.exp (P.β * P.work γ) /
          Real.exp (P.β * P.deltaFreeEnergy) := by
    rw [show P.β * (P.work γ - P.deltaFreeEnergy) =
      P.β * P.work γ - P.β * P.deltaFreeEnergy by ring, Real.exp_sub]
  rw [hexp]
  apply (div_eq_div_iff hR (Real.exp_ne_zero _)).2
  simpa [mul_comm] using P.crooks γ

/-- The trajectory-wise identity in the form directly summed for Jarzynski. -/
theorem crooks_weighted (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.forwardWeight γ * Real.exp (-P.β * P.work γ) =
      P.reverseWeight γ * Real.exp (-P.β * P.deltaFreeEnergy) := by
  have hW :
      Real.exp (-P.β * P.work γ) =
        (Real.exp (P.β * P.work γ))⁻¹ := by
    rw [show -P.β * P.work γ = -(P.β * P.work γ) by ring, Real.exp_neg]
  have hF :
      Real.exp (-P.β * P.deltaFreeEnergy) =
        (Real.exp (P.β * P.deltaFreeEnergy))⁻¹ := by
    rw [show -P.β * P.deltaFreeEnergy = -(P.β * P.deltaFreeEnergy) by ring,
      Real.exp_neg]
  calc
    P.forwardWeight γ * Real.exp (-P.β * P.work γ)
        = P.forwardWeight γ / Real.exp (P.β * P.work γ) := by
            rw [hW, div_eq_mul_inv]
    _ = P.reverseWeight γ / Real.exp (P.β * P.deltaFreeEnergy) := by
          apply (div_eq_div_iff (Real.exp_ne_zero _) (Real.exp_ne_zero _)).2
          simpa [mul_comm] using P.crooks γ
    _ = P.reverseWeight γ * Real.exp (-P.β * P.deltaFreeEnergy) := by
          rw [hF, div_eq_mul_inv]

/-- The Jarzynski equality. -/
theorem jarzynski (P : Protocol Ω n) :
    ∑ γ : Trajectory Ω n,
        P.forwardWeight γ * Real.exp (-P.β * P.work γ) =
      Real.exp (-P.β * P.deltaFreeEnergy) := by
  calc
    (∑ γ : Trajectory Ω n,
        P.forwardWeight γ * Real.exp (-P.β * P.work γ))
        = ∑ γ : Trajectory Ω n,
            P.reverseWeight γ * Real.exp (-P.β * P.deltaFreeEnergy) := by
              apply Finset.sum_congr rfl
              intro γ _
              exact P.crooks_weighted γ
    _ = (∑ γ : Trajectory Ω n, P.reverseWeight γ) *
          Real.exp (-P.β * P.deltaFreeEnergy) := by
          rw [Finset.sum_mul]
    _ = Real.exp (-P.β * P.deltaFreeEnergy) := by
          rw [P.sum_reverseWeight]
          simp

/-- The exponential average of dissipated work is one. -/
theorem integral_fluctuation_theorem (P : Protocol Ω n) :
    ∑ γ : Trajectory Ω n,
        P.forwardWeight γ *
          Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) = 1 := by
  have hexp (γ : Trajectory Ω n) :
      Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) =
        Real.exp (P.β * P.deltaFreeEnergy) *
          Real.exp (-P.β * P.work γ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∑ γ : Trajectory Ω n,
        P.forwardWeight γ *
          Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)))
        = ∑ γ : Trajectory Ω n,
            Real.exp (P.β * P.deltaFreeEnergy) *
              (P.forwardWeight γ * Real.exp (-P.β * P.work γ)) := by
              apply Finset.sum_congr rfl
              intro γ _
              rw [hexp]
              ring
    _ = Real.exp (P.β * P.deltaFreeEnergy) *
          (∑ γ : Trajectory Ω n,
            P.forwardWeight γ * Real.exp (-P.β * P.work γ)) := by
          rw [Finset.mul_sum]
    _ = Real.exp (P.β * P.deltaFreeEnergy) *
          Real.exp (-P.β * P.deltaFreeEnergy) := by
          rw [P.jarzynski]
    _ = 1 := by
          rw [show -P.β * P.deltaFreeEnergy =
            -(P.β * P.deltaFreeEnergy) by ring, Real.exp_neg]
          exact mul_inv_cancel₀ (Real.exp_ne_zero _)

/-- Expected work in the forward process. -/
noncomputable def meanWork (P : Protocol Ω n) : ℝ :=
  ∑ γ : Trajectory Ω n, P.forwardWeight γ * P.work γ

/-- Expected dissipated work. -/
noncomputable def meanDissipatedWork (P : Protocol Ω n) : ℝ :=
  P.meanWork - P.deltaFreeEnergy

/-- The average-work form of the second law, derived from Jarzynski. -/
theorem second_law (P : Protocol Ω n) :
    P.deltaFreeEnergy ≤ P.meanWork := by
  have hexp := P.integral_fluctuation_theorem
  have htangent (γ : Trajectory Ω n) :
      1 - P.β * (P.work γ - P.deltaFreeEnergy) ≤
        Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) := by
    simpa [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-P.β * (P.work γ - P.deltaFreeEnergy))
  have hweighted :
      ∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 - P.β * (P.work γ - P.deltaFreeEnergy)) ≤ 1 := by
    calc
      (∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 - P.β * (P.work γ - P.deltaFreeEnergy)))
          ≤ ∑ γ : Trajectory Ω n,
              P.forwardWeight γ *
                Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) := by
              apply Finset.sum_le_sum
              intro γ _
              exact mul_le_mul_of_nonneg_left (htangent γ)
                (P.forwardWeight_nonneg γ)
      _ = 1 := hexp
  have hleft :
      ∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 - P.β * (P.work γ - P.deltaFreeEnergy)) =
        1 - P.β * (P.meanWork - P.deltaFreeEnergy) := by
    calc
      (∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 - P.β * (P.work γ - P.deltaFreeEnergy)))
          = ∑ γ : Trajectory Ω n,
              (P.forwardWeight γ -
                P.β * (P.forwardWeight γ * P.work γ) +
                (P.β * P.deltaFreeEnergy) * P.forwardWeight γ) := by
              apply Finset.sum_congr rfl
              intro γ _
              ring
      _ = (∑ γ : Trajectory Ω n, P.forwardWeight γ) -
            (∑ γ : Trajectory Ω n,
              P.β * (P.forwardWeight γ * P.work γ)) +
            (∑ γ : Trajectory Ω n,
              (P.β * P.deltaFreeEnergy) * P.forwardWeight γ) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ γ : Trajectory Ω n, P.forwardWeight γ) -
            P.β * (∑ γ : Trajectory Ω n,
              P.forwardWeight γ * P.work γ) +
            (∑ γ : Trajectory Ω n,
              (P.β * P.deltaFreeEnergy) * P.forwardWeight γ) := by
            rw [Finset.mul_sum]
      _ = (∑ γ : Trajectory Ω n, P.forwardWeight γ) -
            P.β * (∑ γ : Trajectory Ω n,
              P.forwardWeight γ * P.work γ) +
            (P.β * P.deltaFreeEnergy) *
              (∑ γ : Trajectory Ω n, P.forwardWeight γ) := by
            simpa only [Finset.mul_sum]
      _ = 1 - P.β * P.meanWork + P.β * P.deltaFreeEnergy := by
            simp [P.sum_forwardWeight, meanWork]
      _ = 1 - P.β * (P.meanWork - P.deltaFreeEnergy) := by ring
  rw [hleft] at hweighted
  nlinarith [P.β_pos]

/-- Mean dissipated work is nonnegative. -/
theorem meanDissipatedWork_nonneg (P : Protocol Ω n) :
    0 ≤ P.meanDissipatedWork := by
  unfold meanDissipatedWork
  exact sub_nonneg.mpr P.second_law

end Protocol

end CrooksJarzynski
