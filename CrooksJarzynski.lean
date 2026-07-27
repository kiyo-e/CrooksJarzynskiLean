import Mathlib

/-!
# Finite-state Crooks and Jarzynski theory

This module formalizes finite, discrete-time stochastic thermodynamics in a
fully division-free pathwise form. A protocol consists of a time-dependent
finite energy landscape together with forward and reverse Markov kernels.
Local detailed balance implies Crooks' path identity. Summing that identity
gives the Jarzynski equality, and the elementary tangent inequality for `exp`
gives the average-work form of the second law.

The convention at a time step `t` is:

1. instantaneously change the energy from `E_t` to `E_{t+1}` while the state is
   still `x_t` (this contributes work `E_{t+1}(x_t) - E_t(x_t)`), then
2. apply the forward Markov kernel at the new energy, taking `x_t` to `x_{t+1}`.

The reverse experiment starts in the final Gibbs state and uses the supplied
reverse kernels in reverse chronological order. The reverse probability of a
forward-oriented trajectory is represented without constructing a separate
reversed path type; because finite products of real numbers commute, this is
exactly the probability of the reversed trajectory.
-/

open scoped BigOperators

namespace CrooksJarzynski

universe u

section Probability

variable (Ω : Type u) [Fintype Ω]

/-- A probability distribution on a finite type, represented by real weights. -/
structure FiniteDistribution where
  prob : Ω → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_prob : ∑ x, prob x = 1

instance : CoeFun (FiniteDistribution Ω) (fun _ => Ω → ℝ) := ⟨FiniteDistribution.prob⟩

@[simp]
theorem FiniteDistribution.sum_apply (μ : FiniteDistribution Ω) : ∑ x, μ x = 1 :=
  μ.sum_prob

/-- A finite-state Markov kernel. Every row is itself a finite distribution. -/
abbrev Kernel := Ω → FiniteDistribution Ω

/-- The states after a specified initial state in an `n`-step trajectory. -/
def Continuation : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Ω × Continuation n

private noncomputable def continuationFintype : (n : ℕ) → Fintype (Continuation Ω n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
      letI : Fintype (Continuation Ω n) := continuationFintype n
      inferInstanceAs (Fintype (Ω × Continuation Ω n))

noncomputable instance (n : ℕ) : Fintype (Continuation Ω n) := continuationFintype Ω n

/-- A complete trajectory, consisting of its initial state and continuation. -/
abbrev Trajectory (n : ℕ) := Ω × Continuation Ω n

/-- The terminal state of a trajectory continuation. -/
def finalState : {n : ℕ} → Ω → Continuation Ω n → Ω
  | 0, x, _ => x
  | _ + 1, _, (y, rest) => finalState y rest

/-- Product of forward transition probabilities along a continuation. -/
def transitionWeight : {n : ℕ} → (Fin n → Kernel Ω) → Ω → Continuation Ω n → ℝ
  | 0, _, _, _ => 1
  | _ + 1, K, x, (y, rest) =>
      K 0 x y * transitionWeight (fun i => K i.succ) y rest

/-- Product of reverse transition probabilities on the reversed trajectory.

For a forward edge `x → y`, the reverse experiment uses `y → x`.
-/
def reverseTransitionWeight :
    {n : ℕ} → (Fin n → Kernel Ω) → Ω → Continuation Ω n → ℝ
  | 0, _, _, _ => 1
  | _ + 1, K, x, (y, rest) =>
      K 0 y x * reverseTransitionWeight (fun i => K i.succ) y rest

@[simp]
theorem finalState_zero (x : Ω) (c : Continuation Ω 0) : finalState x c = x := by
  cases c
  rfl

@[simp]
theorem transitionWeight_zero (K : Fin 0 → Kernel Ω) (x : Ω) (c : Continuation Ω 0) :
    transitionWeight K x c = 1 := by
  cases c
  rfl

@[simp]
theorem reverseTransitionWeight_zero
    (K : Fin 0 → Kernel Ω) (x : Ω) (c : Continuation Ω 0) :
    reverseTransitionWeight K x c = 1 := by
  cases c
  rfl

/-- Conditional forward trajectory weights sum to one from every starting state. -/
theorem sum_transitionWeight (n : ℕ) (K : Fin n → Kernel Ω) (x : Ω) :
    ∑ c : Continuation Ω n, transitionWeight K x c = 1 := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      change
        (∑ c : Ω × Continuation Ω n,
          transitionWeight K x c) = 1
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
theorem sum_reverseTransitionWeight
    (n : ℕ) (K : Fin n → Kernel Ω) (ν : FiniteDistribution Ω) :
    ∑ x : Ω, ∑ c : Continuation Ω n,
      ν (finalState x c) * reverseTransitionWeight K x c = 1 := by
  induction n with
  | zero =>
      simpa using ν.sum_prob
  | succ n ih =>
      change
        (∑ x : Ω, ∑ c : Ω × Continuation Ω n,
          ν (finalState x c) * reverseTransitionWeight K x c) = 1
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
        _ = 1 := ih (fun i => K i.succ) ν

end Probability

section Equilibrium

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]

/-- An energy landscape on a finite state space. -/
abbrev Energy := Ω → ℝ

/-- The unnormalized Boltzmann weight. -/
noncomputable def boltzmannWeight (β : ℝ) (E : Energy) (x : Ω) : ℝ :=
  Real.exp (-β * E x)

/-- The finite canonical partition function. -/
noncomputable def partitionFunction (β : ℝ) (E : Energy) : ℝ :=
  ∑ x, boltzmannWeight β E x

/-- The Gibbs probability of a microstate. -/
noncomputable def gibbsProbability (β : ℝ) (E : Energy) (x : Ω) : ℝ :=
  boltzmannWeight β E x / partitionFunction β E

/-- The Helmholtz free energy in units where the Boltzmann constant is one. -/
noncomputable def freeEnergy (β : ℝ) (E : Energy) : ℝ :=
  -Real.log (partitionFunction β E) / β

@[simp]
theorem boltzmannWeight_pos (β : ℝ) (E : Energy) (x : Ω) :
    0 < boltzmannWeight β E x :=
  Real.exp_pos _

@[simp]
theorem partitionFunction_pos (β : ℝ) (E : Energy) :
    0 < partitionFunction β E := by
  unfold partitionFunction
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

@[simp]
theorem partitionFunction_ne_zero (β : ℝ) (E : Energy) :
    partitionFunction β E ≠ 0 :=
  (partitionFunction_pos β E).ne'

@[simp]
theorem gibbsProbability_nonneg (β : ℝ) (E : Energy) (x : Ω) :
    0 ≤ gibbsProbability β E x := by
  exact div_nonneg (le_of_lt (boltzmannWeight_pos β E x))
    (le_of_lt (partitionFunction_pos β E))

@[simp]
theorem sum_gibbsProbability (β : ℝ) (E : Energy) :
    ∑ x, gibbsProbability β E x = 1 := by
  unfold gibbsProbability partitionFunction
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_ne_zero_iff.mpr ⟨Classical.arbitrary Ω, Finset.mem_univ _, by positivity⟩)

/-- The Gibbs law bundled as a finite distribution. -/
noncomputable def gibbsDistribution (β : ℝ) (E : Energy) : FiniteDistribution Ω where
  prob := gibbsProbability β E
  nonneg := gibbsProbability_nonneg β E
  sum_prob := sum_gibbsProbability β E

/-- Exponentiating a free-energy difference gives the partition-function ratio. -/
theorem exp_beta_mul_freeEnergy_sub
    (β : ℝ) (hβ : β ≠ 0) (E₀ E₁ : Energy) :
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
theorem exp_neg_beta_mul_freeEnergy_sub
    (β : ℝ) (hβ : β ≠ 0) (E₀ E₁ : Energy) :
    Real.exp (-β * (freeEnergy β E₁ - freeEnergy β E₀)) =
      partitionFunction β E₁ / partitionFunction β E₀ := by
  have h := exp_beta_mul_freeEnergy_sub β hβ E₁ E₀
  convert h using 1 <;> ring

/-- A local quench identity, before inserting detailed balance. -/
theorem gibbs_quench_identity
    (β : ℝ) (E₀ E₁ : Energy) (x : Ω) :
    gibbsProbability β E₀ x *
        (partitionFunction β E₀ / partitionFunction β E₁) =
      gibbsProbability β E₁ x * Real.exp (β * (E₁ x - E₀ x)) := by
  have hZ₀ := partitionFunction_ne_zero β E₀
  have hZ₁ := partitionFunction_ne_zero β E₁
  unfold gibbsProbability boltzmannWeight
  field_simp [hZ₀, hZ₁]
  rw [← Real.exp_add]
  congr 1
  ring

/-- One-step Crooks identity derived from local detailed balance.

The balance hypothesis is written with unnormalized Boltzmann weights, so no
probability division occurs in the physical assumption.
-/
theorem local_crooks_identity
    (β : ℝ) (E₀ E₁ : Energy) (Kf Kr : ℝ) (x y : Ω)
    (hbalance : boltzmannWeight β E₁ x * Kf = boltzmannWeight β E₁ y * Kr) :
    gibbsProbability β E₀ x * Kf *
        (partitionFunction β E₀ / partitionFunction β E₁) =
      gibbsProbability β E₁ y * Kr *
        Real.exp (β * (E₁ x - E₀ x)) := by
  have hquench := gibbs_quench_identity β E₀ E₁ x
  calc
    gibbsProbability β E₀ x * Kf *
          (partitionFunction β E₀ / partitionFunction β E₁)
        = (gibbsProbability β E₀ x *
            (partitionFunction β E₀ / partitionFunction β E₁)) * Kf := by ring
    _ = gibbsProbability β E₁ x * Real.exp (β * (E₁ x - E₀ x)) * Kf := by rw [hquench]
    _ = (boltzmannWeight β E₁ x * Kf) /
          partitionFunction β E₁ * Real.exp (β * (E₁ x - E₀ x)) := by
          unfold gibbsProbability
          ring
    _ = (boltzmannWeight β E₁ y * Kr) /
          partitionFunction β E₁ * Real.exp (β * (E₁ x - E₀ x)) := by rw [hbalance]
    _ = gibbsProbability β E₁ y * Kr *
          Real.exp (β * (E₁ x - E₀ x)) := by
          unfold gibbsProbability
          ring

end Equilibrium

section Protocol

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]

/-- A finite, time-inhomogeneous stochastic thermodynamic protocol.

At step `t`, the energy is first quenched from `energy t` to `energy (t+1)`,
then `forwardKernel t` is applied. The reverse experiment uses
`reverseKernel t` in the opposite direction. `localBalance` is local detailed
balance at the post-quench energy.
-/
structure Protocol (n : ℕ) where
  β : ℝ
  β_pos : 0 < β
  energy : ℕ → Energy (Ω := Ω)
  forwardKernel : Fin n → Kernel Ω
  reverseKernel : Fin n → Kernel Ω
  localBalance : ∀ t x y,
    boltzmannWeight β (energy (t.val + 1)) x * forwardKernel t x y =
      boltzmannWeight β (energy (t.val + 1)) y * reverseKernel t y x

namespace Protocol

variable {n : ℕ}

/-- The initial energy landscape. -/
def initialEnergy (P : Protocol (Ω := Ω) n) : Energy := P.energy 0

/-- The final energy landscape. -/
def finalEnergy (P : Protocol (Ω := Ω) n) : Energy := P.energy n

/-- The equilibrium free-energy change. -/
noncomputable def deltaFreeEnergy (P : Protocol (Ω := Ω) n) : ℝ :=
  freeEnergy P.β P.finalEnergy - freeEnergy P.β P.initialEnergy

/-- Work performed on the system along a trajectory. -/
def workAux : {n : ℕ} → (ℕ → Energy (Ω := Ω)) → Ω → Continuation Ω n → ℝ
  | 0, _, _, _ => 0
  | _ + 1, E, x, (y, rest) =>
      (E 1 x - E 0 x) + workAux (fun t => E (t + 1)) y rest

/-- Work performed on the system along a complete trajectory. -/
def work (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) : ℝ :=
  workAux P.energy γ.1 γ.2

/-- Forward path probability. -/
noncomputable def forwardWeight (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) : ℝ :=
  gibbsProbability P.β P.initialEnergy γ.1 *
    transitionWeight P.forwardKernel γ.1 γ.2

/-- Probability of the reversed trajectory in the reverse experiment. -/
noncomputable def reverseWeight (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) : ℝ :=
  gibbsProbability P.β P.finalEnergy (finalState γ.1 γ.2) *
    reverseTransitionWeight P.reverseKernel γ.1 γ.2

/-- The protocol obtained after dropping its first time step. -/
def tail (P : Protocol (Ω := Ω) (n + 1)) : Protocol (Ω := Ω) n where
  β := P.β
  β_pos := P.β_pos
  energy := fun t => P.energy (t + 1)
  forwardKernel := fun t => P.forwardKernel t.succ
  reverseKernel := fun t => P.reverseKernel t.succ
  localBalance := by
    intro t x y
    simpa [Nat.add_assoc] using P.localBalance t.succ x y

@[simp]
theorem tail_initialEnergy (P : Protocol (Ω := Ω) (n + 1)) :
    P.tail.initialEnergy = P.energy 1 := rfl

@[simp]
theorem tail_finalEnergy (P : Protocol (Ω := Ω) (n + 1)) :
    P.tail.finalEnergy = P.finalEnergy := by
  rfl

@[simp]
theorem tail_deltaFreeEnergy (P : Protocol (Ω := Ω) (n + 1)) :
    P.tail.deltaFreeEnergy =
      freeEnergy P.β P.finalEnergy - freeEnergy P.β (P.energy 1) := by
  rfl

/-- Forward path probabilities are nonnegative. -/
theorem forwardWeight_nonneg (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) :
    0 ≤ P.forwardWeight γ := by
  unfold forwardWeight
  apply mul_nonneg
  · exact gibbsProbability_nonneg _ _ _
  · induction n generalizing γ with
    | zero => simp
    | succ n ih =>
        rcases γ with ⟨x, y, rest⟩
        simp only [transitionWeight]
        exact mul_nonneg ((P.forwardKernel 0 x).nonneg y)
          (ih (P := P.tail) (γ := (y, rest)))

/-- Reverse path probabilities are nonnegative. -/
theorem reverseWeight_nonneg (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) :
    0 ≤ P.reverseWeight γ := by
  unfold reverseWeight
  apply mul_nonneg
  · exact gibbsProbability_nonneg _ _ _
  · induction n generalizing γ with
    | zero => simp
    | succ n ih =>
        rcases γ with ⟨x, y, rest⟩
        simp only [reverseTransitionWeight]
        exact mul_nonneg ((P.reverseKernel 0 y).nonneg x)
          (ih (P := P.tail) (γ := (y, rest)))

/-- Forward path probabilities sum to one. -/
theorem sum_forwardWeight (P : Protocol (Ω := Ω) n) :
    ∑ γ : Trajectory Ω n, P.forwardWeight γ = 1 := by
  change
    (∑ x : Ω, ∑ c : Continuation Ω n,
      gibbsProbability P.β P.initialEnergy x *
        transitionWeight P.forwardKernel x c) = 1
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
theorem sum_reverseWeight (P : Protocol (Ω := Ω) n) :
    ∑ γ : Trajectory Ω n, P.reverseWeight γ = 1 := by
  change
    (∑ x : Ω, ∑ c : Continuation Ω n,
      gibbsProbability P.β P.finalEnergy (finalState x c) *
        reverseTransitionWeight P.reverseKernel x c) = 1
  simpa using sum_reverseTransitionWeight Ω n P.reverseKernel
    (gibbsDistribution P.β P.finalEnergy)

/-- Crooks' path identity in a division-free partition-function form. -/
theorem crooks_partition_ratio (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) :
    P.forwardWeight γ *
        (partitionFunction P.β P.initialEnergy /
          partitionFunction P.β P.finalEnergy) =
      P.reverseWeight γ * Real.exp (P.β * P.work γ) := by
  induction n generalizing P γ with
  | zero =>
      rcases γ with ⟨x, c⟩
      cases c
      simp [forwardWeight, reverseWeight, work, workAux, initialEnergy, finalEnergy]
  | succ n ih =>
      rcases γ with ⟨x, y, rest⟩
      let Q := P.tail
      have hlocal := local_crooks_identity P.β (P.energy 0) (P.energy 1)
        (P.forwardKernel 0 x y) (P.reverseKernel 0 y x) x y
        (P.localBalance 0 x y)
      have htail := ih Q (y, rest)
      have hZ₁ : partitionFunction P.β (P.energy 1) ≠ 0 :=
        partitionFunction_ne_zero _ _
      change
        (gibbsProbability P.β (P.energy 0) x *
            (P.forwardKernel 0 x y *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest)) *
            (partitionFunction P.β (P.energy 0) /
              partitionFunction P.β (P.energy (n + 1))) =
          (gibbsProbability P.β (P.energy (n + 1)) (finalState y rest) *
            (P.reverseKernel 0 y x *
              reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest)) *
            Real.exp (P.β *
              ((P.energy 1 x - P.energy 0 x) +
                workAux (fun t => P.energy (t + 1)) y rest))
      have htail' :
          (gibbsProbability P.β (P.energy 1) y *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest) *
              (partitionFunction P.β (P.energy 1) /
                partitionFunction P.β (P.energy (n + 1))) =
            (gibbsProbability P.β (P.energy (n + 1)) (finalState y rest) *
              reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest) *
              Real.exp (P.β * workAux (fun t => P.energy (t + 1)) y rest) := by
        simpa [Q, tail, forwardWeight, reverseWeight, work, initialEnergy, finalEnergy,
          workAux] using htail
      calc
        (gibbsProbability P.β (P.energy 0) x *
            (P.forwardKernel 0 x y *
              transitionWeight (fun i => P.forwardKernel i.succ) y rest)) *
            (partitionFunction P.β (P.energy 0) /
              partitionFunction P.β (P.energy (n + 1)))
            = (gibbsProbability P.β (P.energy 0) x *
                P.forwardKernel 0 x y *
                (partitionFunction P.β (P.energy 0) /
                  partitionFunction P.β (P.energy 1))) *
              (transitionWeight (fun i => P.forwardKernel i.succ) y rest *
                (partitionFunction P.β (P.energy 1) /
                  partitionFunction P.β (P.energy (n + 1)))) := by
                field_simp [hZ₁]
                ring
        _ = (gibbsProbability P.β (P.energy 1) y *
                P.reverseKernel 0 y x *
                Real.exp (P.β * (P.energy 1 x - P.energy 0 x))) *
              (transitionWeight (fun i => P.forwardKernel i.succ) y rest *
                (partitionFunction P.β (P.energy 1) /
                  partitionFunction P.β (P.energy (n + 1)))) := by
                rw [hlocal]
        _ = P.reverseKernel 0 y x *
              Real.exp (P.β * (P.energy 1 x - P.energy 0 x)) *
              ((gibbsProbability P.β (P.energy 1) y *
                transitionWeight (fun i => P.forwardKernel i.succ) y rest) *
                (partitionFunction P.β (P.energy 1) /
                  partitionFunction P.β (P.energy (n + 1)))) := by ring
        _ = P.reverseKernel 0 y x *
              Real.exp (P.β * (P.energy 1 x - P.energy 0 x)) *
              ((gibbsProbability P.β (P.energy (n + 1)) (finalState y rest) *
                reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest) *
                Real.exp (P.β * workAux (fun t => P.energy (t + 1)) y rest)) := by
                rw [htail']
        _ = (gibbsProbability P.β (P.energy (n + 1)) (finalState y rest) *
              (P.reverseKernel 0 y x *
                reverseTransitionWeight (fun i => P.reverseKernel i.succ) y rest)) *
              Real.exp (P.β *
                ((P.energy 1 x - P.energy 0 x) +
                  workAux (fun t => P.energy (t + 1)) y rest)) := by
                rw [mul_add, Real.exp_add]
                ring

/-- Crooks' fluctuation theorem in the usual free-energy form. -/
theorem crooks (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) :
    P.forwardWeight γ * Real.exp (P.β * P.deltaFreeEnergy) =
      P.reverseWeight γ * Real.exp (P.β * P.work γ) := by
  rw [exp_beta_mul_freeEnergy_sub P.β P.β_pos.ne' P.initialEnergy P.finalEnergy]
  exact P.crooks_partition_ratio γ

/-- Ratio form of Crooks' theorem, valid when the reverse path weight is nonzero. -/
theorem crooks_ratio (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n)
    (hR : P.reverseWeight γ ≠ 0) :
    P.forwardWeight γ / P.reverseWeight γ =
      Real.exp (P.β * (P.work γ - P.deltaFreeEnergy)) := by
  have hcrooks := P.crooks γ
  have hExpF : Real.exp (P.β * P.deltaFreeEnergy) ≠ 0 := Real.exp_ne_zero _
  field_simp [hR, hExpF] at hcrooks ⊢
  rw [← Real.exp_add]
  convert hcrooks using 1 <;> ring

/-- The trajectory-wise identity in the form directly summed for Jarzynski. -/
theorem crooks_weighted (P : Protocol (Ω := Ω) n) (γ : Trajectory Ω n) :
    P.forwardWeight γ * Real.exp (-P.β * P.work γ) =
      P.reverseWeight γ * Real.exp (-P.β * P.deltaFreeEnergy) := by
  have h := P.crooks γ
  have hFW : Real.exp (P.β * P.work γ) ≠ 0 := Real.exp_ne_zero _
  have hFF : Real.exp (P.β * P.deltaFreeEnergy) ≠ 0 := Real.exp_ne_zero _
  calc
    P.forwardWeight γ * Real.exp (-P.β * P.work γ)
        = (P.forwardWeight γ * Real.exp (P.β * P.deltaFreeEnergy)) /
            (Real.exp (P.β * P.deltaFreeEnergy) *
              Real.exp (P.β * P.work γ)) := by
              rw [Real.exp_neg]
              field_simp [hFW, hFF]
              ring
    _ = (P.reverseWeight γ * Real.exp (P.β * P.work γ)) /
            (Real.exp (P.β * P.deltaFreeEnergy) *
              Real.exp (P.β * P.work γ)) := by rw [h]
    _ = P.reverseWeight γ * Real.exp (-P.β * P.deltaFreeEnergy) := by
          rw [Real.exp_neg]
          field_simp [hFW, hFF]
          ring

/-- The Jarzynski equality. -/
theorem jarzynski (P : Protocol (Ω := Ω) n) :
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
theorem integral_fluctuation_theorem (P : Protocol (Ω := Ω) n) :
    ∑ γ : Trajectory Ω n,
        P.forwardWeight γ *
          Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) = 1 := by
  calc
    (∑ γ : Trajectory Ω n,
        P.forwardWeight γ *
          Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)))
        = Real.exp (P.β * P.deltaFreeEnergy) *
            (∑ γ : Trajectory Ω n,
              P.forwardWeight γ * Real.exp (-P.β * P.work γ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro γ _
              rw [← Real.exp_add]
              congr 1
              ring
    _ = Real.exp (P.β * P.deltaFreeEnergy) *
          Real.exp (-P.β * P.deltaFreeEnergy) := by rw [P.jarzynski]
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Expected work in the forward process. -/
noncomputable def meanWork (P : Protocol (Ω := Ω) n) : ℝ :=
  ∑ γ : Trajectory Ω n, P.forwardWeight γ * P.work γ

/-- Expected dissipated work. -/
noncomputable def meanDissipatedWork (P : Protocol (Ω := Ω) n) : ℝ :=
  P.meanWork - P.deltaFreeEnergy

/-- The average-work form of the second law, derived from Jarzynski. -/
theorem second_law (P : Protocol (Ω := Ω) n) :
    P.deltaFreeEnergy ≤ P.meanWork := by
  have hexp := P.integral_fluctuation_theorem
  have htangent (γ : Trajectory Ω n) :
      1 + (-P.β * (P.work γ - P.deltaFreeEnergy)) ≤
        Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) := by
    simpa [add_comm] using Real.add_one_le_exp (-P.β * (P.work γ - P.deltaFreeEnergy))
  have hweighted :
      ∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 + (-P.β * (P.work γ - P.deltaFreeEnergy))) ≤ 1 := by
    calc
      (∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 + (-P.β * (P.work γ - P.deltaFreeEnergy))))
          ≤ ∑ γ : Trajectory Ω n,
              P.forwardWeight γ *
                Real.exp (-P.β * (P.work γ - P.deltaFreeEnergy)) := by
              apply Finset.sum_le_sum
              intro γ _
              exact mul_le_mul_of_nonneg_left (htangent γ) (P.forwardWeight_nonneg γ)
      _ = 1 := hexp
  have hmean :
      ∑ γ : Trajectory Ω n,
          P.forwardWeight γ *
            (1 + (-P.β * (P.work γ - P.deltaFreeEnergy))) =
        1 - P.β * (P.meanWork - P.deltaFreeEnergy) := by
    unfold meanWork
    rw [Finset.sum_add_distrib]
    simp only [mul_add, mul_one]
    rw [P.sum_forwardWeight]
    ring_nf
    rw [Finset.mul_sum]
    ring
  rw [hmean] at hweighted
  have hβ := P.β_pos
  nlinarith

/-- Mean dissipated work is nonnegative. -/
theorem meanDissipatedWork_nonneg (P : Protocol (Ω := Ω) n) :
    0 ≤ P.meanDissipatedWork := by
  unfold meanDissipatedWork
  exact sub_nonneg.mpr P.second_law

end Protocol

end Protocol

section Examples

/-- A deterministic distribution concentrated at one state. -/
def FiniteDistribution.dirac {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (x₀ : Ω) :
    FiniteDistribution Ω where
  prob := fun x => if x = x₀ then 1 else 0
  nonneg := by intro x; split <;> positivity
  sum_prob := by simp

/-- The identity Markov kernel. -/
def identityKernel {Ω : Type u} [Fintype Ω] [DecidableEq Ω] : Kernel Ω :=
  fun x => FiniteDistribution.dirac x

@[simp]
theorem identityKernel_apply_self {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (x : Ω) :
    identityKernel x x = 1 := by simp [identityKernel, FiniteDistribution.dirac]

/-- A one-step quench with no state change. It is a useful executable sanity
check: work is the pointwise energy change, and Crooks/Jarzynski follow from the
general theory. -/
noncomputable def deterministicQuenchProtocol
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (β : ℝ) (hβ : 0 < β) (E₀ E₁ : Energy (Ω := Ω)) : Protocol (Ω := Ω) 1 where
  β := β
  β_pos := hβ
  energy := fun t => if t = 0 then E₀ else E₁
  forwardKernel := fun _ => identityKernel
  reverseKernel := fun _ => identityKernel
  localBalance := by
    intro t x y
    fin_cases t
    simp only [Fin.val_zero, zero_add, identityKernel, FiniteDistribution.dirac]
    by_cases hxy : x = y
    · subst y
      simp
    · simp [hxy, Ne.symm hxy]

/-- A concrete two-state energy landscape with levels `0` and `ε`. -/
def twoStateEnergy (ε : ℝ) : Fin 2 → ℝ
  | 0 => 0
  | 1 => ε

/-- Partition function of the two-state landscape. -/
theorem twoState_partitionFunction (β ε : ℝ) :
    partitionFunction β (twoStateEnergy ε) = 1 + Real.exp (-β * ε) := by
  unfold partitionFunction boltzmannWeight
  simp [Fin.sum_univ_two, twoStateEnergy]

end Examples

end CrooksJarzynski
