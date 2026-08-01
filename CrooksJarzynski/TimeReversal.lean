/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Protocol

/-!
# Time reversal, discrete-time work conventions, and work distributions

This module makes the reverse experiment explicit. The forward protocol uses
"quench, then transition" steps. Its physical time reverse therefore uses
"transition, then quench" steps with the energy schedule and kernels read in
reverse chronological order.

The module also proves Crooks' theorem after coarse-graining trajectories to
work values.
-/

open scoped BigOperators

namespace CrooksJarzynski

universe u

namespace Trajectory

variable {Ω : Type u}

/-- The state occupied at every vertex of a finite trajectory. -/
def stateAt : {n : ℕ} → Trajectory Ω n → Fin (n + 1) → Ω
  | 0, (x, _) => fun _ => x
  | _ + 1, (x, tail) => Fin.cons x (stateAt tail)

/-- Build a trajectory from its state at every time vertex. -/
def ofFn : {n : ℕ} → (Fin (n + 1) → Ω) → Trajectory Ω n
  | 0, f => (f 0, PUnit.unit)
  | _ + 1, f => (f 0, ofFn (fun i => f i.succ))

@[simp]
theorem stateAt_ofFn {n : ℕ} (f : Fin (n + 1) → Ω) :
    stateAt (ofFn f) = f := by
  induction n with
  | zero =>
      funext i
      fin_cases i
      rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih (fun k => f k.succ)) j

@[simp]
theorem ofFn_stateAt {n : ℕ} (γ : Trajectory Ω n) :
    ofFn (stateAt γ) = γ := by
  induction n with
  | zero =>
      rcases γ with ⟨x, c⟩
      cases c
      rfl
  | succ n ih =>
      rcases γ with ⟨x, tail⟩
      change (x, ofFn (stateAt tail)) = (x, tail)
      rw [ih tail]
      rfl

@[ext]
theorem ext {n : ℕ} {γ δ : Trajectory Ω n}
    (h : ∀ i, stateAt γ i = stateAt δ i) : γ = δ := by
  rw [← ofFn_stateAt γ, ← ofFn_stateAt δ]
  apply congrArg ofFn
  funext i
  exact h i

/-- Reverse the order of all states in a trajectory. -/
def reverse {n : ℕ} (γ : Trajectory Ω n) : Trajectory Ω n :=
  ofFn fun i => stateAt γ i.rev

@[simp]
theorem stateAt_reverse {n : ℕ} (γ : Trajectory Ω n) (i : Fin (n + 1)) :
    stateAt (reverse γ) i = stateAt γ i.rev := by
  simp [reverse]

@[simp]
theorem reverse_reverse {n : ℕ} (γ : Trajectory Ω n) :
    reverse (reverse γ) = γ := by
  apply ext
  intro i
  simp

/-- Trajectory reversal as an involutive equivalence. -/
def reverseEquiv (Ω : Type u) (n : ℕ) :
    Trajectory Ω n ≃ Trajectory Ω n where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

@[simp]
theorem stateAt_zero {n : ℕ} (γ : Trajectory Ω n) :
    stateAt γ 0 = γ.1 := by
  cases n with
  | zero =>
      rcases γ with ⟨x, c⟩
      rfl
  | succ n =>
      rcases γ with ⟨x, tail⟩
      rfl

@[simp]
theorem stateAt_last {n : ℕ} (γ : Trajectory Ω n) :
    stateAt γ (Fin.last n) = finalState γ.1 γ.2 := by
  induction n with
  | zero =>
      rcases γ with ⟨x, c⟩
      cases c
      rfl
  | succ n ih =>
      rcases γ with ⟨x, tail⟩
      change stateAt tail (Fin.last n) = finalState tail.1 tail.2
      exact ih tail

@[simp]
theorem reverse_fst {n : ℕ} (γ : Trajectory Ω n) :
    (reverse γ).1 = finalState γ.1 γ.2 := by
  rw [← stateAt_zero (reverse γ), stateAt_reverse]
  simp

@[simp]
theorem finalState_reverse {n : ℕ} (γ : Trajectory Ω n) :
    finalState (reverse γ).1 (reverse γ).2 = γ.1 := by
  rw [← stateAt_last (reverse γ), stateAt_reverse]
  simp

/-- Reversal exchanges the left vertex of an edge with the right vertex of the
reversed edge. -/
@[simp]
theorem rev_castSucc_edge {n : ℕ} (i : Fin n) :
    (i.castSucc : Fin (n + 1)).rev = i.rev.succ :=
  Fin.rev_castSucc i

/-- Reversal exchanges the right vertex of an edge with the left vertex of the
reversed edge. -/
@[simp]
theorem rev_succ_edge {n : ℕ} (i : Fin n) :
    (i.succ : Fin (n + 1)).rev = i.rev.castSucc :=
  Fin.rev_succ i

variable [Fintype Ω]

/-- Transition probability product written using the state-at-time view. -/
noncomputable def transitionProduct {n : ℕ}
    (K : Fin n → Kernel Ω) (γ : Trajectory Ω n) : ℝ :=
  ∏ t : Fin n, K t (stateAt γ t.castSucc) (stateAt γ t.succ)

/-- Backward transition probability product along a forward-oriented path. -/
noncomputable def reverseTransitionProduct {n : ℕ}
    (K : Fin n → Kernel Ω) (γ : Trajectory Ω n) : ℝ :=
  ∏ t : Fin n, K t (stateAt γ t.succ) (stateAt γ t.castSucc)

/-- The recursive transition product agrees with the state-at-time product. -/
theorem transitionWeight_eq_transitionProduct {n : ℕ}
    (K : Fin n → Kernel Ω) (γ : Trajectory Ω n) :
    transitionWeight K γ.1 γ.2 = transitionProduct K γ := by
  induction n with
  | zero =>
      rcases γ with ⟨x, c⟩
      cases c
      simp [transitionWeight, transitionProduct]
  | succ n ih =>
      rcases γ with ⟨x, ⟨y, rest⟩⟩
      calc
        transitionWeight K x (y, rest) =
            K 0 x y * transitionWeight (fun i => K i.succ) y rest := rfl
        _ = K 0 x y * transitionProduct (fun i => K i.succ) (y, rest) := by
              rw [ih (fun i => K i.succ) (y, rest)]
        _ = transitionProduct K (x, (y, rest)) := by
              unfold transitionProduct
              rw [Fin.prod_univ_succ]
              simp [stateAt]

/-- The recursive backward product agrees with the state-at-time product. -/
theorem reverseTransitionWeight_eq_reverseTransitionProduct {n : ℕ}
    (K : Fin n → Kernel Ω) (γ : Trajectory Ω n) :
    reverseTransitionWeight K γ.1 γ.2 = reverseTransitionProduct K γ := by
  induction n with
  | zero =>
      rcases γ with ⟨x, c⟩
      cases c
      simp [reverseTransitionWeight, reverseTransitionProduct]
  | succ n ih =>
      rcases γ with ⟨x, ⟨y, rest⟩⟩
      calc
        reverseTransitionWeight K x (y, rest) =
            K 0 y x * reverseTransitionWeight (fun i => K i.succ) y rest := rfl
        _ = K 0 y x * reverseTransitionProduct (fun i => K i.succ) (y, rest) := by
              rw [ih (fun i => K i.succ) (y, rest)]
        _ = reverseTransitionProduct K (x, (y, rest)) := by
              unfold reverseTransitionProduct
              rw [Fin.prod_univ_succ]
              simp [stateAt]

/-- Reversing both the path and kernel order converts a forward transition
product into the backward product on the original path. -/
theorem transitionProduct_reverse {n : ℕ}
    (K : Fin n → Kernel Ω) (γ : Trajectory Ω n) :
    transitionProduct (fun t => K t.rev) (reverse γ) =
      reverseTransitionProduct K γ := by
  simp only [transitionProduct, reverseTransitionProduct, stateAt_reverse,
    rev_castSucc_edge, rev_succ_edge]
  simpa using
    (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n))
      (fun t : Fin n => K t (stateAt γ t.succ) (stateAt γ t.castSucc)))

end Trajectory

/-- Work assigned to the energy quench before edge `t` is traversed. -/
def Protocol.quenchThenTransitionIncrement
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (P : Protocol Ω n) (γ : Trajectory Ω n) (t : Fin n) : ℝ :=
  P.energy (t.val + 1) (Trajectory.stateAt γ t.castSucc) -
    P.energy t.val (Trajectory.stateAt γ t.castSucc)

/-- Work assigned after the transition across edge `t`, using the same energy
schedule. -/
def Protocol.transitionThenQuenchIncrement
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (P : Protocol Ω n) (γ : Trajectory Ω n) (t : Fin n) : ℝ :=
  P.energy (t.val + 1) (Trajectory.stateAt γ t.succ) -
    P.energy t.val (Trajectory.stateAt γ t.succ)

/-- The alternative transition-then-quench work on the same forward schedule. -/
noncomputable def Protocol.transitionThenQuenchWork
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (P : Protocol Ω n) (γ : Trajectory Ω n) : ℝ :=
  ∑ t : Fin n, P.transitionThenQuenchIncrement γ t

namespace Protocol

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]
variable {n : ℕ}

omit [Fintype Ω] [Nonempty Ω] in
private theorem workAux_eq_sum_quenchThenTransitionIncrement
    {n : ℕ} (E : ℕ → Energy Ω) (x : Ω) (c : Continuation Ω n) :
    workAux E x c =
      ∑ t : Fin n,
        (E (t.val + 1) (Trajectory.stateAt (x, c) t.castSucc) -
          E t.val (Trajectory.stateAt (x, c) t.castSucc)) := by
  induction n generalizing E x with
  | zero =>
      cases c
      simp [workAux]
  | succ n ih =>
      rcases c with ⟨y, rest⟩
      rw [Fin.sum_univ_succ]
      simp only [workAux]
      congr 1
      simpa [Trajectory.stateAt, Nat.add_assoc] using
        ih (fun t => E (t + 1)) y rest

/-- The recursive work definition is the sum of quench-before-transition
increments. -/
theorem work_eq_sum_quenchThenTransitionIncrement
    (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.work γ = ∑ t : Fin n, P.quenchThenTransitionIncrement γ t := by
  rcases γ with ⟨x, c⟩
  unfold work quenchThenTransitionIncrement
  exact workAux_eq_sum_quenchThenTransitionIncrement P.energy x c

/-- Exact difference between the two standard discrete-time work conventions.
The discrepancy is the change, across each transition, of the energy-quench
increment as a function of the occupied state. -/
theorem workConvention_difference (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.transitionThenQuenchWork γ - P.work γ =
      ∑ t : Fin n,
        ((P.energy (t.val + 1) (Trajectory.stateAt γ t.succ) -
            P.energy (t.val + 1) (Trajectory.stateAt γ t.castSucc)) -
          (P.energy t.val (Trajectory.stateAt γ t.succ) -
            P.energy t.val (Trajectory.stateAt γ t.castSucc))) := by
  rw [work_eq_sum_quenchThenTransitionIncrement]
  unfold transitionThenQuenchWork transitionThenQuenchIncrement
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold quenchThenTransitionIncrement
  ring

/-- The two work conventions coincide on a trajectory with no state change. -/
theorem workConvention_eq_of_stationary
    (P : Protocol Ω n) (γ : Trajectory Ω n)
    (hγ : ∀ t : Fin n,
      Trajectory.stateAt γ t.castSucc = Trajectory.stateAt γ t.succ) :
    P.transitionThenQuenchWork γ = P.work γ := by
  rw [work_eq_sum_quenchThenTransitionIncrement]
  unfold transitionThenQuenchWork transitionThenQuenchIncrement
  apply Finset.sum_congr rfl
  intro t _
  rw [← hγ t]
  rfl

end Protocol

/-- A protocol whose step order is transition first and energy quench second.
Its kernel at edge `t` is equilibrated with the energy at the left endpoint of
that edge. -/
structure TransitionThenQuenchProtocol
    (Ω : Type u) [Fintype Ω] (n : ℕ) where
  β : ℝ
  β_pos : 0 < β
  energy : Fin (n + 1) → Energy Ω
  forwardKernel : Fin n → Kernel Ω
  reverseKernel : Fin n → Kernel Ω
  localBalance : ∀ t x y,
    boltzmannWeight β (energy t.castSucc) x * forwardKernel t x y =
      boltzmannWeight β (energy t.castSucc) y * reverseKernel t y x

namespace TransitionThenQuenchProtocol

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]
variable {n : ℕ}

/-- Energy before the first reverse transition. -/
def initialEnergy (R : TransitionThenQuenchProtocol Ω n) : Energy Ω :=
  R.energy 0

/-- Energy after the final reverse quench. -/
def finalEnergy (R : TransitionThenQuenchProtocol Ω n) : Energy Ω :=
  R.energy (Fin.last n)

/-- Free-energy change for a transition-then-quench protocol. -/
noncomputable def deltaFreeEnergy (R : TransitionThenQuenchProtocol Ω n) : ℝ :=
  freeEnergy R.β R.finalEnergy - freeEnergy R.β R.initialEnergy

/-- Work of edge `t`: transition at the old energy, then quench at the newly
occupied state. -/
def workIncrement (R : TransitionThenQuenchProtocol Ω n)
    (γ : Trajectory Ω n) (t : Fin n) : ℝ :=
  R.energy t.succ (Trajectory.stateAt γ t.succ) -
    R.energy t.castSucc (Trajectory.stateAt γ t.succ)

/-- Total transition-then-quench work. -/
noncomputable def work (R : TransitionThenQuenchProtocol Ω n)
    (γ : Trajectory Ω n) : ℝ :=
  ∑ t : Fin n, R.workIncrement γ t

/-- Path probability in the transition-then-quench experiment. -/
noncomputable def forwardWeight (R : TransitionThenQuenchProtocol Ω n)
    (γ : Trajectory Ω n) : ℝ :=
  gibbsProbability R.β R.initialEnergy γ.1 *
    Trajectory.transitionProduct R.forwardKernel γ

/-- Path weights of a transition-then-quench protocol are normalized. -/
theorem sum_forwardWeight (R : TransitionThenQuenchProtocol Ω n) :
    ∑ γ : Trajectory Ω n, R.forwardWeight γ = 1 := by
  unfold forwardWeight
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Ω, ∑ c : Continuation Ω n,
        gibbsProbability R.β R.initialEnergy x *
          Trajectory.transitionProduct R.forwardKernel (x, c)) =
        ∑ x : Ω, gibbsProbability R.β R.initialEnergy x *
          (∑ c : Continuation Ω n,
            transitionWeight R.forwardKernel x c) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          rw [← Trajectory.transitionWeight_eq_transitionProduct]
    _ = ∑ x : Ω, gibbsProbability R.β R.initialEnergy x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sum_transitionWeight]
          simp
    _ = 1 := sum_gibbsProbability _ _

/-- Probability mass of an exact work value in a transition-then-quench
experiment. -/
noncomputable def workProbability (R : TransitionThenQuenchProtocol Ω n)
    (w : ℝ) : ℝ := by
  classical
  exact ∑ γ : Trajectory Ω n, if R.work γ = w then R.forwardWeight γ else 0

end TransitionThenQuenchProtocol

namespace Protocol

variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]
variable {n : ℕ}

/-- The physical time reverse of a quench-then-transition protocol. It starts
at the final energy, traverses the reverse kernels in reverse chronological
order, and quenches only after each reverse transition. -/
def reverseProtocol (P : Protocol Ω n) : TransitionThenQuenchProtocol Ω n where
  β := P.β
  β_pos := P.β_pos
  energy := fun t => P.energy t.rev.val
  forwardKernel := fun t => P.reverseKernel t.rev
  reverseKernel := fun t => P.forwardKernel t.rev
  localBalance := by
    intro t x y
    simpa [Fin.rev_castSucc] using (P.localBalance t.rev y x).symm

omit [Nonempty Ω] in
@[simp]
theorem reverseProtocol_initialEnergy (P : Protocol Ω n) :
    P.reverseProtocol.initialEnergy = P.finalEnergy := by
  simp [reverseProtocol, TransitionThenQuenchProtocol.initialEnergy, finalEnergy]

omit [Nonempty Ω] in
@[simp]
theorem reverseProtocol_finalEnergy (P : Protocol Ω n) :
    P.reverseProtocol.finalEnergy = P.initialEnergy := by
  simp [reverseProtocol, TransitionThenQuenchProtocol.finalEnergy, initialEnergy]

omit [Nonempty Ω] in
@[simp]
theorem reverseProtocol_deltaFreeEnergy (P : Protocol Ω n) :
    P.reverseProtocol.deltaFreeEnergy = -P.deltaFreeEnergy := by
  unfold TransitionThenQuenchProtocol.deltaFreeEnergy deltaFreeEnergy
  rw [reverseProtocol_initialEnergy, reverseProtocol_finalEnergy]
  change freeEnergy P.β P.initialEnergy - freeEnergy P.β P.finalEnergy =
    -(freeEnergy P.β P.finalEnergy - freeEnergy P.β P.initialEnergy)
  ring

omit [Nonempty Ω] in
/-- The explicit reverse protocol assigns exactly `reverseWeight` to the
reversed trajectory. -/
@[simp]
theorem reverseProtocol_forwardWeight_reverse
    (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.reverseProtocol.forwardWeight (Trajectory.reverse γ) = P.reverseWeight γ := by
  unfold TransitionThenQuenchProtocol.forwardWeight reverseWeight
  rw [reverseProtocol_initialEnergy, Trajectory.reverse_fst]
  change gibbsProbability P.β P.finalEnergy (finalState γ.1 γ.2) *
      Trajectory.transitionProduct (fun t => P.reverseKernel t.rev)
        (Trajectory.reverse γ) =
    gibbsProbability P.β P.finalEnergy (finalState γ.1 γ.2) *
      reverseTransitionWeight P.reverseKernel γ.1 γ.2
  rw [Trajectory.transitionProduct_reverse]
  rw [← Trajectory.reverseTransitionWeight_eq_reverseTransitionProduct]

/-- Reversing a quench-then-transition step gives a transition-then-quench step
with the opposite work increment. -/
theorem reverseProtocol_workIncrement_reverse
    (P : Protocol Ω n) (γ : Trajectory Ω n) (t : Fin n) :
    P.reverseProtocol.workIncrement (Trajectory.reverse γ) t =
      -P.quenchThenTransitionIncrement γ t.rev := by
  unfold reverseProtocol TransitionThenQuenchProtocol.workIncrement
    quenchThenTransitionIncrement
  simp only [Trajectory.stateAt_reverse, Trajectory.rev_succ_edge,
    Trajectory.rev_castSucc_edge]
  change
    P.energy t.rev.val (Trajectory.stateAt γ t.rev.castSucc) -
        P.energy (t.rev.val + 1) (Trajectory.stateAt γ t.rev.castSucc) =
      -(P.energy (t.rev.val + 1) (Trajectory.stateAt γ t.rev.castSucc) -
        P.energy t.rev.val (Trajectory.stateAt γ t.rev.castSucc))
  ring

/-- Work changes sign under the physical reverse protocol. This theorem also
records why the reverse experiment must use the transition-then-quench
convention. -/
@[simp]
theorem reverseProtocol_work_reverse
    (P : Protocol Ω n) (γ : Trajectory Ω n) :
    P.reverseProtocol.work (Trajectory.reverse γ) = -P.work γ := by
  unfold TransitionThenQuenchProtocol.work
  calc
    (∑ t : Fin n,
        P.reverseProtocol.workIncrement (Trajectory.reverse γ) t) =
        ∑ t : Fin n, -P.quenchThenTransitionIncrement γ t.rev := by
          apply Finset.sum_congr rfl
          intro t _
          rw [P.reverseProtocol_workIncrement_reverse γ t]
    _ = ∑ t : Fin n, -P.quenchThenTransitionIncrement γ t := by
          simpa using
            (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
              (fun t : Fin n => -P.quenchThenTransitionIncrement γ t))
    _ = -(∑ t : Fin n, P.quenchThenTransitionIncrement γ t) := by
          rw [Finset.sum_neg_distrib]
    _ = -P.work γ := by
          rw [P.work_eq_sum_quenchThenTransitionIncrement γ]

/-- Probability mass of an exact work value in the forward experiment. -/
noncomputable def workProbability (P : Protocol Ω n) (w : ℝ) : ℝ := by
  classical
  exact ∑ γ : Trajectory Ω n, if P.work γ = w then P.forwardWeight γ else 0

/-- Reindex the reverse work distribution by forward-oriented trajectories. -/
theorem reverseProtocol_workProbability (P : Protocol Ω n) (w : ℝ) :
    P.reverseProtocol.workProbability w =
      ∑ γ : Trajectory Ω n,
        if -P.work γ = w then P.reverseWeight γ else 0 := by
  classical
  unfold TransitionThenQuenchProtocol.workProbability
  calc
    (∑ δ : Trajectory Ω n,
        if P.reverseProtocol.work δ = w then
          P.reverseProtocol.forwardWeight δ else 0) =
        ∑ γ : Trajectory Ω n,
          if P.reverseProtocol.work (Trajectory.reverse γ) = w then
            P.reverseProtocol.forwardWeight (Trajectory.reverse γ) else 0 := by
          symm
          exact
            Equiv.sum_comp (Trajectory.reverseEquiv Ω n)
              (fun δ : Trajectory Ω n =>
                if P.reverseProtocol.work δ = w then
                  P.reverseProtocol.forwardWeight δ else 0)
    _ = ∑ γ : Trajectory Ω n,
          if -P.work γ = w then P.reverseWeight γ else 0 := by
          apply Finset.sum_congr rfl
          intro γ _
          rw [P.reverseProtocol_work_reverse γ,
            P.reverseProtocol_forwardWeight_reverse γ]

/-- Crooks' theorem for the probability mass of an exact work value. The
multiplicative form remains valid when the reverse work mass is zero. -/
theorem work_distribution_crooks (P : Protocol Ω n) (w : ℝ) :
    P.workProbability w * Real.exp (P.β * P.deltaFreeEnergy) =
      P.reverseProtocol.workProbability (-w) * Real.exp (P.β * w) := by
  classical
  rw [P.reverseProtocol_workProbability]
  unfold workProbability
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ _
  by_cases hwork : P.work γ = w
  · have hreverse : -P.work γ = -w := by rw [hwork]
    simp only [if_pos hwork, if_pos hreverse]
    calc
      P.forwardWeight γ * Real.exp (P.β * P.deltaFreeEnergy) =
          P.reverseWeight γ * Real.exp (P.β * P.work γ) := P.crooks γ
      _ = P.reverseWeight γ * Real.exp (P.β * w) := by rw [hwork]
  · have hreverse : -P.work γ ≠ -w := by
      intro h
      apply hwork
      linarith
    simp [hwork, hreverse]

/-- Ratio form of Crooks' work-distribution theorem. -/
theorem work_distribution_crooks_ratio
    (P : Protocol Ω n) (w : ℝ)
    (hR : P.reverseProtocol.workProbability (-w) ≠ 0) :
    P.workProbability w / P.reverseProtocol.workProbability (-w) =
      Real.exp (P.β * (w - P.deltaFreeEnergy)) := by
  have hexp :
      Real.exp (P.β * (w - P.deltaFreeEnergy)) =
        Real.exp (P.β * w) / Real.exp (P.β * P.deltaFreeEnergy) := by
    rw [show P.β * (w - P.deltaFreeEnergy) =
      P.β * w - P.β * P.deltaFreeEnergy by ring, Real.exp_sub]
  rw [hexp]
  apply (div_eq_div_iff hR (Real.exp_ne_zero _)).2
  simpa [mul_comm] using P.work_distribution_crooks w

end Protocol

end CrooksJarzynski
