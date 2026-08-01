/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpSimplex
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Finite-state continuous-time jump generators

A `FiniteJumpGenerator` stores nonnegative finite-state jump rates with a zero
diagonal. The escape rates and conservative real generator are derived from
those rates. Counting measure on finite state sequences, combined with the
fixed-horizon simplex construction, gives a canonical reference that supports
branching. A symmetric three-state Y chain is included as an example.
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

/-- Nonnegative off-diagonal jump rates on a finite state space. -/
structure FiniteJumpGenerator (Ω : Type u) [Fintype Ω] where
  jumpRate : Ω → Ω → NNReal
  jumpRate_self : ∀ x, jumpRate x x = 0

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω]

@[simp]
theorem jumpRate_self_apply (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.jumpRate x x = 0 :=
  G.jumpRate_self x

/-- The total rate of leaving a state. -/
def escapeRate (G : FiniteJumpGenerator Ω) (x : Ω) : NNReal :=
  ∑ y, G.jumpRate x y

variable [DecidableEq Ω]

/-- The real conservative generator associated with the jump rates. -/
def generator (G : FiniteJumpGenerator Ω) : Matrix Ω Ω ℝ :=
  fun x y => if y = x then -(G.escapeRate x : ℝ) else G.jumpRate x y

@[simp]
theorem generator_apply_self (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.generator x x = -(G.escapeRate x : ℝ) := by
  simp [generator]

@[simp]
theorem generator_apply_of_ne (G : FiniteJumpGenerator Ω) {x y : Ω}
    (h : y ≠ x) :
    G.generator x y = (G.jumpRate x y : ℝ) := by
  simp [generator, h]

/-- Every off-diagonal generator entry is nonnegative. -/
theorem generator_offDiagonal_nonneg (G : FiniteJumpGenerator Ω)
    {x y : Ω} (h : y ≠ x) :
    0 ≤ G.generator x y := by
  rw [G.generator_apply_of_ne h]
  positivity

/-- Off-diagonal nonnegativity together with zero row sums. -/
def IsConservative (Q : Matrix Ω Ω ℝ) : Prop :=
  (∀ x y, y ≠ x → 0 ≤ Q x y) ∧
    ∀ x, ∑ y, Q x y = 0

/-- Every row of the associated real generator sums to zero. -/
theorem generator_row_sum (G : FiniteJumpGenerator Ω) (x : Ω) :
    ∑ y, G.generator x y = 0 := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun y => G.generator x y) (Finset.mem_univ x)]
  rw [G.generator_apply_self]
  have hoff :
      (∑ y ∈ Finset.univ.erase x, G.generator x y) =
        ∑ y ∈ Finset.univ.erase x, (G.jumpRate x y : ℝ) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact G.generator_apply_of_ne (Finset.ne_of_mem_erase hy)
  rw [hoff]
  have hsum :
      (∑ y ∈ Finset.univ.erase x, (G.jumpRate x y : ℝ)) =
        ∑ y, (G.jumpRate x y : ℝ) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun y => (G.jumpRate x y : ℝ)) (Finset.mem_univ x)]
    simp
  rw [hsum]
  simp [escapeRate]

/-- The derived matrix is conservative. -/
theorem generator_isConservative (G : FiniteJumpGenerator Ω) :
    IsConservative G.generator := by
  refine ⟨?_, G.generator_row_sum⟩
  intro x y h
  exact G.generator_offDiagonal_nonneg h

/-- The time-homogeneous escape-rate family for path densities. -/
def pathEscapeRate (G : FiniteJumpGenerator Ω) {n : ℕ} :
    Fin (n + 1) → Ω → NNReal :=
  fun _ x => G.escapeRate x

/-- The time-homogeneous jump-rate family for path densities. -/
def pathJumpRate (G : FiniteJumpGenerator Ω) {n : ℕ} :
    Fin n → Ω → Ω → NNReal :=
  fun _ x y => G.jumpRate x y

variable [MeasurableSpace Ω]

/-- Counting measure on all finite state sequences in one jump-count sector. -/
noncomputable def stateSequenceCountingReference
    (_G : FiniteJumpGenerator Ω) (n : ℕ) :
    Measure (Fin (n + 1) → Ω) :=
  Measure.count

/-- The physical `n`-jump holding-time volume `T^n / n!`, expressed through
the free-coordinate simplex volume. -/
noncomputable def simplexSectorMass (T : NNReal) (n : ℕ) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n *
    (volume : Measure (Fin n → I)) (Simplex.freeSimplexSet n)

/-- The physical sector mass evaluates to `T^n / n!`. -/
theorem simplexSectorMass_eq (T : NNReal) (n : ℕ) :
    simplexSectorMass T n =
      (T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  unfold simplexSectorMass
  rw [Simplex.volume_freeSimplexSet]

/-- Counting state sequences combined with the fixed-horizon simplex law,
scaled by the physical holding-time volume `T^n / n!` of the sector. -/
noncomputable def countingReference
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    Measure (JumpPath Ω n) :=
  Simplex.reference T (G.stateSequenceCountingReference n)
    (simplexSectorMass T n)

omit [DecidableEq Ω] in
/-- The counting reference is invariant under path reversal. -/
theorem map_countingReference_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    (G.countingReference T n).map JumpPath.reverse =
      G.countingReference T n := by
  exact Simplex.map_reference_reverse T
    (G.stateSequenceCountingReference n) (simplexSectorMass T n)

omit [DecidableEq Ω] in
/-- The counting reference is supported on paths of duration `T`. -/
theorem countingReference_ae_horizon
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.countingReference T n,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  exact Simplex.reference_ae_horizon T
    (G.stateSequenceCountingReference n) (simplexSectorMass T n)

variable [MeasurableSingletonClass Ω]

omit [DecidableEq Ω] in
/-- Every state sequence has unit counting mass. -/
@[simp]
theorem stateSequenceCountingReference_singleton
    (G : FiniteJumpGenerator Ω) (n : ℕ)
    (states : Fin (n + 1) → Ω) :
    G.stateSequenceCountingReference n {states} = 1 := by
  exact Measure.count_singleton states

namespace ThreeStateBranching

/-- The central state and two leaves of the Y chain. -/
inductive State
  | center
  | left
  | right
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace State := ⊤

/-- Symmetric unit rates along the two edges of the Y graph. -/
def jumpRate : State → State → NNReal
  | .center, .left => 1
  | .left, .center => 1
  | .center, .right => 1
  | .right, .center => 1
  | _, _ => 0

/-- The three-state branching generator. -/
def model : FiniteJumpGenerator State where
  jumpRate := jumpRate
  jumpRate_self := by
    intro x
    cases x <;> rfl

private theorem state_univ :
    (Finset.univ : Finset State) = {.center, .left, .right} := by
  decide

@[simp]
theorem model_jumpRate (x y : State) :
    model.jumpRate x y = jumpRate x y :=
  rfl

@[simp]
theorem escapeRate_center : model.escapeRate .center = 2 := by
  simp [FiniteJumpGenerator.escapeRate, model, jumpRate, state_univ]
  norm_num

@[simp]
theorem escapeRate_left : model.escapeRate .left = 1 := by
  simp [FiniteJumpGenerator.escapeRate, model, jumpRate, state_univ]

@[simp]
theorem escapeRate_right : model.escapeRate .right = 1 := by
  simp [FiniteJumpGenerator.escapeRate, model, jumpRate, state_univ]

/-- The center has two distinct positive-rate successors. -/
theorem has_two_distinct_successors :
    ∃ y z : State,
      y ≠ z ∧ 0 < model.jumpRate .center y ∧
        0 < model.jumpRate .center z := by
  refine ⟨.left, .right, by decide, ?_, ?_⟩ <;>
    norm_num [model, jumpRate]

/-- The Y-shaped jump rates are symmetric. -/
theorem jumpRate_symm (x y : State) :
    model.jumpRate x y = model.jumpRate y x := by
  cases x <;> cases y <;> rfl

/-- The real generator of the Y-shaped model is symmetric. -/
theorem generator_symm (x y : State) :
    model.generator x y = model.generator y x := by
  cases x <;> cases y <;>
    simp [FiniteJumpGenerator.generator, model, jumpRate]

/-- The three-state generator is conservative. -/
theorem generator_isConservative :
    IsConservative model.generator :=
  model.generator_isConservative

/-- The three-state fixed-horizon counting reference. -/
noncomputable def sectorReference (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  model.countingReference T n

/-- The three-state reference is reversal invariant. -/
theorem map_sectorReference_reverse (T : NNReal) (n : ℕ) :
    (sectorReference T n).map JumpPath.reverse = sectorReference T n := by
  exact model.map_countingReference_reverse T n

/-- The three-state reference is supported on the physical horizon. -/
theorem sectorReference_ae_horizon (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂sectorReference T n,
      γ ∈ JumpPath.horizonSet (Ω := State) (n := n) T := by
  exact model.countingReference_ae_horizon T n

end ThreeStateBranching
end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
