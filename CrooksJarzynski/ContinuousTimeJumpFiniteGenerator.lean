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

This module packages the state-independent data that were previously implicit
in the concrete two-state examples. A `FiniteJumpGenerator` consists of a
nonnegative off-diagonal jump-rate function on a finite state space. Its escape
rates and real conservative generator matrix are derived canonically, so every
row of the resulting matrix sums to zero.

For fixed-jump-count paths, counting measure on finite state sequences is the
canonical common state reference. Combining it with the fixed-horizon simplex
construction gives a finite, reversal-invariant reference that does not choose
a deterministic successor at each jump and therefore supports genuine
branching.

The final namespace instantiates the construction for a symmetric three-state
Y-shaped chain. From the central state, the chain can jump to either leaf; the
central escape rate is two, while each leaf has escape rate one.
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

/-- Nonnegative off-diagonal jump rates on a finite state space.

The diagonal rate is required to vanish. The conservative real generator is
then obtained by placing the negative total escape rate on the diagonal. -/
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

/-- The real conservative generator associated with the nonnegative jump
rates. -/
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

/-- Every off-diagonal entry of the real generator is nonnegative. -/
theorem generator_offDiagonal_nonneg (G : FiniteJumpGenerator Ω)
    {x y : Ω} (h : y ≠ x) :
    0 ≤ G.generator x y := by
  rw [G.generator_apply_of_ne h]
  positivity

/-- A real matrix is a conservative finite-state jump generator when its
off-diagonal entries are nonnegative and every row sums to zero. -/
def IsConservative (Q : Matrix Ω Ω ℝ) : Prop :=
  (∀ x y, y ≠ x → 0 ≤ Q x y) ∧
    ∀ x, ∑ y, Q x y = 0

/-- Every row of the canonically associated generator sums to zero. -/
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
  rw [hoff, Finset.sum_erase Finset.univ (G.jumpRate_self x)]
  simp [escapeRate]

/-- The matrix derived from nonnegative jump rates is conservative. -/
theorem generator_isConservative (G : FiniteJumpGenerator Ω) :
    IsConservative G.generator := by
  refine ⟨?_, G.generator_row_sum⟩
  intro x y h
  exact G.generator_offDiagonal_nonneg h

/-- The time-homogeneous escape-rate family used by the generic path-density
layer. -/
def pathEscapeRate (G : FiniteJumpGenerator Ω) {n : ℕ} :
    Fin (n + 1) → Ω → NNReal :=
  fun _ x => G.escapeRate x

/-- The time-homogeneous jump-rate family used by the generic path-density
layer. -/
def pathJumpRate (G : FiniteJumpGenerator Ω) {n : ℕ} :
    Fin n → Ω → Ω → NNReal :=
  fun _ x y => G.jumpRate x y

variable [MeasurableSpace Ω]

/-- Counting measure on all finite state sequences in the `n`-jump sector.

Unlike the deterministic alternating reference of the two-state example, this
reference retains every possible branch. Forbidden transitions are removed by
zero jump-rate factors in the path density rather than by the reference. -/
noncomputable def stateSequenceCountingReference
    (G : FiniteJumpGenerator Ω) (n : ℕ) :
    Measure (Fin (n + 1) → Ω) :=
  Measure.count

variable [MeasurableSingletonClass Ω]

/-- Every individual finite state sequence has unit counting mass. -/
@[simp]
theorem stateSequenceCountingReference_singleton
    (G : FiniteJumpGenerator Ω) (n : ℕ)
    (states : Fin (n + 1) → Ω) :
    G.stateSequenceCountingReference n {states} = 1 := by
  exact Measure.count_singleton states

/-- The canonical fixed-horizon counting reference for finite-state jump paths.

The holding times use the simplex probability, while the state sequence uses
counting measure. The resulting reference is finite because the state space is
finite, and it is reversal invariant by the simplex symmetrization. -/
noncomputable def countingReference
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    Measure (JumpPath Ω n) :=
  Simplex.pathProbability T (G.stateSequenceCountingReference n)

/-- The fixed-horizon counting reference is invariant under path reversal. -/
theorem map_countingReference_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    (G.countingReference T n).map JumpPath.reverse =
      G.countingReference T n := by
  exact Simplex.map_pathProbability_reverse T
    (G.stateSequenceCountingReference n)

/-- The fixed-horizon counting reference is supported on paths of duration
exactly `T`. -/
theorem countingReference_ae_horizon
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.countingReference T n,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  exact Simplex.pathProbability_ae_horizon T
    (G.stateSequenceCountingReference n)

namespace ThreeStateBranching

/-- The central state and the two leaves of the Y-shaped example. -/
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

/-- The central state has two available unit-rate branches. -/
@[simp]
theorem escapeRate_center :
    model.escapeRate .center = 2 := by
  simp [FiniteJumpGenerator.escapeRate, model, jumpRate, state_univ]

/-- The left leaf has one unit-rate edge back to the center. -/
@[simp]
theorem escapeRate_left :
    model.escapeRate .left = 1 := by
  simp [FiniteJumpGenerator.escapeRate, model, jumpRate, state_univ]

/-- The right leaf has one unit-rate edge back to the center. -/
@[simp]
theorem escapeRate_right :
    model.escapeRate .right = 1 := by
  simp [FiniteJumpGenerator.escapeRate, model, jumpRate, state_univ]

/-- The model has two distinct positive-rate successors from the central state. -/
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
    simp [FiniteJumpGenerator.generator, escapeRate_center,
      escapeRate_left, escapeRate_right, model, jumpRate]

/-- The three-state generator is conservative. -/
theorem generator_isConservative :
    IsConservative model.generator :=
  model.generator_isConservative

/-- The three-state fixed-horizon path reference counts every state sequence. -/
noncomputable def sectorReference (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  model.countingReference T n

/-- The three-state counting reference is reversal invariant. -/
theorem map_sectorReference_reverse (T : NNReal) (n : ℕ) :
    (sectorReference T n).map JumpPath.reverse = sectorReference T n := by
  exact model.map_countingReference_reverse T n

/-- The three-state counting reference is supported on the physical horizon. -/
theorem sectorReference_ae_horizon (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂sectorReference T n,
      γ ∈ JumpPath.horizonSet (Ω := State) (n := n) T := by
  exact model.countingReference_ae_horizon T n

end ThreeStateBranching
end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
