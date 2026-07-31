/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteGenerator
import CrooksJarzynski.ContinuousTimeJumpTwoStateNormalization

/-!
# The two-state chain as a finite jump generator

This module identifies the conservative matrix used by the normalized
unit-rate two-state CTMC with the matrix canonically derived from a
`FiniteJumpGenerator`. It records that the former two-state-specific row-sum
calculation is an instance of the general finite-state theorem.
-/

open scoped BigOperators Matrix

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- The unit-rate two-state chain packaged as a general finite jump generator. -/
def finiteGenerator : FiniteJumpGenerator State where
  jumpRate := generatorRate
  jumpRate_self := by
    intro x
    cases x <;> rfl

@[simp]
theorem finiteGenerator_jumpRate (x y : State) :
    finiteGenerator.jumpRate x y = generatorRate x y :=
  rfl

private theorem state_univ :
    (Finset.univ : Finset State) = {.zero, .one} := by
  decide

/-- The abstract escape-rate construction recovers the unit escape rate. -/
@[simp]
theorem finiteGenerator_escapeRate (x : State) :
    finiteGenerator.escapeRate x = 1 := by
  cases x <;>
    simp [FiniteJumpGenerator.escapeRate, finiteGenerator,
      generatorRate, flip, state_univ]

/-- The abstract conservative generator agrees entrywise with the matrix used
by the two-state semigroup development. -/
theorem finiteGenerator_generator_apply (x y : State) :
    finiteGenerator.generator x y = generator x y := by
  cases x <;> cases y <;>
    simp [FiniteJumpGenerator.generator, finiteGenerator_escapeRate,
      generator, generatorRate, flip]

/-- Matrix-level identification of the concrete and abstract generators. -/
theorem finiteGenerator_generator_eq :
    finiteGenerator.generator =
      (show Matrix State State ℝ from fun x y => generator x y) := by
  ext x y
  exact finiteGenerator_generator_apply x y

/-- The existing two-state row-sum statement follows directly from the general
finite-state generator theorem. -/
theorem generator_row_sum_via_finiteGenerator (x : State) :
    ∑ y : State, generator x y = 0 := by
  calc
    (∑ y : State, generator x y) =
        ∑ y : State, finiteGenerator.generator x y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact (finiteGenerator_generator_apply x y).symm
    _ = 0 := finiteGenerator.generator_row_sum x

/-- The concrete two-state matrix satisfies the general conservative-generator
predicate. -/
theorem generator_isConservative :
    FiniteJumpGenerator.IsConservative
      (show Matrix State State ℝ from fun x y => generator x y) := by
  rw [← finiteGenerator_generator_eq]
  exact finiteGenerator.generator_isConservative

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
