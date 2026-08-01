/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorRenewal
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorExp
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorFullPath

/-!
# The terminal marginal of a general jump path law is a row of `exp (TQ)`

The two halves of the identification are now in place.  The jump-process side
satisfies a renewal equation in the residual fraction of the horizon, and the
matrix exponential is the unique continuous solution of that same equation.
Matching them identifies the constructed path law with the semigroup generated
by the conservative generator, for an arbitrary finite jump generator.

The statement is phrased against `pathLawFrom` -- the measure actually
constructed -- rather than against the sector sum used in the arithmetic.  The
sector sum is only ever an intermediate evaluation of that measure.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **The real transition mass on a fraction of the horizon is the matrix
exponential at the corresponding time.**  Both sides solve the same renewal
equation in the fraction, and that equation has only one continuous solution. -/
theorem transitionReal_eq_exp
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    G.transitionReal T x y ρ =
      NormedSpace.exp (((T : ℝ) * ρ) • G.generator) x y :=
  G.eq_exp_smul_apply_of_renewal_fraction (G.transitionReal T) T 1
    (fun x y => G.continuous_transitionReal T x y)
    (fun x y _ hρ => G.transitionReal_renewal T x y hρ.1 hρ.2) x y ρ ⟨h0, h1⟩

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The transition mass over the full horizon is the corresponding entry of
`exp (TQ)`. -/
theorem transitionMass_toReal_eq_exp
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    (G.transitionMass T x y).toReal =
      NormedSpace.exp ((T : ℝ) • G.generator) x y := by
  have h := G.transitionReal_eq_exp T x y zero_le_one (le_refl (1 : ℝ))
  rw [G.transitionReal_apply T x y zero_le_one (le_refl (1 : ℝ)),
    G.transitionMassAt_one T x y, mul_one] at h
  exact h

/-- **The terminal marginal of the fixed-initial path law is a row of
`exp (TQ)`.**  This is the general-generator counterpart of the two-state
statement, and it is phrased on the path law itself. -/
theorem pathLawFrom_terminalState_eq_exp_generator
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    ((G.pathLawFrom T x).map FullPath.terminalState).real {y} =
      NormedSpace.exp ((T : ℝ) • G.generator) x y := by
  rw [measureReal_def, G.pathLawFrom_terminalState_singleton T x y]
  exact G.transitionMass_toReal_eq_exp T x y

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
