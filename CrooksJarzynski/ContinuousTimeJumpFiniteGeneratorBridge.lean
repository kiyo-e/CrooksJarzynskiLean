/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorRenewal
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorExp
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorFullPath
import CrooksJarzynski.ContinuousTimeJumpTwoStateFiniteGenerator
import Mathlib.Probability.Kernel.Composition.Comp

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

open MeasureTheory ProbabilityTheory
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

/-! ### The Markov semigroup

Identifying the terminal marginals with `exp (TQ)` turns the semigroup law for
the matrix exponential into Chapman--Kolmogorov for the constructed path laws,
with no further probabilistic input. -/

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem transitionMass_toReal_chapman_kolmogorov
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x y : Ω) :
    (∑ z, (G.transitionMass S x z).toReal * (G.transitionMass T z y).toReal) =
      (G.transitionMass (S + T) x y).toReal := by
  simp only [G.transitionMass_toReal_eq_exp]
  rw [NNReal.coe_add, add_smul,
    Matrix.exp_add_of_commute _ _
      (((Commute.refl G.generator).smul_left (S : ℝ)).smul_right (T : ℝ))]
  exact Matrix.mul_apply.symm

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem transitionMass_ne_top
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    G.transitionMass T x y ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (G.transitionMass_le_one T x y)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **Chapman--Kolmogorov for the transition mass.** -/
theorem transitionMass_chapman_kolmogorov
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x y : Ω) :
    (∑ z, G.transitionMass S x z * G.transitionMass T z y) =
      G.transitionMass (S + T) x y := by
  have hterm : ∀ z : Ω,
      G.transitionMass S x z * G.transitionMass T z y ≠ ∞ := fun z =>
    ENNReal.mul_ne_top (G.transitionMass_ne_top S x z)
      (G.transitionMass_ne_top T z y)
  refine (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.sum_ne_top.2 fun z _ => hterm z)
    (G.transitionMass_ne_top (S + T) x y)).1 ?_
  rw [ENNReal.toReal_sum fun z _ => hterm z]
  simp only [ENNReal.toReal_mul]
  exact G.transitionMass_toReal_chapman_kolmogorov S T x y

/-- The transition kernel of a general finite jump generator: the terminal
marginal of its fixed-initial path law, packaged as a Mathlib kernel. -/
noncomputable def transitionKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) : ProbabilityTheory.Kernel Ω Ω :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x =>
    (G.pathLawFrom T x).map FullPath.terminalState

@[simp]
theorem transitionKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    G.transitionKernel T x = (G.pathLawFrom T x).map FullPath.terminalState :=
  rfl

noncomputable instance instIsMarkovKernelTransitionKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    ProbabilityTheory.IsMarkovKernel (G.transitionKernel T) := by
  constructor
  intro x
  change IsProbabilityMeasure ((G.pathLawFrom T x).map FullPath.terminalState)
  exact Measure.isProbabilityMeasure_map
    FullPath.measurable_terminalState.aemeasurable

theorem transitionKernel_singleton
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    G.transitionKernel T x {y} = G.transitionMass T x y :=
  G.pathLawFrom_terminalState_singleton T x y

/-- **The transition kernel rows are the rows of `exp (TQ)`.** -/
theorem transitionKernel_real_singleton_eq_exp_generator
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    (G.transitionKernel T x).real {y} =
      NormedSpace.exp ((T : ℝ) • G.generator) x y :=
  G.pathLawFrom_terminalState_eq_exp_generator T x y

/-- **Chapman--Kolmogorov for the transition kernel.** -/
theorem transitionKernel_chapman_kolmogorov
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x y : Ω) :
    (∑ z, (G.transitionKernel S x).real {z} *
        (G.transitionKernel T z).real {y}) =
      (G.transitionKernel (S + T) x).real {y} := by
  simp only [measureReal_def, transitionKernel_singleton]
  exact G.transitionMass_toReal_chapman_kolmogorov S T x y

/-- **The terminal laws form a Markov semigroup under Mathlib kernel
composition.**  The rightmost kernel acts first. -/
theorem transitionKernel_add
    (G : FiniteJumpGenerator Ω) (S T : NNReal) :
    G.transitionKernel (S + T) =
      G.transitionKernel T ∘ₖ G.transitionKernel S := by
  symm
  refine ProbabilityTheory.Kernel.ext fun x => Measure.ext_of_singleton fun y => ?_
  rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ (MeasurableSet.singleton y),
    lintegral_fintype]
  simp only [transitionKernel_singleton]
  rw [← G.transitionMass_chapman_kolmogorov S T x y]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-! ### The branching instance

The three-state Y chain is the point of the general construction: it genuinely
branches, so the two-state parity argument cannot reach it, and the identity
below is a consequence of the general theorem rather than of any explicit
diagonalization. -/

namespace ThreeStateBranching

/-- **The Y-shaped chain's terminal marginal is a row of `exp (TQ)`.** -/
theorem pathLawFrom_terminalState_eq_exp_generator (T : NNReal) (x y : State) :
    ((model.pathLawFrom T x).map FullPath.terminalState).real {y} =
      NormedSpace.exp ((T : ℝ) • model.generator) x y :=
  model.pathLawFrom_terminalState_eq_exp_generator T x y

/-- Chapman--Kolmogorov for the branching chain. -/
theorem transitionKernel_chapman_kolmogorov (S T : NNReal) (x y : State) :
    (∑ z, (model.transitionKernel S x).real {z} *
        (model.transitionKernel T z).real {y}) =
      (model.transitionKernel (S + T) x).real {y} :=
  model.transitionKernel_chapman_kolmogorov S T x y

end ThreeStateBranching

end FiniteJumpGenerator

/-! ### Recovering the two-state statement

The general theorem specializes to the normalized two-state chain, whose
generator is the concrete matrix already used by the semigroup development. -/

namespace TwoState

/-- The general identification, transported through the entrywise
identification of the abstract and concrete two-state generators. -/
theorem finiteGenerator_pathLawFrom_terminalState_eq_exp_generator
    (T : NNReal) (x y : State) :
    ((finiteGenerator.pathLawFrom T x).map FullPath.terminalState).real {y} =
      NormedSpace.exp
        ((T : ℝ) •
          (show Matrix State State ℝ from fun x y => generator x y)) x y := by
  rw [← finiteGenerator_generator_eq]
  exact finiteGenerator.pathLawFrom_terminalState_eq_exp_generator T x y

end TwoState

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
