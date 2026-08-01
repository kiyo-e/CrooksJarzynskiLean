/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorPathLaw
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral form of the matrix exponential

The exponential of a generator satisfies the integral equation obtained from
its own derivative.  This is the half of the `exp (TQ)` identification that
lives entirely in real matrices; the jump-process side is a separate renewal
equation, and the two are matched afterwards.

Matrices carry no canonical norm, so the `ℓ∞` operator norm is installed as a
local instance here.  Keeping this module separate stops that choice from
leaking into the measure-theoretic development.
-/

open MeasureTheory
open scoped Matrix

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- The exponential curve of a fixed matrix has derivative `Q * exp (t • Q)`. -/
theorem hasDerivAt_exp_smul (Q : Matrix Ω Ω ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Q))
      (Q * NormedSpace.exp (t • Q)) t :=
  hasDerivAt_exp_smul_const' Q t

/-- **Integral form of the matrix exponential.**  Integrating its own
derivative recovers `exp (TQ)` from the identity. -/
theorem exp_smul_eq_one_add_integral (Q : Matrix Ω Ω ℝ) (T : ℝ) :
    NormedSpace.exp (T • Q) =
      1 + ∫ s in (0 : ℝ)..T, Q * NormedSpace.exp (s • Q) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Q))
        (Q * NormedSpace.exp (s • Q)) s :=
    fun s _ => hasDerivAt_exp_smul Q s
  have hcont : ContinuousOn (fun s : ℝ => Q * NormedSpace.exp (s • Q))
      (Set.uIcc (0 : ℝ) T) := by
    apply Continuous.continuousOn
    exact continuous_const.mul
      ((NormedSpace.exp_continuous (𝔸 := Matrix Ω Ω ℝ)).comp
        (continuous_id.smul continuous_const))
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  rw [hsub]
  simp

/-- Reading off one entry is a bounded linear functional for the `ℓ∞` operator
norm, since an entry is dominated by its own row sum. -/
noncomputable def entryCLM (x y : Ω) : Matrix Ω Ω ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun M => M x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (by
      intro M
      rw [one_mul]
      calc
        ‖M x y‖ ≤ ∑ j, ‖M x j‖ :=
          Finset.single_le_sum (f := fun j => ‖M x j‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
        _ ≤ ‖M‖ := by
          rw [Matrix.linfty_opNorm_def,
            show (∑ j, ‖M x j‖) = ((∑ j, ‖M x j‖₊ : NNReal) : ℝ) by push_cast; rfl]
          exact_mod_cast Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊)
            (Finset.mem_univ x))

@[simp]
theorem entryCLM_apply (x y : Ω) (M : Matrix Ω Ω ℝ) :
    entryCLM x y M = M x y := rfl

/-- **Entrywise integral form of the matrix exponential.** -/
theorem exp_smul_apply_eq_add_integral
    (Q : Matrix Ω Ω ℝ) (T : ℝ) (x y : Ω) :
    NormedSpace.exp (T • Q) x y =
      (1 : Matrix Ω Ω ℝ) x y +
        ∫ s in (0 : ℝ)..T, (Q * NormedSpace.exp (s • Q)) x y := by
  have hcont : ContinuousOn (fun s : ℝ => Q * NormedSpace.exp (s • Q))
      (Set.uIcc (0 : ℝ) T) := by
    apply Continuous.continuousOn
    exact continuous_const.mul
      ((NormedSpace.exp_continuous (𝔸 := Matrix Ω Ω ℝ)).comp
        (continuous_id.smul continuous_const))
  have hpull :
      (∫ s in (0 : ℝ)..T, (Q * NormedSpace.exp (s • Q)) x y) =
        (∫ s in (0 : ℝ)..T, Q * NormedSpace.exp (s • Q)) x y :=
    (entryCLM x y).intervalIntegral_comp_comm hcont.intervalIntegrable
  rw [hpull, exp_smul_eq_one_add_integral Q T]
  rfl

/-- Splitting the generator into its escape and jump parts.  The diagonal
contributes `-λ(x)` times the entry being left, and the off-diagonal
contributes the jump rates; the `z = x` jump term is zero, so the jump sum can
run over all states.

This is the algebraic input to the renewal equation: the escape term is what
the integrating factor `e^{λ(x) t}` cancels, leaving the jump term as the
integrand. -/
theorem generator_mul_apply
    (G : FiniteJumpGenerator Ω) (M : Matrix Ω Ω ℝ) (x y : Ω) :
    (G.generator * M) x y =
      -(G.escapeRate x : ℝ) * M x y +
        ∑ z, (G.jumpRate x z : ℝ) * M z y := by
  rw [Matrix.mul_apply]
  have hterm : ∀ z : Ω,
      G.generator x z * M z y =
        (if z = x then -(G.escapeRate x : ℝ) * M x y else 0) +
          (G.jumpRate x z : ℝ) * M z y := by
    intro z
    by_cases h : z = x
    · subst h
      simp [FiniteJumpGenerator.generator]
    · simp [FiniteJumpGenerator.generator, h]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ x
    (fun _ => -(G.escapeRate x : ℝ) * M x y)]
  simp

/-- The entrywise derivative of the exponential curve.  This is the one place
that has to cross from the matrix norm to scalars; everything downstream works
with real-valued functions, which keeps the `NormedSpace ℝ ℝ` instance diamond
out of the integrating-factor argument. -/
theorem hasDerivAt_exp_smul_apply (Q : Matrix Ω Ω ℝ) (t : ℝ) (x y : Ω) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Q) x y)
      ((Q * NormedSpace.exp (t • Q)) x y) t :=
  (entryCLM x y).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul Q t)

/-- The rate of arriving at `y` from `x` after one more jump. -/
noncomputable def jumpFlow
    (G : FiniteJumpGenerator Ω) (x y : Ω) (t : ℝ) : ℝ :=
  ∑ z, (G.jumpRate x z : ℝ) * NormedSpace.exp (t • G.generator) z y

theorem continuous_jumpFlow (G : FiniteJumpGenerator Ω) (x y : Ω) :
    Continuous (G.jumpFlow x y) := by
  unfold jumpFlow
  refine continuous_finsetSum _ fun z _ => continuous_const.mul ?_
  exact (entryCLM z y).continuous.comp
    ((NormedSpace.exp_continuous (𝔸 := Matrix Ω Ω ℝ)).comp
      (continuous_id.smul continuous_const))

/-- The integrating factor `e^{λ(x) t}` cancels the escape term, leaving the
jump flow as an exact derivative. -/
theorem hasDerivAt_expScaled
    (G : FiniteJumpGenerator Ω) (x y : Ω) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        Real.exp ((G.escapeRate x : ℝ) * u) *
          NormedSpace.exp (u • G.generator) x y)
      (Real.exp ((G.escapeRate x : ℝ) * t) * G.jumpFlow x y t) t := by
  have hlin : HasDerivAt (fun u : ℝ => (G.escapeRate x : ℝ) * u)
      (G.escapeRate x : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (G.escapeRate x : ℝ)
  have hmul := hlin.exp.mul (hasDerivAt_exp_smul_apply G.generator t x y)
  have hval :
      Real.exp ((G.escapeRate x : ℝ) * t) * G.jumpFlow x y t =
        Real.exp ((G.escapeRate x : ℝ) * t) * (G.escapeRate x : ℝ) *
            NormedSpace.exp (t • G.generator) x y +
          Real.exp ((G.escapeRate x : ℝ) * t) *
            (G.generator * NormedSpace.exp (t • G.generator)) x y := by
    rw [generator_mul_apply]
    unfold jumpFlow
    ring
  rw [hval]
  exact hmul

end MatrixNorm

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
