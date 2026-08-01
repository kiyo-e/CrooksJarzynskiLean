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

end MatrixNorm

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
