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

/-! ### Uniqueness for the renewal equation

The renewal equation determines its solution, so any other family satisfying it
is forced to agree with the exponential.  Nothing here mentions matrices: the
argument is the standard iterated Volterra estimate, driven by the uniform rate
bound already used for non-explosion. -/

section Volterra

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem sum_jumpRate_real (G : FiniteJumpGenerator Ω) (x : Ω) :
    ∑ z, (G.jumpRate x z : ℝ) = (G.escapeRate x : ℝ) := by
  simp [escapeRate]

omit [DecidableEq Ω] in
theorem escapeRate_le_rateBound_real (G : FiniteJumpGenerator Ω) (x : Ω) :
    (G.escapeRate x : ℝ) ≤ (G.rateBound : ℝ) := by
  exact_mod_cast G.escapeRate_le_rateBound x

omit [DecidableEq Ω] in
/-- **Iterated Volterra bound.**  A bounded continuous family satisfying the
homogeneous renewal equation obeys the factorial bound at every order.  Each
iteration trades one factor of the rate bound for one integration of the
elapsed time, which is what produces the factorial. -/
theorem abs_le_of_homogeneous_renewal
    (G : FiniteJumpGenerator Ω) (D : Ω → Ω → ℝ → ℝ) (C T : ℝ)
    (hcont : ∀ x y, Continuous (D x y))
    (hbdd : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T, |D x y t| ≤ C)
    (hrec : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      D x y t = ∫ s in (0 : ℝ)..t,
        Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s)) :
    ∀ (n : ℕ) (x y : Ω), ∀ t ∈ Set.Icc (0 : ℝ) T,
      |D x y t| ≤ C * ((G.rateBound : ℝ) * t) ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro x y t ht
      simpa using hbdd x y t ht
  | succ n ih =>
      intro x y t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have hgcont : Continuous fun s : ℝ =>
          Real.exp (-(G.escapeRate x : ℝ) * s) *
            ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s) := by
        have h1 : Continuous fun s : ℝ => -(G.escapeRate x : ℝ) * s :=
          continuous_const.mul continuous_id
        refine (Real.continuous_exp.comp h1).mul ?_
        refine continuous_finsetSum _ fun z _ => continuous_const.mul ?_
        exact (hcont z y).comp (continuous_const.sub continuous_id)
      have hhcont : Continuous fun s : ℝ =>
          (G.rateBound : ℝ) *
            (C * ((G.rateBound : ℝ) * (t - s)) ^ n / (n.factorial : ℝ)) := by
        fun_prop
      have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t,
          |Real.exp (-(G.escapeRate x : ℝ) * s) *
              ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s)| ≤
            (G.rateBound : ℝ) *
              (C * ((G.rateBound : ℝ) * (t - s)) ^ n / (n.factorial : ℝ)) := by
        intro s hs
        have hs0 : (0 : ℝ) ≤ s := hs.1
        have hst : s ≤ t := hs.2
        have hts : t - s ∈ Set.Icc (0 : ℝ) T :=
          ⟨by linarith, by linarith [ht.2]⟩
        have hB0 : 0 ≤ C * ((G.rateBound : ℝ) * (t - s)) ^ n /
            (n.factorial : ℝ) := by
          refine le_trans (abs_nonneg (D x y (t - s))) (ih x y (t - s) hts)
        have hsum : |∑ z, (G.jumpRate x z : ℝ) * D z y (t - s)| ≤
            (G.escapeRate x : ℝ) *
              (C * ((G.rateBound : ℝ) * (t - s)) ^ n / (n.factorial : ℝ)) := by
          calc |∑ z, (G.jumpRate x z : ℝ) * D z y (t - s)|
              ≤ ∑ z, |(G.jumpRate x z : ℝ) * D z y (t - s)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = ∑ z, (G.jumpRate x z : ℝ) * |D z y (t - s)| := by
                refine Finset.sum_congr rfl fun z _ => ?_
                rw [abs_mul, abs_of_nonneg (G.jumpRate x z).coe_nonneg]
            _ ≤ ∑ z, (G.jumpRate x z : ℝ) *
                  (C * ((G.rateBound : ℝ) * (t - s)) ^ n /
                    (n.factorial : ℝ)) :=
                Finset.sum_le_sum fun z _ =>
                  mul_le_mul_of_nonneg_left (ih z y (t - s) hts)
                    (G.jumpRate x z).coe_nonneg
            _ = (G.escapeRate x : ℝ) *
                  (C * ((G.rateBound : ℝ) * (t - s)) ^ n /
                    (n.factorial : ℝ)) := by
                rw [← Finset.sum_mul, G.sum_jumpRate_real x]
        have hexp1 : Real.exp (-(G.escapeRate x : ℝ) * s) ≤ 1 := by
          refine Real.exp_le_one_iff.2 ?_
          have : (0 : ℝ) ≤ (G.escapeRate x : ℝ) * s :=
            mul_nonneg (G.escapeRate x).coe_nonneg hs0
          linarith
        calc |Real.exp (-(G.escapeRate x : ℝ) * s) *
                ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s)|
            = Real.exp (-(G.escapeRate x : ℝ) * s) *
                |∑ z, (G.jumpRate x z : ℝ) * D z y (t - s)| := by
              rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          _ ≤ 1 * ((G.escapeRate x : ℝ) *
                (C * ((G.rateBound : ℝ) * (t - s)) ^ n /
                  (n.factorial : ℝ))) :=
              mul_le_mul hexp1 hsum (abs_nonneg _) zero_le_one
          _ ≤ (G.rateBound : ℝ) *
                (C * ((G.rateBound : ℝ) * (t - s)) ^ n /
                  (n.factorial : ℝ)) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right
                (G.escapeRate_le_rateBound_real x) hB0
      have hbound : |D x y t| ≤
          ∫ s in (0 : ℝ)..t,
            (G.rateBound : ℝ) *
              (C * ((G.rateBound : ℝ) * (t - s)) ^ n / (n.factorial : ℝ)) := by
        rw [hrec x y t ht]
        refine le_trans ?_
          (intervalIntegral.integral_mono_on ht0
            (hgcont.abs.intervalIntegrable _ _)
            (hhcont.intervalIntegrable _ _) hpoint)
        simpa [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm
            (f := fun s : ℝ => Real.exp (-(G.escapeRate x : ℝ) * s) *
              ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s))
            (μ := volume) ht0
      have heval : (∫ s in (0 : ℝ)..t,
            (G.rateBound : ℝ) *
              (C * ((G.rateBound : ℝ) * (t - s)) ^ n / (n.factorial : ℝ))) =
          C * ((G.rateBound : ℝ) * t) ^ (n + 1) /
            ((n + 1).factorial : ℝ) := by
        have hcongr : ∀ s : ℝ,
            (G.rateBound : ℝ) *
                (C * ((G.rateBound : ℝ) * (t - s)) ^ n /
                  (n.factorial : ℝ)) =
              ((G.rateBound : ℝ) * C * (G.rateBound : ℝ) ^ n /
                (n.factorial : ℝ)) * (t - s) ^ n := by
          intro s
          rw [mul_pow]
          ring
        simp_rw [hcongr]
        rw [intervalIntegral.integral_const_mul]
        have hsub : (∫ s in (0 : ℝ)..t, (t - s) ^ n) = t ^ (n + 1) / (n + 1) := by
          rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ n) t,
            sub_self, sub_zero, integral_pow]
          simp
        rw [hsub, Nat.factorial_succ]
        have hne : (n.factorial : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        push_cast
        field_simp
        ring
      rw [← heval]
      exact hbound

/-- **Uniqueness for the renewal equation.**  Two bounded continuous families
satisfying the same renewal equation agree on the horizon. -/
theorem eq_of_renewal
    (G : FiniteJumpGenerator Ω) (F₁ F₂ : Ω → Ω → ℝ → ℝ) (T : ℝ)
    (hcont₁ : ∀ x y, Continuous (F₁ x y))
    (hcont₂ : ∀ x y, Continuous (F₂ x y))
    (hrec₁ : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      F₁ x y t = (if x = y then Real.exp (-(G.escapeRate x : ℝ) * t) else 0) +
        ∫ s in (0 : ℝ)..t, Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F₁ z y (t - s))
    (hrec₂ : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      F₂ x y t = (if x = y then Real.exp (-(G.escapeRate x : ℝ) * t) else 0) +
        ∫ s in (0 : ℝ)..t, Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F₂ z y (t - s)) :
    ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T, F₁ x y t = F₂ x y t := by
  set D : Ω → Ω → ℝ → ℝ := fun x y t => F₁ x y t - F₂ x y t with hD
  have hDcont : ∀ x y, Continuous (D x y) := fun x y =>
    (hcont₁ x y).sub (hcont₂ x y)
  -- One uniform bound for the finitely many entries.
  choose Cf hCf using fun p : Ω × Ω =>
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (hDcont p.1 p.2).continuousOn
  have hDbdd : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      |D x y t| ≤ ∑ p : Ω × Ω, |Cf p| := by
    intro x y t ht
    refine le_trans (le_trans (hCf (x, y) t ht) (le_abs_self _)) ?_
    exact Finset.single_le_sum (f := fun p : Ω × Ω => |Cf p|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (x, y))
  -- Subtracting the two equations kills the inhomogeneous term.
  have hDrec : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      D x y t = ∫ s in (0 : ℝ)..t,
        Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s) := by
    intro x y t ht
    have hcont₁' : Continuous fun s : ℝ =>
        Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F₁ z y (t - s) := by
      have h1 : Continuous fun s : ℝ => -(G.escapeRate x : ℝ) * s :=
        continuous_const.mul continuous_id
      refine (Real.continuous_exp.comp h1).mul ?_
      refine continuous_finsetSum _ fun z _ => continuous_const.mul ?_
      exact (hcont₁ z y).comp (continuous_const.sub continuous_id)
    have hcont₂' : Continuous fun s : ℝ =>
        Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F₂ z y (t - s) := by
      have h1 : Continuous fun s : ℝ => -(G.escapeRate x : ℝ) * s :=
        continuous_const.mul continuous_id
      refine (Real.continuous_exp.comp h1).mul ?_
      refine continuous_finsetSum _ fun z _ => continuous_const.mul ?_
      exact (hcont₂ z y).comp (continuous_const.sub continuous_id)
    have hsplit : ∀ s : ℝ,
        Real.exp (-(G.escapeRate x : ℝ) * s) *
            ∑ z, (G.jumpRate x z : ℝ) * D z y (t - s) =
          Real.exp (-(G.escapeRate x : ℝ) * s) *
              ∑ z, (G.jumpRate x z : ℝ) * F₁ z y (t - s) -
            Real.exp (-(G.escapeRate x : ℝ) * s) *
              ∑ z, (G.jumpRate x z : ℝ) * F₂ z y (t - s) := by
      intro s
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      simp only [hD, mul_sub]
    have h₁ : (∫ s in (0 : ℝ)..t, Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F₁ z y (t - s)) =
        F₁ x y t -
          (if x = y then Real.exp (-(G.escapeRate x : ℝ) * t) else 0) := by
      rw [hrec₁ x y t ht]
      ring
    have h₂ : (∫ s in (0 : ℝ)..t, Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F₂ z y (t - s)) =
        F₂ x y t -
          (if x = y then Real.exp (-(G.escapeRate x : ℝ) * t) else 0) := by
      rw [hrec₂ x y t ht]
      ring
    simp_rw [hsplit]
    rw [intervalIntegral.integral_sub (hcont₁'.intervalIntegrable _ _)
      (hcont₂'.intervalIntegrable _ _), h₁, h₂]
    simp only [hD]
    ring
  intro x y t ht
  have hlimit : |D x y t| ≤ 0 := by
    have htend : Filter.Tendsto
        (fun n : ℕ => (∑ p : Ω × Ω, |Cf p|) *
          (((G.rateBound : ℝ) * t) ^ n / (n.factorial : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa using
        (FloorSemiring.tendsto_pow_div_factorial_atTop
          ((G.rateBound : ℝ) * t)).const_mul (∑ p : Ω × Ω, |Cf p|)
    refine ge_of_tendsto' htend fun n => ?_
    simpa [mul_div_assoc] using
      G.abs_le_of_homogeneous_renewal D (∑ p : Ω × Ω, |Cf p|) T hDcont
        hDbdd hDrec n x y t ht
  have : D x y t = 0 := abs_eq_zero.1 (le_antisymm hlimit (abs_nonneg _))
  simpa [hD, sub_eq_zero] using this

end Volterra

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

/-- At time zero the exponential curve is the identity matrix. -/
theorem exp_zero_smul_apply (Q : Matrix Ω Ω ℝ) (x y : Ω) :
    NormedSpace.exp ((0 : ℝ) • Q) x y = if x = y then 1 else 0 := by
  rw [zero_smul, NormedSpace.exp_zero]
  simp [Matrix.one_apply]

theorem continuousOn_expScaled_jumpFlow
    (G : FiniteJumpGenerator Ω) (x y : Ω) (T : ℝ) :
    ContinuousOn
      (fun s : ℝ => Real.exp ((G.escapeRate x : ℝ) * s) * G.jumpFlow x y s)
      (Set.uIcc (0 : ℝ) T) := by
  have hlin : Continuous fun s : ℝ => (G.escapeRate x : ℝ) * s :=
    continuous_const.mul continuous_id
  exact ((Real.continuous_exp.comp hlin).mul
    (G.continuous_jumpFlow x y)).continuousOn

/-- Integrating the exact derivative supplied by the integrating factor. -/
theorem integral_expScaled_jumpFlow
    (G : FiniteJumpGenerator Ω) (x y : Ω) (T : ℝ) :
    (∫ s in (0 : ℝ)..T,
        Real.exp ((G.escapeRate x : ℝ) * s) * G.jumpFlow x y s) =
      Real.exp ((G.escapeRate x : ℝ) * T) *
          NormedSpace.exp (T • G.generator) x y -
        (if x = y then (1 : ℝ) else 0) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => G.hasDerivAt_expScaled x y s)
    (G.continuousOn_expScaled_jumpFlow x y T).intervalIntegrable]
  rw [mul_zero, Real.exp_zero, one_mul, exp_zero_smul_apply]

/-- **Entrywise renewal equation for the matrix exponential.**  Conditioning on
the first jump: either no jump occurs during `[0, T]`, which happens with the
survival weight `e^{-λ(x) T}` and keeps the state at `x`, or the first jump
leaves `x` at time `s` and the remaining time `T - s` is again covered by the
exponential.

The right-hand side is exactly the first-jump decomposition of the jump
process, so this is the real-valued form that the `ℝ≥0∞` path-law side has to
be matched against. -/
theorem exp_smul_apply_renewal
    (G : FiniteJumpGenerator Ω) (x y : Ω) (T : ℝ) :
    NormedSpace.exp (T • G.generator) x y =
      (if x = y then Real.exp (-(G.escapeRate x : ℝ) * T) else 0) +
        ∫ s in (0 : ℝ)..T,
          Real.exp (-(G.escapeRate x : ℝ) * s) * G.jumpFlow x y (T - s) := by
  have hchange :
      (∫ s in (0 : ℝ)..T,
          Real.exp (-(G.escapeRate x : ℝ) * s) * G.jumpFlow x y (T - s)) =
        ∫ s in (0 : ℝ)..T,
          Real.exp (-(G.escapeRate x : ℝ) * (T - s)) * G.jumpFlow x y s := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := T)
      (fun u : ℝ =>
        Real.exp (-(G.escapeRate x : ℝ) * (T - u)) * G.jumpFlow x y u) T
    simpa using h
  have hsplit :
      (∫ s in (0 : ℝ)..T,
          Real.exp (-(G.escapeRate x : ℝ) * (T - s)) * G.jumpFlow x y s) =
        Real.exp (-(G.escapeRate x : ℝ) * T) *
          ∫ s in (0 : ℝ)..T,
            Real.exp ((G.escapeRate x : ℝ) * s) * G.jumpFlow x y s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hexp : -(G.escapeRate x : ℝ) * (T - s) =
        -(G.escapeRate x : ℝ) * T + (G.escapeRate x : ℝ) * s := by ring
    rw [hexp, Real.exp_add, mul_assoc]
  have hinv : Real.exp (-(G.escapeRate x : ℝ) * T) *
      Real.exp ((G.escapeRate x : ℝ) * T) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hchange, hsplit, integral_expScaled_jumpFlow, mul_sub, ← mul_assoc, hinv,
    one_mul]
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy]

theorem continuous_exp_smul_apply (Q : Matrix Ω Ω ℝ) (x y : Ω) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Q) x y :=
  (entryCLM x y).continuous.comp
    ((NormedSpace.exp_continuous (𝔸 := Matrix Ω Ω ℝ)).comp
      (continuous_id.smul continuous_const))

/-- **The exponential is the unique solution of the renewal equation.**  This is
the hook the jump-process side plugs into: exhibiting a continuous family that
satisfies the same first-jump decomposition identifies it with `exp (tQ)`
entrywise, with no further analysis of the matrix exponential. -/
theorem eq_exp_smul_apply_of_renewal
    (G : FiniteJumpGenerator Ω) (F : Ω → Ω → ℝ → ℝ) (T : ℝ)
    (hcont : ∀ x y, Continuous (F x y))
    (hrec : ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      F x y t = (if x = y then Real.exp (-(G.escapeRate x : ℝ) * t) else 0) +
        ∫ s in (0 : ℝ)..t, Real.exp (-(G.escapeRate x : ℝ) * s) *
          ∑ z, (G.jumpRate x z : ℝ) * F z y (t - s)) :
    ∀ x y, ∀ t ∈ Set.Icc (0 : ℝ) T,
      F x y t = NormedSpace.exp (t • G.generator) x y :=
  eq_of_renewal G F (fun x y t => NormedSpace.exp (t • G.generator) x y) T
    hcont (fun x y => continuous_exp_smul_apply G.generator x y) hrec
    fun x y t _ => by
      simpa [jumpFlow] using G.exp_smul_apply_renewal x y t

end MatrixNorm

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
