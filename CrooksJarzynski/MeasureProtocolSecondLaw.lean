/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocol
import Mathlib.Analysis.Convex.Integral

/-!
# The second law from an abstract Crooks relation

This module derives the average-work inequality directly from the physical
measure-level Crooks relation on an arbitrary measurable trajectory space.  It
is independent of a particular discrete protocol, jump-process construction,
or path parametrization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol

universe u

variable {Γ : Type u} [MeasurableSpace Γ]

/-- A physical Crooks relation with positive inverse temperature implies the
average-work form of the second law.  Both path laws are assumed normalized,
and the work observable is assumed integrable under the forward law. -/
theorem second_law_of_crooks
    (forward reverse : Measure Γ) (β ΔF : ℝ) (work : Γ → ℝ)
    [IsProbabilityMeasure forward] [IsProbabilityMeasure reverse]
    (hβ : 0 < β) (hwork : Measurable work)
    (hworkInt : Integrable work forward)
    (h : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work γ)))
      (ENNReal.ofReal (Real.exp (-β * ΔF)))) :
    ΔF ≤ ∫ γ, work γ ∂forward := by
  have hjarzynski :=
    jarzynski_integral forward reverse β ΔF work hwork h
  have hexpInt : Integrable
      (fun γ => Real.exp (-β * work γ)) forward := by
    by_contra hn
    rw [MeasureTheory.integral_undef hn] at hjarzynski
    exact Real.exp_ne_zero _ hjarzynski.symm
  have hlinearInt : Integrable (fun γ => -β * work γ) forward := by
    simpa using hworkInt.const_mul (-β)
  have hjensen :
      Real.exp (∫ γ, -β * work γ ∂forward) ≤
        ∫ γ, Real.exp (-β * work γ) ∂forward := by
    simpa [Function.comp_def] using
      (convexOn_exp.map_integral_le Real.continuousOn_exp isClosed_univ
        (by simp) hlinearInt hexpInt)
  rw [hjarzynski, integral_const_mul] at hjensen
  have hscaled :
      -β * (∫ γ, work γ ∂forward) ≤ -β * ΔF :=
    Real.exp_le_exp.mp hjensen
  nlinarith

end MeasureProtocol
end CrooksJarzynski
