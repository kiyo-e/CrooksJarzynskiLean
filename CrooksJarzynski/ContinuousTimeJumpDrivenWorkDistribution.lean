/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenPhysical

/-!
# Work-distribution Crooks for stepwise driven protocols

The measure-level Crooks relation for the driven laws is stated on the path
space.  This module connects it to the presentation standard in the physics
literature: the distribution of the work observable itself.

Two ingredients are needed.  First, the reverse experiment's own work
observable is defined intrinsically: its `j`-th window first quenches the
energy one step along the reversed protocol — evaluated at that window's
initial state, which the forward-aligned carrier stores at position `j.rev` —
and then relaxes under the corresponding generator.  An index
computation shows this observable is exactly the negated forward work — the
sign convention familiar from the `P_F(W = w) = e^{β(w-ΔF)} P_R(W_R = -w)`
form of Crooks' relation.  Second, pushing the measure-level relation forward
along the work observable gives the division-free Crooks relation between the
two work distributions, and evaluating it on singleton events gives the
conventional atomwise ratio.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### The reverse experiment's own work observable -/

/-- The work performed by the reverse experiment, read in its own chronology.
The reverse protocol visits the energy landscapes in reversed order, and each
window quenches before it relaxes: the `j`-th window first switches
`energy (j.castSucc).rev` off and `energy (j.succ).rev` on at its own initial
state, and then relaxes under the matching generator.  The forward-aligned
carrier stores that quench state at position `j.rev`. -/
noncomputable def reverseWork
    {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ) (γ : Path Ω M) : ℝ :=
  ∑ j : Fin M,
    (energy (j.succ).rev (endpointAt γ j.rev) -
      energy (j.castSucc).rev (endpointAt γ j.rev))

/-- **Sign convention.**  On the aligned carrier the reverse experiment's own
work observable is the negated forward work observable, pointwise. -/
theorem reverseWork_eq_neg
    {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ) (γ : Path Ω M) :
    reverseWork energy γ = -work energy γ := by
  have hsucc : ∀ j : Fin M, (j.succ).rev = (j.rev).castSucc := by
    intro j
    have hj := j.isLt
    ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    omega
  have hcast : ∀ j : Fin M, (j.castSucc).rev = (j.rev).succ := by
    intro j
    have hj := j.isLt
    ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    omega
  have hreindex : reverseWork energy γ =
      ∑ i : Fin M,
        (energy i.castSucc (endpointAt γ i) -
          energy i.succ (endpointAt γ i)) := by
    unfold reverseWork
    exact Fintype.sum_bijective Fin.rev Fin.rev_involutive.bijective _ _
      (fun j => by rw [hsucc j, hcast j])
  rw [hreindex, work_eq_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The reverse work observable is measurable. -/
theorem measurable_reverseWork
    {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ)
    (henergy : ∀ i, Measurable (energy i)) :
    Measurable (reverseWork energy) := by
  have h : Measurable (fun γ : Path Ω M => -work energy γ) :=
    (measurable_work energy henergy).neg
  have hfun : reverseWork energy = fun γ : Path Ω M => -work energy γ :=
    funext fun γ => reverseWork_eq_neg energy γ
  rw [hfun]
  exact h

/-! ### Evaluating a Crooks relation on constant-weight events -/

/-- Evaluating a division-free Crooks relation on an event where the work
weight is a single value.  Stated for an arbitrary measurable carrier. -/
theorem crooks_event_const {Γ : Type*} [MeasurableSpace Γ]
    {forward reverse : Measure Γ} {q : Γ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : CrooksRelation forward reverse q c)
    {E : Set Γ} (hE : MeasurableSet E) {k : ℝ≥0∞}
    (hk : ∀ γ ∈ E, q γ = k) :
    k * forward E = c * reverse E := by
  have hh : forward.withDensity q E = (c • reverse) E := by
    rw [show forward.withDensity q = c • reverse from h]
  rw [withDensity_apply _ hE, setLIntegral_congr_fun hE hk,
    setLIntegral_const, Measure.smul_apply, smul_eq_mul] at hh
  exact hh

variable [Fintype Ω] [MeasurableSingletonClass Ω]
variable [DecidableEq Ω] [Nonempty Ω]

/-! ### The driven work-distribution Crooks relation -/

/-- **Work-distribution Crooks relation for the constructed stepwise driven
laws.**  Pushing the measure-level relation forward along the work observable
relates the forward and aligned-reverse work distributions by the exponential
work weight. -/
theorem work_distribution_crooks_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    CrooksRelation
      ((forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).map (work energy))
      ((reverseDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M)))
        generator duration).map (work energy))
      (fun w => ENNReal.ofReal (Real.exp (-β * w)))
      (ENNReal.ofReal
        (Real.exp (-β *
          deltaFreeEnergy (Measure.count : Measure Ω) β energy))) :=
  MeasureProtocol.work_distribution_crooks _ _ β _ (work energy)
    (measurable_work energy fun _ => Measurable.of_discrete)
    (crooks_of_gibbsDetailedBalance β hβ energy generator duration hbalance)

/-- **Work-distribution Crooks relation in the reverse experiment's own work
coordinate.** The reverse distribution is reflected by `w ↦ -w` before it is
compared with the forward distribution, so the theorem exposes `reverseWork`
directly while retaining the division-free measure identity. -/
theorem work_distribution_crooks_reverseWork_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc)) :
    CrooksRelation
      ((forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).map (work energy))
      (((reverseDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β
          (energy (Fin.last M)))
        generator duration).map (reverseWork energy)).map
          (fun w : ℝ => -w))
      (fun w => ENNReal.ofReal (Real.exp (-β * w)))
      (ENNReal.ofReal
        (Real.exp (-β *
          deltaFreeEnergy (Measure.count : Measure Ω) β energy))) := by
  have hreverse :
      ((reverseDrivenLaw
          (Gibbs.measure (Measure.count : Measure Ω) β
            (energy (Fin.last M)))
          generator duration).map (reverseWork energy)).map
            (fun w : ℝ => -w) =
        (reverseDrivenLaw
          (Gibbs.measure (Measure.count : Measure Ω) β
            (energy (Fin.last M)))
          generator duration).map (work energy) := by
    rw [Measure.map_map measurable_neg (measurable_reverseWork energy
      fun _ => Measurable.of_discrete)]
    apply Measure.map_congr
    filter_upwards [] with γ
    rw [Function.comp_apply, reverseWork_eq_neg]
    simp
  rw [hreverse]
  exact work_distribution_crooks_of_gibbsDetailedBalance
    β hβ energy generator duration hbalance

/-- **The conventional atomwise Crooks ratio for driven protocols**:
`P_F(W = w) = exp (β (w - ΔF)) · P_R(W_R = -w)`, stated with the reverse
experiment's own work observable and valid for every real work value. -/
theorem crooks_work_atom_of_gibbsDetailedBalance
    {M : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal)
    (hbalance : ∀ i,
      (generator i).IsGibbsDetailedBalance β (energy i.castSucc))
    (w : ℝ) :
    (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
        generator duration).real {γ | work energy γ = w} =
      Real.exp (β * (w -
          deltaFreeEnergy (Measure.count : Measure Ω) β energy)) *
        (reverseDrivenLaw
          (Gibbs.measure (Measure.count : Measure Ω) β
            (energy (Fin.last M)))
          generator duration).real
          {γ | reverseWork energy γ = -w} := by
  classical
  set ΔF := deltaFreeEnergy (Measure.count : Measure Ω) β energy with hΔF
  have hset : {γ : Path Ω M | reverseWork energy γ = -w} =
      {γ : Path Ω M | work energy γ = w} := by
    ext γ
    simp only [Set.mem_setOf_eq, reverseWork_eq_neg, neg_inj]
  have hwork : Measurable (work energy : Path Ω M → ℝ) :=
    measurable_work energy fun _ => Measurable.of_discrete
  have hB : MeasurableSet {γ : Path Ω M | work energy γ = w} :=
    hwork (measurableSet_singleton w)
  have hkey := crooks_event_const
    (crooks_of_gibbsDetailedBalance β hβ energy generator duration
      hbalance)
    hB (k := ENNReal.ofReal (Real.exp (-β * w)))
    (fun γ hγ => by rw [show work energy γ = w from hγ])
  have hreal := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ← measureReal_def, ← measureReal_def] at hreal
  rw [hset]
  set a := (forwardDrivenLaw
      (Gibbs.measure (Measure.count : Measure Ω) β (energy 0))
      generator duration).real {γ | work energy γ = w}
  set r := (reverseDrivenLaw
      (Gibbs.measure (Measure.count : Measure Ω) β
        (energy (Fin.last M)))
      generator duration).real {γ | work energy γ = w}
  have hcancel : Real.exp (β * w) * Real.exp (-β * w) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    a = Real.exp (β * w) * (Real.exp (-β * w) * a) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = Real.exp (β * w) * (Real.exp (-β * ΔF) * r) := by rw [hreal]
    _ = Real.exp (β * (w - ΔF)) * r := by
      rw [← mul_assoc, ← Real.exp_add,
        show β * w + -β * ΔF = β * (w - ΔF) by ring]

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
