/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateThermodynamics

/-!
# Physical work and fluctuation relations for the asymmetric chain

The factorized ENNReal work weight of the asymmetric path law telescopes to the
Boltzmann factor of the terminal quench.  This identifies the existing
measure-level Crooks relation with a real-valued thermodynamic work observable
and yields physical Jarzynski, work-law Crooks, integral-fluctuation, and
average-work second-law statements.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState
namespace AsymmetricExample

/-- The terminal-state potential whose ratios give the jump-work factors. -/
noncomputable def terminalWorkWeight (x : State) : ℝ≥0∞ :=
  boundaryWork x x

/-- The state-to-state work factor, independent of the jump index. -/
noncomputable def edgeWorkWeight (x y : State) : ℝ≥0∞ :=
  jumpWork (0 : Fin 1) x y

/-- The boundary factor depends only on the initial endpoint. -/
theorem boundaryWork_eq_terminalWorkWeight (x y : State) :
    boundaryWork x y = terminalWorkWeight x := by
  cases x <;> rfl

/-- Every indexed jump-work factor is the same time-homogeneous edge factor. -/
theorem jumpWork_eq_edgeWorkWeight {n : ℕ} (i : Fin n) (x y : State) :
    jumpWork i x y = edgeWorkWeight x y := by
  cases x <;> cases y <;> rfl

/-- Multiplying by one edge-work factor transports the terminal-state
potential across that edge. -/
theorem terminalWorkWeight_mul_edgeWorkWeight (x y : State) :
    terminalWorkWeight x * edgeWorkWeight x y = terminalWorkWeight y := by
  cases x <;> cases y
  · norm_num [terminalWorkWeight, edgeWorkWeight, boundaryWork, jumpWork]
  · change (3 : ℝ≥0∞) * (1 / 2) = 3 / 2
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ac_rfl
  · change (3 / 2 : ℝ≥0∞) * 2 = 3
    exact ENNReal.div_mul_cancel (a := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
  · norm_num [terminalWorkWeight, edgeWorkWeight, boundaryWork, jumpWork]

/-- The product of edge-work factors telescopes between the first and last
states of every finite state sequence. -/
theorem terminalWorkWeight_mul_prod_edgeWorkWeight {n : ℕ}
    (states : Fin (n + 1) → State) :
    terminalWorkWeight (states 0) *
        (∏ i : Fin n,
          edgeWorkWeight (states i.castSucc) (states i.succ)) =
      terminalWorkWeight (states (Fin.last n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_succ, ← mul_assoc]
      simp only [Fin.castSucc_zero]
      rw [terminalWorkWeight_mul_edgeWorkWeight]
      simpa using ih (fun i : Fin (n + 1) => states i.succ)

/-- The complete factorized path-work weight is determined by the terminal
state. -/
theorem rateWorkWeight_eq_terminalWorkWeight {n : ℕ}
    (γ : JumpPath State n) :
    JumpPath.rateWorkWeight boundaryWork jumpWork γ =
      terminalWorkWeight (γ.1 (Fin.last n)) := by
  unfold JumpPath.rateWorkWeight JumpPath.factorizedWorkWeight
  simp only [one_mul, mul_one]
  rw [boundaryWork_eq_terminalWorkWeight]
  simp_rw [jumpWork_eq_edgeWorkWeight]
  exact terminalWorkWeight_mul_prod_edgeWorkWeight γ.1

/-- The full-path work weight is the terminal-state potential. -/
theorem fullWorkWeight_eq_terminalWorkWeight (γ : FullPath State) :
    fullWorkWeight γ = terminalWorkWeight (FullPath.terminalState γ) := by
  rcases γ with ⟨n, γ⟩
  change JumpPath.rateWorkWeight boundaryWork jumpWork γ =
    terminalWorkWeight (γ.1 (Fin.last n))
  exact rateWorkWeight_eq_terminalWorkWeight γ

/-- Real-valued work performed by the final energy quench. -/
noncomputable def thermodynamicStateWork (x : State) : ℝ :=
  finalEnergy x - initialEnergy x

/-- The thermodynamic work of a path is the final-quench work evaluated at its
actual terminal state. -/
noncomputable def thermodynamicWork (γ : FullPath State) : ℝ :=
  thermodynamicStateWork (FullPath.terminalState γ)

/-- The real-valued thermodynamic work is measurable. -/
theorem measurable_thermodynamicWork : Measurable thermodynamicWork := by
  unfold thermodynamicWork
  exact (Measurable.of_discrete : Measurable thermodynamicStateWork).comp
    FullPath.measurable_terminalState

/-- The terminal-state potential is the Boltzmann factor of the final-quench
work. -/
theorem terminalWorkWeight_eq_exp_thermodynamicStateWork (x : State) :
    terminalWorkWeight x =
      ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * thermodynamicStateWork x)) := by
  cases x
  · change (3 : ℝ≥0∞) =
      ENNReal.ofReal
        (Real.exp (-(1 : ℝ) * ((-Real.log 3) - 0)))
    rw [show -(1 : ℝ) * ((-Real.log 3) - 0) = Real.log 3 by ring,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  · change (3 / 2 : ℝ≥0∞) =
      ENNReal.ofReal
        (Real.exp (-(1 : ℝ) *
          ((-Real.log 3) - (-Real.log 2))))
    rw [show -(1 : ℝ) * ((-Real.log 3) - (-Real.log 2)) =
        Real.log 3 - Real.log 2 by ring,
      Real.exp_sub,
      Real.exp_log (by norm_num : (0 : ℝ) < 3),
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num [ENNReal.ofReal_ofNat]

/-- The existing factorized path-work observable is exactly `exp (-β W)` for
the real-valued final-quench work. -/
theorem fullWorkWeight_eq_exp_thermodynamicWork (γ : FullPath State) :
    fullWorkWeight γ =
      ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * thermodynamicWork γ)) := by
  rw [fullWorkWeight_eq_terminalWorkWeight]
  exact terminalWorkWeight_eq_exp_thermodynamicStateWork
    (FullPath.terminalState γ)

/-- The real-valued quench work is not almost-everywhere constant under the
normalized forward path law. -/
theorem thermodynamicWork_not_ae_const (T : NNReal) :
    ¬ ∃ c : ℝ, thermodynamicWork =ᵐ[forwardPathLaw T] fun _ => c := by
  rintro ⟨c, hc⟩
  apply fullWorkWeight_not_ae_const T
  refine ⟨ENNReal.ofReal (Real.exp (-thermodynamicBeta * c)), ?_⟩
  filter_upwards [hc] with γ hγ
  rw [fullWorkWeight_eq_exp_thermodynamicWork, hγ]

/-- Physical Crooks relation for the normalized asymmetric chain, stated with
real work and free-energy observables. -/
theorem full_crooks_physical (T : NNReal) :
    CrooksRelation (forwardPathLaw T) (reversePathLaw T)
      (fun γ => ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * thermodynamicWork γ)))
      (ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * physicalDeltaFreeEnergy))) := by
  have hwork :
      (fun γ => ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * thermodynamicWork γ))) =
        fullWorkWeight := by
    funext γ
    exact (fullWorkWeight_eq_exp_thermodynamicWork γ).symm
  have hfree :
      ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * physicalDeltaFreeEnergy)) =
        freeEnergyWeight :=
    freeEnergyWeight_eq_exp_delta.symm
  rw [hwork, hfree]
  exact full_crooks T

/-- Real-valued physical Jarzynski equality for the asymmetric chain. -/
theorem full_jarzynski_physical (T : NNReal) :
    ∫ γ, Real.exp (-thermodynamicBeta * thermodynamicWork γ)
        ∂forwardPathLaw T =
      Real.exp (-thermodynamicBeta * physicalDeltaFreeEnergy) :=
  jarzynski_integral _ _ thermodynamicBeta physicalDeltaFreeEnergy
    thermodynamicWork measurable_thermodynamicWork (full_crooks_physical T)

/-- The physical Jarzynski average evaluates to the explicit factor two. -/
theorem full_jarzynski_physical_eq_two (T : NNReal) :
    ∫ γ, Real.exp (-thermodynamicBeta * thermodynamicWork γ)
        ∂forwardPathLaw T = 2 := by
  rw [full_jarzynski_physical, thermodynamicBeta]
  rw [show (-(1 : ℝ)) * physicalDeltaFreeEnergy =
      -physicalDeltaFreeEnergy by ring,
    exp_neg_physicalDeltaFreeEnergy]

/-- Density-free Crooks relation for the pushforward laws of the real work
observable. -/
theorem full_work_distribution_crooks (T : NNReal) :
    CrooksRelation
      ((forwardPathLaw T).map thermodynamicWork)
      ((reversePathLaw T).map thermodynamicWork)
      (fun w => ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * w)))
      (ENNReal.ofReal
        (Real.exp (-thermodynamicBeta * physicalDeltaFreeEnergy))) :=
  work_distribution_crooks _ _ thermodynamicBeta physicalDeltaFreeEnergy
    thermodynamicWork measurable_thermodynamicWork (full_crooks_physical T)

/-- The two-valued thermodynamic work observable is integrable under the
normalized forward path law. -/
theorem integrable_thermodynamicWork (T : NNReal) :
    Integrable thermodynamicWork (forwardPathLaw T) := by
  apply Integrable.of_bound measurable_thermodynamicWork.aestronglyMeasurable
    (max ‖thermodynamicStateWork .zero‖ ‖thermodynamicStateWork .one‖)
  filter_upwards [] with γ
  unfold thermodynamicWork
  cases h : FullPath.terminalState γ
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The average-work second law for the normalized asymmetric chain. -/
theorem full_second_law (T : NNReal) :
    physicalDeltaFreeEnergy ≤
      ∫ γ, thermodynamicWork γ ∂forwardPathLaw T :=
  second_law_of_crooks (forwardPathLaw T) (reversePathLaw T)
    thermodynamicBeta physicalDeltaFreeEnergy thermodynamicWork
    (by norm_num [thermodynamicBeta]) measurable_thermodynamicWork
    (integrable_thermodynamicWork T) (full_crooks_physical T)

/-- Stochastic entropy production associated with the final-quench work. -/
noncomputable def entropyProduction (γ : FullPath State) : ℝ :=
  thermodynamicBeta * (thermodynamicWork γ - physicalDeltaFreeEnergy)

/-- Integral fluctuation theorem for the entropy production. -/
theorem full_entropyProduction_integral_fluctuation (T : NNReal) :
    ∫ γ, Real.exp (-entropyProduction γ) ∂forwardPathLaw T = 1 := by
  have hpoint :
      (fun γ => Real.exp (-entropyProduction γ)) =
        fun γ =>
          Real.exp (thermodynamicBeta * physicalDeltaFreeEnergy) *
            Real.exp (-thermodynamicBeta * thermodynamicWork γ) := by
    funext γ
    rw [← Real.exp_add]
    congr 1
    unfold entropyProduction
    ring
  rw [hpoint, integral_const_mul, full_jarzynski_physical,
    ← Real.exp_add,
    show thermodynamicBeta * physicalDeltaFreeEnergy +
        -thermodynamicBeta * physicalDeltaFreeEnergy = 0 by ring]
  exact Real.exp_zero

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
