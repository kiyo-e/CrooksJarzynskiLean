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

/-! ### Exact terminal-state and work distributions

The measure-level Crooks relation restricted to a terminal-state event has
a work weight taking a single value, so the four terminal masses of the
forward and reverse laws satisfy a solvable linear system.  This determines the full work
distribution without computing any transition probability of the chain. -/

/-- The event that a full path terminates in the state `y`. -/
def terminalEvent (y : State) : Set (FullPath State) :=
  {γ | FullPath.terminalState γ = y}

theorem measurableSet_terminalEvent (y : State) :
    MeasurableSet (terminalEvent y) :=
  FullPath.measurable_terminalState (measurableSet_singleton y)

/-- Crooks' relation evaluated on an event carrying a single work-weight
value. -/
theorem crooks_event_const (T : NNReal) {E : Set (FullPath State)}
    (hE : MeasurableSet E) {k : ℝ≥0∞}
    (hk : ∀ γ ∈ E, fullWorkWeight γ = k) :
    k * forwardPathLaw T E = 2 * reversePathLaw T E := by
  have h : (forwardPathLaw T).withDensity fullWorkWeight E =
      (freeEnergyWeight • reversePathLaw T) E := by
    rw [show (forwardPathLaw T).withDensity fullWorkWeight =
        freeEnergyWeight • reversePathLaw T from full_crooks T]
  rw [withDensity_apply _ hE, setLIntegral_congr_fun hE hk,
    setLIntegral_const, Measure.smul_apply, smul_eq_mul] at h
  exact h

/-- Crooks' relation on the terminal-state events of the asymmetric chain. -/
theorem crooks_terminalEvent (T : NNReal) (y : State) :
    terminalWorkWeight y * forwardPathLaw T (terminalEvent y) =
      2 * reversePathLaw T (terminalEvent y) :=
  crooks_event_const T (measurableSet_terminalEvent y)
    (fun γ hγ => by
      rw [fullWorkWeight_eq_terminalWorkWeight,
        show FullPath.terminalState γ = y from hγ])

/-- The two terminal-state events partition the path space. -/
theorem compl_terminalEvent_zero :
    (terminalEvent State.zero)ᶜ = terminalEvent State.one := by
  ext γ
  cases h : FullPath.terminalState γ <;>
    simp [terminalEvent, h]

private theorem real_crooks_zero (T : NNReal) :
    3 * (forwardPathLaw T).real (terminalEvent State.zero) =
      2 * (reversePathLaw T).real (terminalEvent State.zero) := by
  have h := crooks_terminalEvent T State.zero
  rw [show terminalWorkWeight State.zero = 3 from rfl] at h
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofNat, ← measureReal_def, ← measureReal_def] at h'

private theorem real_crooks_one (T : NNReal) :
    3 / 2 * (forwardPathLaw T).real (terminalEvent State.one) =
      2 * (reversePathLaw T).real (terminalEvent State.one) := by
  have h := crooks_terminalEvent T State.one
  rw [show terminalWorkWeight State.one = 3 / 2 from rfl] at h
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofNat,
    ← measureReal_def, ← measureReal_def] at h'

private theorem real_split (μ : Measure (FullPath State))
    [IsProbabilityMeasure μ] :
    μ.real (terminalEvent State.zero) + μ.real (terminalEvent State.one) =
      1 := by
  have h : μ (terminalEvent State.zero) +
      μ (terminalEvent State.one) = 1 := by
    rw [← compl_terminalEvent_zero,
      measure_add_measure_compl (measurableSet_terminalEvent State.zero)]
    exact measure_univ
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one, ← measureReal_def, ← measureReal_def] at h'

/-- The forward law terminates in the ground state with probability `1/3`. -/
theorem forwardPathLaw_terminalEvent_zero (T : NNReal) :
    (forwardPathLaw T).real (terminalEvent State.zero) = 1 / 3 := by
  have h0 := real_crooks_zero T
  have h1 := real_crooks_one T
  have h2 := real_split (forwardPathLaw T)
  have h3 := real_split (reversePathLaw T)
  linarith

/-- The forward law terminates in the excited state with probability `2/3`. -/
theorem forwardPathLaw_terminalEvent_one (T : NNReal) :
    (forwardPathLaw T).real (terminalEvent State.one) = 2 / 3 := by
  have h0 := forwardPathLaw_terminalEvent_zero T
  have h2 := real_split (forwardPathLaw T)
  linarith

/-- The reverse law has the uniform terminal distribution. -/
theorem reversePathLaw_terminalEvent (T : NNReal) (y : State) :
    (reversePathLaw T).real (terminalEvent y) = 1 / 2 := by
  have h0 := real_crooks_zero T
  have h1 := real_crooks_one T
  have h2 := real_split (forwardPathLaw T)
  have h3 := real_split (reversePathLaw T)
  cases y <;> linarith

/-- The quench work takes the value `-log 3` exactly on the ground-state
terminal event. -/
theorem thermodynamicWork_preimage_low :
    thermodynamicWork ⁻¹' {-Real.log 3} = terminalEvent State.zero := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  ext γ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, terminalEvent,
    Set.mem_setOf_eq]
  unfold thermodynamicWork thermodynamicStateWork
  cases h : FullPath.terminalState γ
  · simp [finalEnergy, initialEnergy]
  · simp only [finalEnergy, initialEnergy]
    constructor
    · intro heq
      exfalso
      have : Real.log 2 = 0 := by linarith
      linarith
    · intro heq
      cases heq

/-- The quench work takes the value `log 2 - log 3 = log (2/3)` exactly on the
excited-state terminal event. -/
theorem thermodynamicWork_preimage_high :
    thermodynamicWork ⁻¹' {Real.log 2 - Real.log 3} =
      terminalEvent State.one := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  ext γ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, terminalEvent,
    Set.mem_setOf_eq]
  unfold thermodynamicWork thermodynamicStateWork
  cases h : FullPath.terminalState γ
  · simp only [finalEnergy, initialEnergy]
    constructor
    · intro heq
      exfalso
      have : Real.log 2 = 0 := by linarith
      linarith
    · intro heq
      cases heq
  · constructor
    · intro _
      rfl
    · intro _
      simp [finalEnergy, initialEnergy]
      ring

/-- The exact forward work distribution at its low atom:
`P(W = -log 3) = 1/3`. -/
theorem forward_work_atom_low (T : NNReal) :
    ((forwardPathLaw T).map thermodynamicWork).real {-Real.log 3} =
      1 / 3 := by
  rw [measureReal_def,
    Measure.map_apply measurable_thermodynamicWork
      (measurableSet_singleton _),
    thermodynamicWork_preimage_low, ← measureReal_def]
  exact forwardPathLaw_terminalEvent_zero T

/-- The exact forward work distribution at its high atom:
`P(W = log (2/3)) = 2/3`. -/
theorem forward_work_atom_high (T : NNReal) :
    ((forwardPathLaw T).map thermodynamicWork).real
        {Real.log 2 - Real.log 3} = 2 / 3 := by
  rw [measureReal_def,
    Measure.map_apply measurable_thermodynamicWork
      (measurableSet_singleton _),
    thermodynamicWork_preimage_high, ← measureReal_def]
  exact forwardPathLaw_terminalEvent_one T

/-- The exact mean quench work under the forward law. -/
theorem full_average_work (T : NNReal) :
    ∫ γ, thermodynamicWork γ ∂forwardPathLaw T =
      2 / 3 * Real.log 2 - Real.log 3 := by
  rw [← integral_add_compl (measurableSet_terminalEvent State.zero)
    (integrable_thermodynamicWork T), compl_terminalEvent_zero]
  have hzero :
      ∫ γ in terminalEvent State.zero, thermodynamicWork γ
          ∂forwardPathLaw T =
        (forwardPathLaw T).real (terminalEvent State.zero) •
          thermodynamicStateWork State.zero := by
    rw [← setIntegral_const]
    exact setIntegral_congr_fun (measurableSet_terminalEvent State.zero)
      (fun γ hγ => by
        unfold thermodynamicWork
        rw [show FullPath.terminalState γ = State.zero from hγ])
  have hone :
      ∫ γ in terminalEvent State.one, thermodynamicWork γ
          ∂forwardPathLaw T =
        (forwardPathLaw T).real (terminalEvent State.one) •
          thermodynamicStateWork State.one := by
    rw [← setIntegral_const]
    exact setIntegral_congr_fun (measurableSet_terminalEvent State.one)
      (fun γ hγ => by
        unfold thermodynamicWork
        rw [show FullPath.terminalState γ = State.one from hγ])
  rw [hzero, hone, forwardPathLaw_terminalEvent_zero T,
    forwardPathLaw_terminalEvent_one T]
  unfold thermodynamicStateWork
  simp only [finalEnergy, initialEnergy, smul_eq_mul]
  ring

/-- The strict second law for the asymmetric quench: the mean dissipated work
is strictly positive because `27 < 32`. -/
theorem full_second_law_strict (T : NNReal) :
    physicalDeltaFreeEnergy <
      ∫ γ, thermodynamicWork γ ∂forwardPathLaw T := by
  rw [full_average_work, physicalDeltaFreeEnergy_eq]
  have hlt : Real.log 27 < Real.log 32 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith

/-! ### The reverse work observable and the conventional Crooks ratio -/

/-- The reverse experiment's own quench work, expressed in the chronological
representation used by `reversePathLaw`: the reverse protocol un-quenches
`finalEnergy` back to `initialEnergy`, and in the reversed time coordinates
this happens at the state recorded as the terminal coordinate. -/
noncomputable def reverseThermodynamicWork (γ : FullPath State) : ℝ :=
  initialEnergy (FullPath.terminalState γ) -
    finalEnergy (FullPath.terminalState γ)

/-- Sign convention: the reverse work observable is the negated forward work
observable, pointwise on the reversed path space. -/
theorem reverseThermodynamicWork_eq_neg (γ : FullPath State) :
    reverseThermodynamicWork γ = -thermodynamicWork γ := by
  unfold reverseThermodynamicWork thermodynamicWork thermodynamicStateWork
  ring

/-- The conventional atomwise Crooks ratio
`P_F(W = w) = exp (β (w - ΔF)) * P_R(W_rev = -w)`, stated with the reverse
experiment's own work observable and valid for every real work value. -/
theorem crooks_work_atom (T : NNReal) (w : ℝ) :
    (forwardPathLaw T).real {γ | thermodynamicWork γ = w} =
      Real.exp (thermodynamicBeta * (w - physicalDeltaFreeEnergy)) *
        (reversePathLaw T).real
          {γ | reverseThermodynamicWork γ = -w} := by
  have hset : {γ : FullPath State | reverseThermodynamicWork γ = -w} =
      {γ : FullPath State | thermodynamicWork γ = w} := by
    ext γ
    simp only [Set.mem_setOf_eq, reverseThermodynamicWork_eq_neg,
      neg_inj]
  have hB : MeasurableSet {γ : FullPath State | thermodynamicWork γ = w} :=
    measurable_thermodynamicWork (measurableSet_singleton w)
  have hkey := crooks_event_const T hB
    (k := ENNReal.ofReal (Real.exp (-thermodynamicBeta * w)))
    (fun γ hγ => by
      rw [fullWorkWeight_eq_exp_thermodynamicWork,
        show thermodynamicWork γ = w from hγ])
  have hreal := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_ofNat,
    ← measureReal_def, ← measureReal_def] at hreal
  rw [hset, physicalDeltaFreeEnergy_eq]
  simp only [thermodynamicBeta] at hreal ⊢
  rw [show (1 : ℝ) * (w - -Real.log 2) = w + Real.log 2 by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hcancel : Real.exp w * Real.exp (-(1 : ℝ) * w) = 1 := by
    rw [← Real.exp_add]
    norm_num
  set a := (forwardPathLaw T).real {γ | thermodynamicWork γ = w}
  set r := (reversePathLaw T).real {γ | thermodynamicWork γ = w}
  calc
    a = Real.exp w * (Real.exp (-(1 : ℝ) * w) * a) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = Real.exp w * (2 * r) := by rw [hreal]
    _ = Real.exp w * 2 * r := by ring

end AsymmetricExample
end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
