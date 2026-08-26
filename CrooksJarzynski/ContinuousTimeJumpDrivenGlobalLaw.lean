/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatLaw
import CrooksJarzynski.ContinuousTimeJumpDrivenConcat

/-!
# Global laws for driven continuous-time jump protocols

This module pushes the marked driven path laws through the chronological
concatenation of their window charts.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Concatenating all marked window charts is measurable. -/
@[fun_prop]
theorem measurable_concatenateWindows :
    ∀ {M : ℕ}, Measurable (concatenateWindows : Path Ω M → FullPath Ω)
  | 0 => by
      simp only [concatenateWindows]
      exact (FullPath.measurable_mk 0).comp (by fun_prop)
  | M + 1 => by
      simp only [concatenateWindows]
      exact FullPath.measurable_concat_prod.comp
        ((measurable_concatenateWindows.comp (by fun_prop)).prodMk (by fun_prop))

/-- Elapsed protocol time at a window boundary. -/
def boundaryTime {M : ℕ} (duration : Fin M → NNReal)
    (i : Fin (M + 1)) : NNReal :=
  ∑ j ∈ Finset.Iio i, Fin.lastCases 0 duration j

@[simp]
theorem boundaryTime_zero {M : ℕ} (duration : Fin M → NNReal) :
    boundaryTime duration 0 = 0 := by
  simp [boundaryTime]

@[simp]
theorem boundaryTime_last {M : ℕ} (duration : Fin M → NNReal) :
    boundaryTime duration (Fin.last M) = ∑ i, duration i := by
  simp [boundaryTime]

theorem boundaryTime_succ {M : ℕ} (duration : Fin M → NNReal) (i : Fin M) :
    boundaryTime duration i.succ =
      boundaryTime duration i.castSucc + duration i := by
  have hIio : Finset.Iio i.succ =
      insert i.castSucc (Finset.Iio i.castSucc) := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert]
    constructor
    · intro h
      by_cases heq : j = i.castSucc
      · exact Or.inl heq
      · right
        change j.val < i.val + 1 at h
        have hle : j.val ≤ i.val := Nat.le_of_lt_succ h
        have hneval : j.val ≠ i.val := by
          intro hvaleq
          apply heq
          apply Fin.ext
          exact hvaleq
        exact Fin.mk_lt_mk.mpr (lt_of_le_of_ne hle hneval)
    · rintro (rfl | h)
      · exact Fin.castSucc_lt_succ
      · exact h.trans Fin.castSucc_lt_succ
  rw [boundaryTime, boundaryTime, hIio, Finset.sum_insert]
  · simp [add_comm]
  · simp

private theorem boundaryTime_castSucc {M : ℕ}
    (duration : Fin (M + 1) → NNReal) (i : Fin (M + 1)) :
    boundaryTime duration i.castSucc =
      boundaryTime (fun j : Fin M => duration j.castSucc) i := by
  rw [boundaryTime, boundaryTime, Fin.Iio_castSucc, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  have hne : j ≠ Fin.last M := by
    exact ne_of_lt ((Finset.mem_Iio.mp hj).trans_le (Fin.le_last i))
  rcases Fin.exists_castSucc_eq.2 hne with ⟨k, rfl⟩
  simp

private theorem boundaryTime_le_last {M : ℕ}
    (duration : Fin M → NNReal) (i : Fin (M + 1)) :
    boundaryTime duration i ≤ boundaryTime duration (Fin.last M) := by
  unfold boundaryTime
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hj).trans_le (Fin.le_last i))
  · intro j _ _
    simp

/-- Work read directly from the global right-continuous trajectory at every
window-end time. -/
noncomputable def globalWork {M : ℕ} (energy : Fin (M + 1) → Ω → ℝ)
    (duration : Fin M → NNReal) (γ : FullPath Ω) : ℝ :=
  ∑ i : Fin M,
    (energy i.succ
        (FullPath.trajectory γ ((boundaryTime duration i.succ : NNReal) : ℝ)) -
      energy i.castSucc
        (FullPath.trajectory γ ((boundaryTime duration i.succ : NNReal) : ℝ)))

/-- The reverse experiment's own work, read on the chronology-aligned global
chart: the negated aligned work coordinate. -/
noncomputable def globalReverseWork {M : ℕ}
    (energy : Fin (M + 1) → Ω → ℝ)
    (duration : Fin M → NNReal) (γ : FullPath Ω) : ℝ :=
  -(globalWork energy duration γ)

/-- The work observable read from a global chart is measurable. -/
theorem measurable_globalWork {M : ℕ}
    (energy : Fin (M + 1) → Ω → ℝ) (duration : Fin M → NNReal)
    (henergy : ∀ i, Measurable (energy i)) :
    Measurable (globalWork energy duration) := by
  unfold globalWork
  fun_prop

/-- The reverse experiment's work observable on a global chart is
measurable. -/
theorem measurable_globalReverseWork {M : ℕ}
    (energy : Fin (M + 1) → Ω → ℝ) (duration : Fin M → NNReal)
    (henergy : ∀ i, Measurable (energy i)) :
    Measurable (globalReverseWork energy duration) := by
  exact (measurable_globalWork energy duration henergy).neg

/-- A boundary-consistent concatenation ends at the carrier's current
endpoint. -/
theorem terminalState_concatenateWindows :
    ∀ {M : ℕ} {γ : Path Ω M}, IsBoundaryConsistent γ →
      FullPath.terminalState (concatenateWindows γ) = γ.1
  | 0, γ, _ => by simp [concatenateWindows]
  | M + 1, γ, hγ => by
      rw [concatenateWindows, FullPath.terminalState_concat _ _
        ((terminalState_concatenateWindows hγ.2.2).trans hγ.1.symm)]
      exact hγ.2.1

variable [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]

/-- The forward law of the single concatenated real-time chart. -/
noncomputable def forwardGlobalLaw {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) : Measure (FullPath Ω) :=
  (forwardDrivenLaw initial generator duration).map concatenateWindows

noncomputable instance instIsProbabilityMeasureForwardGlobalLaw
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (forwardGlobalLaw initial generator duration) := by
  unfold forwardGlobalLaw
  exact Measure.isProbabilityMeasure_map measurable_concatenateWindows.aemeasurable

/-- The reverse-experiment law on a forward-chronology concatenated chart. -/
noncomputable def reverseGlobalLaw {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) : Measure (FullPath Ω) :=
  (reverseDrivenLaw final generator duration).map concatenateWindows

noncomputable instance instIsProbabilityMeasureReverseGlobalLaw
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) [IsProbabilityMeasure final] :
    IsProbabilityMeasure (reverseGlobalLaw final generator duration) := by
  unfold reverseGlobalLaw
  exact Measure.isProbabilityMeasure_map measurable_concatenateWindows.aemeasurable

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
private theorem measurableSet_windowsTotal
    {M : ℕ} (duration : Fin M → NNReal) :
    MeasurableSet {γ : Path Ω M |
      ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i} := by
  rw [show {γ : Path Ω M |
      ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i} =
      ⋂ i, (fun γ => windowAt (Ω := Ω) (M := M) γ i) ⁻¹'
        {w | FullPath.totalHoldingTime w = duration i} by ext; simp]
  exact MeasurableSet.iInter fun i =>
    ((FullPath.measurable_totalHoldingTime.eq_const (duration i)).setOf).preimage
      (measurable_windowAt i)

private theorem forwardWindowKernel_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ p ∂G.forwardWindowKernel T x,
      FullPath.totalHoldingTime p.2 = T := by
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T x),
    FullPath.totalHoldingTime p.2 = T
  refine (ae_map_iff
    (FullPath.measurable_terminalState.prodMk measurable_id).aemeasurable
    ((FullPath.measurable_totalHoldingTime.comp measurable_snd).eq_const T).setOf).2 ?_
  filter_upwards [G.pathLawFrom_ae_totalHoldingTime T x] with γ hγ
  exact hγ

private theorem reverseWindowKernel_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (y : Ω) :
    ∀ᵐ p ∂G.reverseWindowKernel T y,
      FullPath.totalHoldingTime p.2 = T := by
  let record : FullPath Ω → Ω × FullPath Ω :=
    fun γ => (FullPath.terminalState γ, FullPath.reverse γ)
  change ∀ᵐ p ∂Measure.map record (G.pathLawFrom T y),
    FullPath.totalHoldingTime p.2 = T
  refine (ae_map_iff
    (FullPath.measurable_terminalState.prodMk
      FullPath.measurable_reverse).aemeasurable
    ((FullPath.measurable_totalHoldingTime.comp measurable_snd).eq_const T).setOf).2 ?_
  filter_upwards [G.pathLawFrom_ae_totalHoldingTime T y] with γ hγ
  rcases γ with ⟨n, γ⟩
  simpa [record, FullPath.reverse, FullPath.totalHoldingTime] using hγ

private theorem forwardDrivenLaw_ae_windowsTotal :
    ∀ {M : ℕ} (initial : Measure Ω)
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal),
      ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
        ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i
  | 0, initial, generator, duration => by simp
  | M + 1, initial, generator, duration => by
      have hpast := forwardDrivenLaw_ae_windowsTotal initial
        (fun i : Fin M => generator i.castSucc)
        (fun i : Fin M => duration i.castSucc)
      simp only [forwardDrivenLaw, Marked.reversedForwardPathMeasure]
      let prepend := Marked.prependEquiv (Ω := Ω) (Λ := FullPath Ω) M
      have hset := measurableSet_windowsTotal (Ω := Ω) duration
      refine (ae_map_iff prepend.measurable.aemeasurable hset).2 ?_
      apply Measure.ae_compProd_of_ae_ae
      · exact hset.preimage prepend.measurable
      · filter_upwards [hpast] with past hpast
        filter_upwards
          [forwardWindowKernel_ae_totalHoldingTime (generator (Fin.last M))
            (duration (Fin.last M)) past.1] with window hwindow
        change ∀ i, FullPath.totalHoldingTime
          (windowAt ((window.1,
            (((past.1, window.2), past.2) :
              Marked.MarkedContinuation Ω (FullPath Ω) (M + 1))) :
                Path Ω (M + 1)) i) = duration i
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hwindow
        · simpa using hpast j

private theorem reverseContinuationKernel_ae_windowsTotal :
    ∀ {M : ℕ}
      (generator : Fin M → FiniteJumpGenerator Ω)
      (duration : Fin M → NNReal) (endpoint : Ω),
      ∀ᵐ past ∂Marked.reverseContinuationKernel
          (fun i => (generator i).reverseWindowKernel (duration i)) endpoint,
        ∀ i, FullPath.totalHoldingTime
          (windowAt (endpoint, past) i) = duration i
  | 0, generator, duration, endpoint => by simp
  | M + 1, generator, duration, endpoint => by
      simp only [Marked.reverseContinuationKernel]
      have hrecord : Measurable
          (fun past : Marked.MarkedContinuation Ω (FullPath Ω) (M + 1) =>
            (endpoint, past)) := by fun_prop
      have hset :=
        (measurableSet_windowsTotal (Ω := Ω) duration).preimage hrecord
      apply Kernel.ae_compProd_of_ae_ae
      · exact hset
      · filter_upwards
          [reverseWindowKernel_ae_totalHoldingTime
            (generator (Fin.last M)) (duration (Fin.last M)) endpoint] with
            window hwindow
        have hpast := reverseContinuationKernel_ae_windowsTotal
          (fun i : Fin M => generator i.castSucc)
          (fun i : Fin M => duration i.castSucc) window.1
        filter_upwards [hpast] with past hpast
        change ∀ i, FullPath.totalHoldingTime
          (windowAt ((endpoint,
            (((window.1, window.2), past) :
              Marked.MarkedContinuation Ω (FullPath Ω) (M + 1))) :
                Path Ω (M + 1)) i) = duration i
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [windowAt_last]
          exact hwindow
        · rw [windowAt_castSucc]
          exact hpast j

private theorem reverseDrivenLaw_ae_windowsTotal
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseDrivenLaw final generator duration,
      ∀ i, FullPath.totalHoldingTime (windowAt γ i) = duration i := by
  unfold reverseDrivenLaw Marked.reversePathMeasure
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_windowsTotal (Ω := Ω) duration
  · filter_upwards [] with endpoint
    exact reverseContinuationKernel_ae_windowsTotal
      generator duration endpoint

/-- Almost every forward driven carrier has exact window horizons and no jump
at the local time-zero seams. -/
theorem forwardDrivenLaw_ae_windowRegular
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
      ∀ i, ¬FullPath.HasJumpAt 0 (windowAt γ i) ∧
        FullPath.totalHoldingTime (windowAt γ i) = duration i := by
  filter_upwards
    [forwardDrivenLaw_ae_isProtocolValid initial generator duration,
      forwardDrivenLaw_ae_windowsTotal initial generator duration] with γ hvalid htotal
  exact fun i =>
    ⟨FullPath.not_hasJumpAt_zero_of_isValid _ (hvalid.2 i), htotal i⟩

/-- Almost every reverse driven carrier has exact window horizons and no jump
at the local time-zero seams. -/
theorem reverseDrivenLaw_ae_windowRegular
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseDrivenLaw final generator duration,
      ∀ i, ¬FullPath.HasJumpAt 0 (windowAt γ i) ∧
        FullPath.totalHoldingTime (windowAt γ i) = duration i := by
  filter_upwards
    [reverseDrivenLaw_ae_isProtocolValid final generator duration,
      reverseDrivenLaw_ae_windowsTotal final generator duration] with γ hvalid htotal
  exact fun i =>
    ⟨FullPath.not_hasJumpAt_zero_of_isValid _ (hvalid.2 i), htotal i⟩

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
private theorem trajectory_concatenateWindows_boundary_pointwise :
    ∀ {M : ℕ} (duration : Fin M → NNReal) (γ : Path Ω M),
      IsBoundaryConsistent γ →
      (∀ i, ¬FullPath.HasJumpAt 0 (windowAt γ i) ∧
        FullPath.totalHoldingTime (windowAt γ i) = duration i) →
      ∀ i : Fin M,
        FullPath.trajectory (concatenateWindows γ)
            ((boundaryTime duration i.succ : NNReal) : ℝ) =
          endpointAt γ i
  | 0, duration, γ, hboundary, hregular, i => Fin.elim0 i
  | M + 1, duration, γ, hboundary, hregular, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have htotal :
            FullPath.totalHoldingTime (concatenateWindows γ) =
              ∑ k, duration k := by
          rw [totalHoldingTime_concatenateWindows]
          exact Finset.sum_congr rfl fun k _ => (hregular k).2
        rw [show (Fin.last M).succ = Fin.last (M + 1) by ext; simp]
        rw [boundaryTime_last, ← htotal,
          FullPath.trajectory_total_eq_terminal,
          terminalState_concatenateWindows hboundary, endpointAt_last]
      · let past : Path Ω M := (γ.2.1.1, γ.2.2)
        let pastDuration : Fin M → NNReal :=
          fun k => duration k.castSucc
        have hpastBoundary : IsBoundaryConsistent past := hboundary.2.2
        have hpastRegular : ∀ k,
            ¬FullPath.HasJumpAt 0 (windowAt past k) ∧
              FullPath.totalHoldingTime (windowAt past k) = pastDuration k := by
          intro k
          simpa [past, pastDuration] using hregular k.castSucc
        have hih := trajectory_concatenateWindows_boundary_pointwise
          pastDuration past hpastBoundary hpastRegular j
        have hidx : (j.castSucc).succ = j.succ.castSucc := by
          apply Fin.ext
          rfl
        have htime : boundaryTime duration (j.castSucc).succ =
            boundaryTime pastDuration j.succ := by
          rw [hidx, boundaryTime_castSucc]
        have hpastTotal :
            FullPath.totalHoldingTime (concatenateWindows past) =
              boundaryTime pastDuration (Fin.last M) := by
          rw [boundaryTime_last, totalHoldingTime_concatenateWindows]
          exact Finset.sum_congr rfl fun k _ => (hpastRegular k).2
        have hle :
            ((boundaryTime pastDuration j.succ : NNReal) : ℝ) ≤
              (FullPath.totalHoldingTime (concatenateWindows past) : ℝ) := by
          rw [hpastTotal]
          exact_mod_cast boundaryTime_le_last pastDuration j.succ
        by_cases hlt :
            ((boundaryTime pastDuration j.succ : NNReal) : ℝ) <
              (FullPath.totalHoldingTime (concatenateWindows past) : ℝ)
        · rw [concatenateWindows, htime]
          rw [FullPath.trajectory_concat_left _ _ hlt]
          simpa [past] using hih
        · have hge :
              (FullPath.totalHoldingTime (concatenateWindows past) : ℝ) ≤
                ((boundaryTime pastDuration j.succ : NNReal) : ℝ) :=
            le_of_not_gt hlt
          have heq :
              ((boundaryTime pastDuration j.succ : NNReal) : ℝ) =
                (FullPath.totalHoldingTime (concatenateWindows past) : ℝ) :=
            le_antisymm hle hge
          have hmatch :
              FullPath.terminalState (concatenateWindows past) =
                FullPath.initialState γ.2.1.2 :=
            (terminalState_concatenateWindows hpastBoundary).trans
              hboundary.1.symm
          have hno : ¬FullPath.HasJumpAt 0 γ.2.1.2 := by
            simpa using (hregular (Fin.last M)).1
          rw [concatenateWindows, htime]
          rw [FullPath.trajectory_concat_right _ _ hmatch hge]
          rw [heq, sub_self,
            FullPath.trajectory_zero_of_not_hasJumpAt_zero _ hno]
          calc
            FullPath.initialState γ.2.1.2 =
                FullPath.terminalState (concatenateWindows past) := hmatch.symm
            _ = FullPath.trajectory (concatenateWindows past)
                ((boundaryTime pastDuration j.succ : NNReal) : ℝ) := by
              rw [heq, FullPath.trajectory_total_eq_terminal]
            _ = endpointAt γ j.castSucc := by
              simpa [past] using hih

/-- Almost every concatenated forward chart agrees with the marked carrier at
every protocol boundary. -/
theorem trajectory_concatenateWindows_boundary_ae
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
      ∀ i : Fin M,
        FullPath.trajectory (concatenateWindows γ)
            ((boundaryTime duration i.succ : NNReal) : ℝ) =
          endpointAt γ i := by
  filter_upwards
    [forwardDrivenLaw_ae_isBoundaryConsistent initial generator duration,
      forwardDrivenLaw_ae_windowRegular initial generator duration] with γ hboundary hregular
  exact trajectory_concatenateWindows_boundary_pointwise
    duration γ hboundary hregular

/-- Almost every concatenated reverse chart agrees with the marked carrier at
every protocol boundary. -/
theorem trajectory_concatenateWindows_boundary_ae_reverse
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseDrivenLaw final generator duration,
      ∀ i : Fin M,
        FullPath.trajectory (concatenateWindows γ)
            ((boundaryTime duration i.succ : NNReal) : ℝ) =
          endpointAt γ i := by
  filter_upwards
    [reverseDrivenLaw_ae_isBoundaryConsistent final generator duration,
      reverseDrivenLaw_ae_windowRegular final generator duration] with γ hboundary hregular
  exact trajectory_concatenateWindows_boundary_pointwise
    duration γ hboundary hregular

/-- Pulling global trajectory work back to the marked carrier recovers the
original endpoint work almost surely under the forward law. -/
theorem work_comp_concatenateWindows_ae
    {M : ℕ} (initial : Measure Ω)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardDrivenLaw initial generator duration,
      globalWork energy duration (concatenateWindows γ) = work energy γ := by
  filter_upwards
    [trajectory_concatenateWindows_boundary_ae initial generator duration] with γ hboundary
  rw [globalWork, work_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hboundary i]

/-- Pulling global trajectory work back to the marked carrier recovers the
original endpoint work almost surely under the reverse law. -/
theorem work_comp_concatenateWindows_ae_reverse
    {M : ℕ} (final : Measure Ω)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseDrivenLaw final generator duration,
      globalWork energy duration (concatenateWindows γ) = work energy γ := by
  filter_upwards
    [trajectory_concatenateWindows_boundary_ae_reverse
      final generator duration] with γ hboundary
  rw [globalWork, work_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hboundary i]

/-- The global forward work distribution is the marked-carrier work
distribution. -/
theorem map_globalWork_forwardGlobalLaw
    {M : ℕ} (initial : Measure Ω)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    (forwardGlobalLaw initial generator duration).map
        (globalWork energy duration) =
      (forwardDrivenLaw initial generator duration).map (work energy) := by
  unfold forwardGlobalLaw
  rw [Measure.map_map
    (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
    measurable_concatenateWindows]
  apply Measure.map_congr
  exact work_comp_concatenateWindows_ae initial energy generator duration

/-- The global reverse work distribution is the marked-carrier work
distribution. -/
theorem map_globalWork_reverseGlobalLaw
    {M : ℕ} (final : Measure Ω)
    (energy : Fin (M + 1) → Ω → ℝ)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    (reverseGlobalLaw final generator duration).map
        (globalWork energy duration) =
      (reverseDrivenLaw final generator duration).map (work energy) := by
  unfold reverseGlobalLaw
  rw [Measure.map_map
    (measurable_globalWork energy duration fun _ => Measurable.of_discrete)
    measurable_concatenateWindows]
  apply Measure.map_congr
  exact work_comp_concatenateWindows_ae_reverse
    final energy generator duration

/-- The forward global law is concentrated on valid concatenated charts. -/
theorem forwardGlobalLaw_ae_isValid
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardGlobalLaw initial generator duration,
      FullPath.IsValid (∑ i, duration i) γ := by
  unfold forwardGlobalLaw
  rw [ae_map_iff measurable_concatenateWindows.aemeasurable
    (FullPath.measurableSet_isValid (∑ i, duration i))]
  filter_upwards
    [forwardDrivenLaw_ae_isProtocolValid initial generator duration,
      forwardDrivenLaw_ae_windowsTotal initial generator duration] with γ hvalid htotal
  exact isValid_concatenateWindows duration γ hvalid.2
    (fun i => (htotal i).le)

/-- The forward global chart exactly fills the sum of all window durations. -/
theorem forwardGlobalLaw_ae_totalHoldingTime
    {M : ℕ} (initial : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂forwardGlobalLaw initial generator duration,
      FullPath.totalHoldingTime γ = ∑ i, duration i := by
  unfold forwardGlobalLaw
  rw [ae_map_iff measurable_concatenateWindows.aemeasurable
    (FullPath.measurable_totalHoldingTime.eq_const (∑ i, duration i)).setOf]
  filter_upwards
    [forwardDrivenLaw_ae_windowsTotal initial generator duration] with γ htotal
  rw [totalHoldingTime_concatenateWindows]
  exact Finset.sum_congr rfl fun i _ => htotal i

/-- The reverse global law is concentrated on valid concatenated charts. -/
theorem reverseGlobalLaw_ae_isValid
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseGlobalLaw final generator duration,
      FullPath.IsValid (∑ i, duration i) γ := by
  unfold reverseGlobalLaw
  rw [ae_map_iff measurable_concatenateWindows.aemeasurable
    (FullPath.measurableSet_isValid (∑ i, duration i))]
  filter_upwards
    [reverseDrivenLaw_ae_isProtocolValid final generator duration,
      reverseDrivenLaw_ae_windowsTotal final generator duration] with γ hvalid htotal
  exact isValid_concatenateWindows duration γ hvalid.2
    (fun i => (htotal i).le)

/-- The reverse global chart exactly fills the sum of all window durations. -/
theorem reverseGlobalLaw_ae_totalHoldingTime
    {M : ℕ} (final : Measure Ω)
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) :
    ∀ᵐ γ ∂reverseGlobalLaw final generator duration,
      FullPath.totalHoldingTime γ = ∑ i, duration i := by
  unfold reverseGlobalLaw
  rw [ae_map_iff measurable_concatenateWindows.aemeasurable
    (FullPath.measurable_totalHoldingTime.eq_const (∑ i, duration i)).setOf]
  filter_upwards
    [reverseDrivenLaw_ae_windowsTotal final generator duration] with γ htotal
  rw [totalHoldingTime_concatenateWindows]
  exact Finset.sum_congr rfl fun i _ => htotal i

end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
