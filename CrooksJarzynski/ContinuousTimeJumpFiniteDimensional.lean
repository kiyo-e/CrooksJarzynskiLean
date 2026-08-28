/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatPathLawBridge
import CrooksJarzynski.MeasureProtocolFiniteBridge
import CrooksJarzynski.MeasureProtocolMarginals
import CrooksJarzynski.MeasureProtocolPaths

/-!
# Finite-dimensional distributions of continuous-time jump paths

This module identifies the finite-dimensional marginals of the fixed-initial
continuous-time path law with the chronological finite-path measures generated
by its transition kernels.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Sample a complete continuous-time path at finitely many observation times. -/
noncomputable def sampleAt {n : ℕ} (time : Fin (n + 1) → NNReal) :
    FullPath Ω → Trajectory Ω n :=
  fun γ => Trajectory.ofFn fun i => trajectory γ (time i)

@[fun_prop]
theorem measurable_sampleAt {n : ℕ} (time : Fin (n + 1) → NNReal) :
    Measurable (sampleAt (Ω := Ω) time) := by
  apply Trajectory.measurable_ofFn.comp
  refine measurable_pi_iff.2 ?_
  intro i
  exact measurable_trajectory (time i)

end FullPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Sampling only up to `S` has the same law under every later path horizon. -/
theorem map_pathLawFrom_sampleAt_horizon_le
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (hST : S ≤ T) (x : Ω)
    {n : ℕ} (time : Fin (n + 1) → NNReal)
    (hlast : time (Fin.last n) ≤ S) (hmono : Monotone time) :
    (G.pathLawFrom T x).map (FullPath.sampleAt time) =
      (G.pathLawFrom S x).map (FullPath.sampleAt time) := by
  have hdecomp : T = S + (T - S) := by
    rw [add_comm, tsub_add_cancel_of_le hST]
  rw [hdecomp, G.pathLawFrom_add]
  have hconcat : Measurable
      (fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2) :=
    FullPath.measurable_concat_prod_of_point x
  rw [Measure.map_map (FullPath.measurable_sampleAt time) hconcat]
  have hsample :
      (FullPath.sampleAt time ∘
        fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2) =ᵐ[
          G.pathLawFrom S x ⊗ₘ G.continuationPathKernel (T - S)]
        (FullPath.sampleAt time ∘ Prod.fst) := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (((FullPath.measurable_sampleAt time).comp hconcat).eq
        ((FullPath.measurable_sampleAt time).comp measurable_fst)).setOf
    · filter_upwards [G.pathLawFrom_ae_totalHoldingTime S x,
        G.pathLawFrom_ae_trajectory_horizon S x] with γ htotal hhorizon
      rw [G.continuationPathKernel_apply]
      filter_upwards [G.pathLawFrom_ae_initialState (T - S)
          (FullPath.terminalState γ),
        G.pathLawFrom_ae_trajectory_zero (T - S)
          (FullPath.terminalState γ)] with δ hinitial hzero
      apply Trajectory.ext
      intro i
      simp only [Function.comp_apply, FullPath.sampleAt,
        Trajectory.stateAt_ofFn]
      have htime : time i ≤ S :=
        (hmono (Fin.le_last i)).trans hlast
      by_cases hlt : time i < S
      · apply FullPath.trajectory_concat_left
        rw [htotal]
        exact_mod_cast hlt
      · have heq : time i = S := le_antisymm htime (not_lt.mp hlt)
        have hright := FullPath.trajectory_concat_right γ δ
          hinitial.symm (t := (time i : ℝ))
            (by rw [htotal, heq])
        rw [hright, htotal, heq]
        norm_num
        exact hzero.trans hhorizon.symm
  rw [Measure.map_congr hsample]
  rw [← Measure.map_map (FullPath.measurable_sampleAt time) measurable_fst]
  change
    ((G.pathLawFrom S x ⊗ₘ G.continuationPathKernel (T - S)).fst).map
        (FullPath.sampleAt time) =
      (G.pathLawFrom S x).map (FullPath.sampleAt time)
  rw [Measure.fst_compProd]

end FiniteJumpGenerator

end ContinuousTimeJump

namespace Markov

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The last state of a chronological finite trajectory. -/
def chronologicalLast {n : ℕ} (γ : Trajectory Ω n) : Ω :=
  finalState γ.1 γ.2

@[fun_prop]
theorem measurable_chronologicalLast {n : ℕ} :
    Measurable (chronologicalLast (Ω := Ω) (n := n)) := by
  rw [show chronologicalLast (Ω := Ω) (n := n) =
      fun γ : Trajectory Ω n => Trajectory.stateAt γ (Fin.last n) by
    funext γ
    exact (Trajectory.stateAt_last γ).symm]
  exact (measurable_pi_apply (Fin.last n)).comp
    Trajectory.measurable_stateAt

/-- Append a newly sampled endpoint to a chronological finite trajectory. -/
noncomputable def appendState {n : ℕ} (p : Trajectory Ω n × Ω) :
    Trajectory Ω (n + 1) :=
  Trajectory.reverse
    ((prependEquiv n) (Trajectory.reverse p.1, p.2))

@[fun_prop]
theorem measurable_appendState {n : ℕ} :
    Measurable (appendState (Ω := Ω) (n := n)) := by
  exact Trajectory.measurable_reverse.comp
    ((prependEquiv n).measurable.comp
      ((Trajectory.measurable_reverse.comp measurable_fst).prodMk
        measurable_snd))

theorem reverse_prependEquiv (n : ℕ) (p : Trajectory Ω n × Ω) :
    Trajectory.reverse ((prependEquiv n) p) =
      appendState (Trajectory.reverse p.1, p.2) := by
  simp [appendState]

@[simp]
theorem stateAt_appendState_castSucc {n : ℕ}
    (p : Trajectory Ω n × Ω) (i : Fin (n + 1)) :
    Trajectory.stateAt (appendState p) i.castSucc =
      Trajectory.stateAt p.1 i := by
  rw [appendState, Trajectory.stateAt_reverse]
  rw [Trajectory.rev_castSucc_edge]
  change Trajectory.stateAt (Trajectory.reverse p.1) i.rev =
    Trajectory.stateAt p.1 i
  rw [Trajectory.stateAt_reverse]
  simp

@[simp]
theorem stateAt_appendState_last {n : ℕ} (p : Trajectory Ω n × Ω) :
    Trajectory.stateAt (appendState p) (Fin.last (n + 1)) = p.2 := by
  rw [appendState, Trajectory.stateAt_last, Trajectory.finalState_reverse]
  rfl

/-- Peel the last transition from a chronological forward finite-path law. -/
theorem chronologicalForwardPathMeasure_succ
    {n : ℕ} (initial : Measure Ω)
    (forward : Fin (n + 1) → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure initial]
    [hforward : ∀ i : Fin (n + 1), IsMarkovKernel (forward i)] :
    chronologicalForwardPathMeasure initial forward =
      ((chronologicalForwardPathMeasure initial
          (fun i : Fin n => forward i.castSucc)) ⊗ₘ
        (forward (Fin.last n)).comap
          (chronologicalLast (Ω := Ω) (n := n))
          (measurable_chronologicalLast (Ω := Ω) (n := n))).map
            (appendState (Ω := Ω) (n := n)) := by
  let forwardPrefix : Fin n → ProbabilityTheory.Kernel Ω Ω :=
    fun i => forward i.castSucc
  let μ : Measure (Trajectory Ω n) :=
    reversedForwardPathMeasure initial forwardPrefix
  let κ : ProbabilityTheory.Kernel (Trajectory Ω n) Ω :=
    endpointKernel (forward (Fin.last n)) n
  let e : Trajectory Ω n ≃ᵐ Trajectory Ω n :=
    Trajectory.reverseMeasurableEquiv Ω n
  letI : ∀ i : Fin n, IsMarkovKernel (forwardPrefix i) :=
    fun i => hforward i.castSucc
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsMarkovKernel κ := by
    dsimp [κ]
    infer_instance
  have htransport := map_compProd_prodMap_equiv μ κ e
  have hkernel :
      κ.comap e.symm e.symm.measurable =
        (forward (Fin.last n)).comap
          (chronologicalLast (Ω := Ω) (n := n))
          (measurable_chronologicalLast (Ω := Ω) (n := n)) := by
    apply ProbabilityTheory.Kernel.ext
    intro γ
    ext s hs
    simp only [ProbabilityTheory.Kernel.comap_apply]
    change (forward (Fin.last n)) (Trajectory.reverse γ).1 s =
      (forward (Fin.last n)) (finalState γ.1 γ.2) s
    rw [Trajectory.reverse_fst]
  unfold chronologicalForwardPathMeasure
  simp only [reversedForwardPathMeasure]
  rw [Measure.map_map
    (Trajectory.reverseMeasurableEquiv Ω (n + 1)).measurable
    (prependEquiv n).measurable]
  calc
    (μ ⊗ₘ κ).map
          (Trajectory.reverse ∘ fun p => (prependEquiv n) p) =
        (μ ⊗ₘ κ).map
          (appendState ∘ Prod.map (Trajectory.reverseMeasurableEquiv Ω n)
            (id : Ω → Ω)) := by
            apply Measure.map_congr
            filter_upwards [] with p
            exact reverse_prependEquiv n p
    _ = ((μ ⊗ₘ κ).map
          (Prod.map (Trajectory.reverseMeasurableEquiv Ω n)
            (id : Ω → Ω))).map
            appendState := by
          rw [Measure.map_map measurable_appendState
            ((Trajectory.reverseMeasurableEquiv Ω n).measurable.prodMap
              measurable_id)]
    _ = (μ.map (Trajectory.reverseMeasurableEquiv Ω n) ⊗ₘ
          κ.comap e.symm e.symm.measurable).map appendState := by
          rw [htransport]
    _ = (μ.map (Trajectory.reverseMeasurableEquiv Ω n) ⊗ₘ
          (forward (Fin.last n)).comap
            (chronologicalLast (Ω := Ω) (n := n))
            (measurable_chronologicalLast (Ω := Ω) (n := n))).map
              appendState := by
          rw [hkernel]

/-- A zero-step chronological path law records only its initial point. -/
theorem chronologicalForwardPathMeasure_zero_dirac
    [Fintype Ω] [MeasurableSingletonClass Ω] (x : Ω) :
    chronologicalForwardPathMeasure (Measure.dirac x)
        (fun i : Fin 0 => Fin.elim0 i) =
      Measure.dirac (Trajectory.ofFn fun _ => x) := by
  have hreverse (γ : Trajectory Ω 0) :
      (Trajectory.reverseMeasurableEquiv Ω 0).symm γ = γ := by
    apply Trajectory.ext
    intro i
    change Trajectory.stateAt (Trajectory.reverse γ) i =
      Trajectory.stateAt γ i
    rw [Trajectory.stateAt_reverse]
    congr 1
    apply Fin.ext
    omega
  apply Measure.ext_of_singleton
  intro γ
  rw [Measure.dirac_apply' _ (measurableSet_singleton γ)]
  unfold chronologicalForwardPathMeasure
  rw [Measure.map_apply
    (Trajectory.reverseMeasurableEquiv Ω 0).measurable
    (measurableSet_singleton γ)]
  rw [← (Trajectory.reverseMeasurableEquiv Ω 0).image_symm,
    Set.image_singleton, hreverse]
  simp only [reversedForwardPathMeasure, reversePathMeasure,
    reverseContinuationKernel]
  rw [MathlibBridge.compProd_singleton]
  rcases γ with ⟨y, c⟩
  cases c
  simp only [ProbabilityTheory.Kernel.deterministic_apply]
  by_cases hxy : x = y
  · subst y
    simp [Trajectory.ofFn]
    change (1 : ℝ≥0∞) = 1
    rfl
  · simp [hxy, Trajectory.ofFn]

end Markov

namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Mapping a continuation path to its endpoint gives the transition kernel
started from the prefix endpoint. -/
theorem map_continuationPathKernel_terminalState
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    (G.continuationPathKernel T).map FullPath.terminalState =
      ((G.transitionKernel T).comap FullPath.terminalState
        FullPath.measurable_terminalState) := by
  apply ProbabilityTheory.Kernel.ext
  intro γ
  rw [ProbabilityTheory.Kernel.map_apply _
      FullPath.measurable_terminalState γ,
    G.continuationPathKernel_apply,
    ProbabilityTheory.Kernel.comap_apply,
    G.transitionKernel_apply]

/-- The sampled path law obeys the same last-step recursion as the
chronological discrete-time path measure. -/
theorem map_pathLawFrom_sampleAt_succ
    (G : FiniteJumpGenerator Ω) (x : Ω) {n : ℕ}
    (time : Fin (n + 2) → NNReal) (hmono : Monotone time) :
    (G.pathLawFrom (time (Fin.last (n + 1))) x).map
        (FullPath.sampleAt time) =
      (((G.pathLawFrom (time (Fin.last n).castSucc) x).map
          (FullPath.sampleAt (fun i : Fin (n + 1) => time i.castSucc))) ⊗ₘ
        (G.transitionKernel
          (time (Fin.last (n + 1)) - time (Fin.last n).castSucc)).comap
            (Markov.chronologicalLast (Ω := Ω) (n := n))
            (Markov.measurable_chronologicalLast (Ω := Ω) (n := n))).map
              (Markov.appendState (Ω := Ω) (n := n)) := by
  let earlierTime : Fin (n + 1) → NNReal := fun i => time i.castSucc
  let cutTime : NNReal := time (Fin.last n).castSucc
  let endTime : NNReal := time (Fin.last (n + 1))
  let duration : NNReal := endTime - cutTime
  let μ : Measure (FullPath Ω) := G.pathLawFrom cutTime x
  let continuation := G.continuationPathKernel duration
  let sample : FullPath Ω → Trajectory Ω n :=
    FullPath.sampleAt earlierTime
  let endpoint : FullPath Ω → Ω := FullPath.terminalState
  let K : ProbabilityTheory.Kernel Ω Ω := G.transitionKernel duration
  let lastKernel : ProbabilityTheory.Kernel (Trajectory Ω n) Ω := K.comap
    (Markov.chronologicalLast (Ω := Ω) (n := n))
    (Markov.measurable_chronologicalLast (Ω := Ω) (n := n))
  have hcut : cutTime ≤ endTime := by
    exact hmono (Fin.le_last (Fin.last n).castSucc)
  have hadd : cutTime + duration = endTime := by
    dsimp [duration]
    rw [add_comm, tsub_add_cancel_of_le hcut]
  have hsampleLast :
      endpoint =ᵐ[μ]
        (Markov.chronologicalLast ∘ sample) := by
    dsimp [μ]
    filter_upwards [G.pathLawFrom_ae_trajectory_horizon cutTime x] with γ hγ
    change FullPath.terminalState γ =
      finalState (sample γ).1 (sample γ).2
    rw [← Trajectory.stateAt_last]
    simp only [sample, FullPath.sampleAt, Trajectory.stateAt_ofFn,
      earlierTime]
    exact hγ.symm
  have hkernelAE :
      K.comap endpoint FullPath.measurable_terminalState =ᵐ[μ]
        lastKernel.comap sample (FullPath.measurable_sampleAt earlierTime) := by
    filter_upwards [hsampleLast] with γ hγ
    apply Measure.ext
    intro s hs
    dsimp [lastKernel]
    change K (endpoint γ) s =
      K ((Markov.chronologicalLast ∘ sample) γ) s
    rw [hγ]
  have hjoint :
      (μ ⊗ₘ continuation).map (Prod.map sample endpoint) =
        μ.map sample ⊗ₘ lastKernel := by
    calc
      (μ ⊗ₘ continuation).map (Prod.map sample endpoint) =
          ((μ ⊗ₘ continuation).map (Prod.map id endpoint)).map
            (Prod.map sample id) := by
              rw [Measure.map_map
                ((FullPath.measurable_sampleAt earlierTime).prodMap
                  measurable_id)
                (measurable_id.prodMap FullPath.measurable_terminalState)]
              apply Measure.map_congr
              filter_upwards [] with p
              rfl
      _ = (μ ⊗ₘ continuation.map endpoint).map
            (Prod.map sample id) := by
              rw [← Measure.compProd_map FullPath.measurable_terminalState]
      _ = (μ ⊗ₘ K.comap endpoint
              FullPath.measurable_terminalState).map
            (Prod.map sample id) := by
              rw [G.map_continuationPathKernel_terminalState duration]
      _ = (μ ⊗ₘ lastKernel.comap sample
              (FullPath.measurable_sampleAt earlierTime)).map
            (Prod.map sample id) := by
              rw [Measure.compProd_congr hkernelAE]
      _ = μ.map sample ⊗ₘ lastKernel := by
              rw [map_compProd_eq_map_compProd_comap μ lastKernel sample
                (FullPath.measurable_sampleAt earlierTime)]
  change (G.pathLawFrom endTime x).map (FullPath.sampleAt time) =
    (μ.map sample ⊗ₘ lastKernel).map Markov.appendState
  rw [← hadd]
  rw [G.pathLawFrom_add]
  have hconcat : Measurable
      (fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2) :=
    FullPath.measurable_concat_prod_of_point x
  rw [Measure.map_map (FullPath.measurable_sampleAt time) hconcat]
  have hsampleConcat :
      (FullPath.sampleAt time ∘
        fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2) =ᵐ[
          μ ⊗ₘ continuation]
        (Markov.appendState ∘ Prod.map sample endpoint) := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (((FullPath.measurable_sampleAt time).comp hconcat).eq
        (Markov.measurable_appendState.comp
          ((FullPath.measurable_sampleAt earlierTime).comp measurable_fst |>.prodMk
            (FullPath.measurable_terminalState.comp measurable_snd)))).setOf
    · dsimp [μ]
      filter_upwards [G.pathLawFrom_ae_totalHoldingTime cutTime x,
        G.pathLawFrom_ae_trajectory_horizon cutTime x] with γ htotal hhorizon
      dsimp [continuation]
      rw [G.continuationPathKernel_apply]
      filter_upwards [G.pathLawFrom_ae_initialState duration
          (FullPath.terminalState γ),
        G.pathLawFrom_ae_trajectory_zero duration
          (FullPath.terminalState γ),
        G.pathLawFrom_ae_trajectory_horizon duration
          (FullPath.terminalState γ)] with δ hinitial hzero hend
      apply Trajectory.ext
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [FullPath.sampleAt,
          Trajectory.stateAt_ofFn, Markov.stateAt_appendState_last,
          endpoint]
        have hright := FullPath.trajectory_concat_right γ δ
          hinitial.symm (t := (endTime : ℝ))
            (by rw [htotal]; exact_mod_cast hcut)
        rw [hright, htotal]
        dsimp [duration] at hend
        simpa only [NNReal.coe_sub hcut] using hend
      · simp only [FullPath.sampleAt,
          Trajectory.stateAt_ofFn, Markov.stateAt_appendState_castSucc,
          sample, earlierTime]
        have htime : time j.castSucc ≤ cutTime := by
          exact hmono (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
        by_cases hlt : time j.castSucc < cutTime
        · apply FullPath.trajectory_concat_left
          rw [htotal]
          exact_mod_cast hlt
        · have heq : time j.castSucc = cutTime :=
            le_antisymm htime (not_lt.mp hlt)
          have hright := FullPath.trajectory_concat_right γ δ
            hinitial.symm (t := (time j.castSucc : ℝ))
              (by rw [htotal, heq])
          rw [hright, htotal, heq]
          norm_num
          exact hzero.trans hhorizon.symm
  rw [Measure.map_congr hsampleConcat]
  rw [← Measure.map_map Markov.measurable_appendState
    ((FullPath.measurable_sampleAt earlierTime).prodMap
      FullPath.measurable_terminalState)]
  rw [hjoint]

/-- At an exact final observation horizon, all sampled path coordinates have
the chronological transition-kernel law. -/
theorem pathLawFrom_finiteDimensional_eq_horizon
    (G : FiniteJumpGenerator Ω) (x : Ω) {n : ℕ}
    (time : Fin (n + 1) → NNReal)
    (hmono : Monotone time) (h0 : time 0 = 0) :
    (G.pathLawFrom (time (Fin.last n)) x).map
        (FullPath.sampleAt time) =
      Markov.chronologicalForwardPathMeasure (Measure.dirac x)
        (fun i : Fin n =>
          G.transitionKernel (time i.succ - time i.castSucc)) := by
  induction n with
  | zero =>
      rw [show time (Fin.last 0) = 0 by simpa using h0]
      have hsample :
          FullPath.sampleAt time =ᵐ[G.pathLawFrom 0 x]
            fun _ => Trajectory.ofFn fun _ => x := by
        filter_upwards [G.pathLawFrom_ae_trajectory_zero 0 x] with γ hγ
        apply Trajectory.ext
        intro i
        simp only [FullPath.sampleAt, Trajectory.stateAt_ofFn]
        rw [show time i = 0 by rw [Fin.eq_zero i, h0]]
        exact hγ
      rw [Measure.map_congr hsample]
      have hconst :
          (G.pathLawFrom 0 x).map
              (fun _ : FullPath Ω =>
                Trajectory.ofFn (n := 0) fun _ => x) =
            Measure.dirac (Trajectory.ofFn (n := 0) fun _ => x) := by
        apply Measure.ext
        intro s hs
        rw [Measure.map_apply measurable_const hs,
          Measure.dirac_apply' _ hs]
        by_cases hmem : Trajectory.ofFn (n := 0) (fun _ => x) ∈ s
        · simp [hmem, measure_univ]
        · simp [hmem]
      rw [hconst]
      exact Markov.chronologicalForwardPathMeasure_zero_dirac x |>.symm
  | succ n ih =>
      let earlierTime : Fin (n + 1) → NNReal := fun i => time i.castSucc
      have hmonoEarlier : Monotone earlierTime := fun _ _ hij =>
        hmono (Fin.castSucc_le_castSucc_iff.mpr hij)
      have hzeroEarlier : earlierTime 0 = 0 := by
        simpa [earlierTime] using h0
      rw [G.map_pathLawFrom_sampleAt_succ x time hmono]
      rw [ih earlierTime hmonoEarlier hzeroEarlier]
      rw [Markov.chronologicalForwardPathMeasure_succ]
      congr 2

/-- **Finite-dimensional distributions of the fixed-initial path law.**
Sampling the continuous-time construction at any monotone finite family of
times gives the chronological path measure of its transition kernels. -/
theorem pathLawFrom_finiteDimensional_eq
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω)
    {n : ℕ} (time : Fin (n + 1) → NNReal)
    (hmono : Monotone time) (h0 : time 0 = 0)
    (hT : time (Fin.last n) ≤ T) :
    (G.pathLawFrom T x).map (FullPath.sampleAt time) =
      Markov.chronologicalForwardPathMeasure (Measure.dirac x)
        (fun i : Fin n =>
          G.transitionKernel (time i.succ - time i.castSucc)) := by
  rw [G.map_pathLawFrom_sampleAt_horizon_le
    (time (Fin.last n)) T hT x time le_rfl hmono]
  exact G.pathLawFrom_finiteDimensional_eq_horizon x time hmono h0

/-- The atom of every finite-dimensional marginal is the initial-state
indicator times the product of the corresponding matrix-exponential entries. -/
theorem pathLawFrom_sampleAt_real_singleton_eq_exp_product
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω)
    {n : ℕ} (time : Fin (n + 1) → NNReal)
    (hmono : Monotone time) (h0 : time 0 = 0)
    (hT : time (Fin.last n) ≤ T) (γ : Trajectory Ω n) :
    ((G.pathLawFrom T x).map (FullPath.sampleAt time)).real {γ} =
      (if Trajectory.stateAt γ 0 = x then 1 else 0) *
        ∏ i : Fin n,
          NormedSpace.exp
              ((((time i.succ - time i.castSucc) : NNReal) : ℝ) • G.generator)
            (Trajectory.stateAt γ i.castSucc) (Trajectory.stateAt γ i.succ) := by
  let initial : FiniteDistribution Ω :=
    { prob := fun y => if y = x then 1 else 0
      nonneg := fun y => by split_ifs <;> positivity
      sum_prob := by simp }
  let K : Fin n → CrooksJarzynski.Kernel Ω := fun i y =>
    { prob := fun z =>
        (G.transitionKernel (time i.succ - time i.castSucc) y).real {z}
      nonneg := fun z => measureReal_nonneg
      sum_prob := by
        calc
          (∑ z, (G.transitionKernel
                (time i.succ - time i.castSucc) y).real {z}) =
              (G.transitionKernel
                (time i.succ - time i.castSucc) y).real
                (Finset.univ : Finset Ω) :=
            sum_measureReal_singleton (Finset.univ : Finset Ω)
          _ = (G.transitionKernel
                (time i.succ - time i.castSucc) y).real Set.univ := by simp
          _ = 1 := by
            rw [Measure.real_def, measure_univ, ENNReal.toReal_one] }
  have hinitial : initial.toMeasure = Measure.dirac x := by
    apply Measure.ext_of_singleton
    intro y
    rw [FiniteDistribution.toMeasure_singleton,
      Measure.dirac_apply' _ (measurableSet_singleton y)]
    by_cases hy : y = x
    · subst y
      simp [initial]
    · simp [initial, hy, Ne.symm hy]
  have hK (i : Fin n) :
      MathlibBridge.toKernel (K i) =
        G.transitionKernel (time i.succ - time i.castSucc) := by
    apply ProbabilityTheory.Kernel.ext
    intro y
    apply Measure.ext_of_singleton
    intro z
    rw [MathlibBridge.toKernel_singleton]
    change ENNReal.ofReal
        ((G.transitionKernel (time i.succ - time i.castSucc) y).real {z}) = _
    rw [Measure.real_def, ENNReal.ofReal_toReal]
    exact ne_of_lt measure_singleton_lt_top
  rw [G.pathLawFrom_finiteDimensional_eq T x time hmono h0 hT]
  rw [← hinitial]
  simp_rw [← hK]
  rw [Measure.real_def,
    MathlibBridge.chronologicalForwardPathMeasure_singleton]
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (initial.nonneg γ.1) (transitionWeight_nonneg K γ.1 γ.2))]
  rw [Trajectory.transitionWeight_eq_transitionProduct]
  simp only [Trajectory.transitionProduct, K]
  simp_rw [G.transitionKernel_real_singleton_eq_exp_generator]
  simp [initial]

/-- The state at any time before the path horizon has the corresponding
transition-kernel law. -/
theorem map_pathLawFrom_trajectory_eq_transitionKernel
    (G : FiniteJumpGenerator Ω) (T t : NNReal) (ht : t ≤ T) (x : Ω) :
    (G.pathLawFrom T x).map
        (fun γ => FullPath.trajectory γ t) =
      G.transitionKernel t x := by
  let time : Fin 1 → NNReal := fun _ => t
  let eval : Trajectory Ω 0 → Ω := fun γ => Trajectory.stateAt γ 0
  have heval : Measurable eval :=
    (measurable_pi_apply (0 : Fin 1)).comp Trajectory.measurable_stateAt
  have hsample := G.map_pathLawFrom_sampleAt_horizon_le
    t T ht x time le_rfl monotone_const
  have hmap := congrArg (fun μ : Measure (Trajectory Ω 0) => μ.map eval) hsample
  rw [Measure.map_map heval (FullPath.measurable_sampleAt time),
    Measure.map_map heval (FullPath.measurable_sampleAt time)] at hmap
  have hrestrict :
      (G.pathLawFrom T x).map (fun γ => FullPath.trajectory γ t) =
        (G.pathLawFrom t x).map (fun γ => FullPath.trajectory γ t) := by
    simpa [Function.comp_def, eval, time, FullPath.sampleAt,
      Trajectory.ofFn] using hmap
  calc
    (G.pathLawFrom T x).map (fun γ => FullPath.trajectory γ t) =
        (G.pathLawFrom t x).map (fun γ => FullPath.trajectory γ t) := hrestrict
    _ = (G.pathLawFrom t x).map FullPath.terminalState :=
      Measure.map_congr (G.pathLawFrom_ae_trajectory_horizon t x)
    _ = G.transitionKernel t x := (G.transitionKernel_apply t x).symm

/-- The finite distribution represented by one row of the transition kernel. -/
private noncomputable def transitionDistribution
    (G : FiniteJumpGenerator Ω) (t : NNReal) (x : Ω) :
    FiniteDistribution Ω where
  prob y := (G.transitionKernel t x).real {y}
  nonneg _ := measureReal_nonneg
  sum_prob := by
    calc
      (∑ y, (G.transitionKernel t x).real {y}) =
          (G.transitionKernel t x).real (Finset.univ : Finset Ω) :=
        sum_measureReal_singleton (Finset.univ : Finset Ω)
      _ = (G.transitionKernel t x).real Set.univ := by simp
      _ = 1 := by
        rw [Measure.real_def, measure_univ, ENNReal.toReal_one]

private theorem transitionDistribution_toMeasure
    (G : FiniteJumpGenerator Ω) (t : NNReal) (x : Ω) :
    (transitionDistribution G t x).toMeasure = G.transitionKernel t x := by
  apply Measure.ext_of_singleton
  intro y
  rw [FiniteDistribution.toMeasure_singleton]
  change ENNReal.ofReal ((G.transitionKernel t x).real {y}) = _
  rw [Measure.real_def, ENNReal.ofReal_toReal]
  exact ne_of_lt measure_singleton_lt_top

/-- **General finite-dimensional distributions.** Sampling the fixed-initial path law
at any monotone finite family of times, not necessarily starting at zero, gives the
chronological transition-kernel path measure started from the time-`time 0` marginal. -/
theorem pathLawFrom_finiteDimensional_eq_general
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω)
    {n : ℕ} (time : Fin (n + 1) → NNReal)
    (hmono : Monotone time) (hT : time (Fin.last n) ≤ T) :
    (G.pathLawFrom T x).map (FullPath.sampleAt time) =
      Markov.chronologicalForwardPathMeasure (G.transitionKernel (time 0) x)
        (fun i : Fin n =>
          G.transitionKernel (time i.succ - time i.castSucc)) := by
  rw [G.map_pathLawFrom_sampleAt_horizon_le
    (time (Fin.last n)) T hT x time le_rfl hmono]
  induction n with
  | zero =>
      let lift : Ω → Trajectory Ω 0 :=
        fun y => Trajectory.ofFn fun _ => y
      have hlift : Measurable lift := by
        apply Trajectory.measurable_ofFn.comp
        exact measurable_pi_iff.2 fun _ => measurable_id
      have hsample :
          FullPath.sampleAt time =
            lift ∘ fun γ : FullPath Ω => FullPath.trajectory γ (time 0) := by
        funext γ
        apply Trajectory.ext
        intro i
        simp only [FullPath.sampleAt, lift, Function.comp_apply,
          Trajectory.stateAt_ofFn]
        rw [Fin.eq_zero i]
      rw [show time (Fin.last 0) = time 0 by rfl, hsample]
      rw [← Measure.map_map hlift (FullPath.measurable_trajectory (time 0))]
      rw [G.map_pathLawFrom_trajectory_eq_transitionKernel
        (time 0) (time 0) le_rfl x]
      let initial := transitionDistribution G (time 0) x
      have hinitial : initial.toMeasure = G.transitionKernel (time 0) x := by
        simpa [initial] using transitionDistribution_toMeasure G (time 0) x
      rw [← hinitial]
      have hforward :
          (fun i : Fin 0 =>
              G.transitionKernel (time i.succ - time i.castSucc)) =
            fun i : Fin 0 => MathlibBridge.toKernel (Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      rw [hforward]
      apply Measure.ext_of_singleton
      intro γ
      rw [Measure.map_apply hlift (measurableSet_singleton γ)]
      have hpre : lift ⁻¹' {γ} = {Trajectory.stateAt γ 0} := by
        rcases γ with ⟨y, c⟩
        cases c
        ext z
        simp [lift, Trajectory.ofFn, Trajectory.stateAt]
      rw [hpre, FiniteDistribution.toMeasure_singleton,
        MathlibBridge.chronologicalForwardPathMeasure_singleton]
      simp [transitionWeight]
  | succ n ih =>
      let earlierTime : Fin (n + 1) → NNReal := fun i => time i.castSucc
      have hmonoEarlier : Monotone earlierTime := fun _ _ hij =>
        hmono (Fin.castSucc_le_castSucc_iff.mpr hij)
      have hTEarlier : earlierTime (Fin.last n) ≤ T :=
        (hmono (Fin.le_last (Fin.last n).castSucc)).trans hT
      rw [G.map_pathLawFrom_sampleAt_succ x time hmono]
      rw [ih earlierTime hmonoEarlier hTEarlier]
      rw [Markov.chronologicalForwardPathMeasure_succ]
      congr 2

/-- The atom of every general finite-dimensional marginal is the matrix-exponential
entry from the initial state times the product of matrix-exponential entries between
consecutive observation times. -/
theorem pathLawFrom_sampleAt_real_singleton_eq_exp_product_general
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω)
    {n : ℕ} (time : Fin (n + 1) → NNReal)
    (hmono : Monotone time) (hT : time (Fin.last n) ≤ T) (γ : Trajectory Ω n) :
    ((G.pathLawFrom T x).map (FullPath.sampleAt time)).real {γ} =
      NormedSpace.exp (((time 0 : NNReal) : ℝ) • G.generator) x
          (Trajectory.stateAt γ 0) *
        ∏ i : Fin n,
          NormedSpace.exp
              ((((time i.succ - time i.castSucc) : NNReal) : ℝ) • G.generator)
            (Trajectory.stateAt γ i.castSucc) (Trajectory.stateAt γ i.succ) := by
  let initial := transitionDistribution G (time 0) x
  let K : Fin n → CrooksJarzynski.Kernel Ω := fun i y =>
    transitionDistribution G (time i.succ - time i.castSucc) y
  have hinitial : initial.toMeasure = G.transitionKernel (time 0) x := by
    simpa [initial] using transitionDistribution_toMeasure G (time 0) x
  have hK (i : Fin n) :
      MathlibBridge.toKernel (K i) =
        G.transitionKernel (time i.succ - time i.castSucc) := by
    apply ProbabilityTheory.Kernel.ext
    intro y
    rw [MathlibBridge.toKernel_apply]
    simpa [K] using transitionDistribution_toMeasure G
      (time i.succ - time i.castSucc) y
  rw [G.pathLawFrom_finiteDimensional_eq_general T x time hmono hT]
  rw [← hinitial]
  simp_rw [← hK]
  rw [Measure.real_def,
    MathlibBridge.chronologicalForwardPathMeasure_singleton]
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (initial.nonneg γ.1) (transitionWeight_nonneg K γ.1 γ.2))]
  rw [Trajectory.transitionWeight_eq_transitionProduct]
  simp only [Trajectory.transitionProduct, K, initial,
    transitionDistribution]
  simp_rw [G.transitionKernel_real_singleton_eq_exp_generator]
  rw [Trajectory.stateAt_zero]

/-- The mass of observing a state at any time before the path horizon is the
corresponding entry of the matrix exponential. -/
theorem pathLawFrom_trajectory_real_singleton_eq_exp_generator
    (G : FiniteJumpGenerator Ω) (T t : NNReal) (ht : t ≤ T) (x y : Ω) :
    ((G.pathLawFrom T x).map
        (fun γ => FullPath.trajectory γ t)).real {y} =
      NormedSpace.exp ((t : ℝ) • G.generator) x y := by
  rw [G.map_pathLawFrom_trajectory_eq_transitionKernel T t ht x]
  exact G.transitionKernel_real_singleton_eq_exp_generator t x y

example (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    ((G.pathLawFrom T x).map FullPath.terminalState).real {y} =
      NormedSpace.exp ((T : ℝ) • G.generator) x y := by
  rw [← Measure.map_congr (G.pathLawFrom_ae_trajectory_horizon T x)]
  exact G.pathLawFrom_trajectory_real_singleton_eq_exp_generator T T le_rfl x y

end FiniteJumpGenerator
end ContinuousTimeJump

end MeasureProtocol
end CrooksJarzynski
