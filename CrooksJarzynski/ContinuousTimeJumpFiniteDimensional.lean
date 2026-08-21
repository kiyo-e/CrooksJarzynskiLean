/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatPathLawBridge
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

@[simp]
theorem reverse_prependEquiv (n : ℕ) (p : Trajectory Ω n × Ω) :
    Trajectory.reverse ((prependEquiv n) p) =
      appendState (Trajectory.reverse p.1, p.2) := by
  simp [appendState]

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

end Markov

end MeasureProtocol
end CrooksJarzynski
