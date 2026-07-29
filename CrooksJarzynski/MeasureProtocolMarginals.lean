/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolPaths

/-!
# Finite marginals of the Ionescu–Tulcea trajectory measure

This module identifies every finite-dimensional marginal of
`MeasureProtocol.Markov.trajectoryMeasure` with the recursively constructed
finite-horizon forward path measure. The proof transports Mathlib's
Ionescu–Tulcea one-step law through a measurable equivalence between
`Finset.Iic n`-indexed prefixes and the project's recursive trajectory type.
-/

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Markov

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Restrict an infinite trajectory to its first `n + 1` states, in
chronological order. -/
def finitePrefix (n : ℕ) (x : ℕ → Ω) : Trajectory Ω n :=
  Trajectory.ofFn (fun i => x i.val)

theorem measurable_finitePrefix (n : ℕ) :
    Measurable (finitePrefix (Ω := Ω) n) := by
  apply Trajectory.measurable_ofFn.comp
  refine measurable_pi_iff.2 ?_
  intro i
  exact measurable_pi_apply i.val

/-- A prefix indexed by `Finset.Iic n` is measurably equivalent to the
reverse-oriented recursive trajectory used by the finite-horizon
construction. -/
noncomputable def reversedPrefixEquiv (n : ℕ) :
    ((i : Finset.Iic n) → Ω) ≃ᵐ Trajectory Ω n where
  toFun x := Trajectory.reverse
    (Trajectory.ofFn
      (fun i => x ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩))
  invFun γ j := Trajectory.stateAt (Trajectory.reverse γ)
    ⟨j.val, Nat.lt_succ_of_le (Finset.mem_Iic.mp j.property)⟩
  left_inv x := by
    funext j
    simp
  right_inv γ := by
    change Trajectory.reverse
      (Trajectory.ofFn (Trajectory.stateAt (Trajectory.reverse γ))) = γ
    rw [Trajectory.ofFn_stateAt, Trajectory.reverse_reverse]
  measurable_toFun := by
    apply Trajectory.measurable_reverse.comp
    apply Trajectory.measurable_ofFn.comp
    refine measurable_pi_iff.2 ?_
    intro i
    exact measurable_pi_apply
      (⟨i.val, Finset.mem_Iic.mpr
        (Nat.le_of_lt_succ i.isLt)⟩ : Finset.Iic n)
  measurable_invFun := by
    refine measurable_pi_iff.2 ?_
    intro j
    exact (measurable_pi_apply
      (⟨j.val, Nat.lt_succ_of_le
        (Finset.mem_Iic.mp j.property)⟩ : Fin (n + 1))).comp
        (Trajectory.measurable_stateAt.comp
          Trajectory.measurable_reverse)

@[simp]
theorem reversedPrefixEquiv_symm_last (n : ℕ) (γ : Trajectory Ω n) :
    historyLast n ((reversedPrefixEquiv (Ω := Ω) n).symm γ) = γ.1 := by
  change Trajectory.stateAt (Trajectory.reverse γ) (Fin.last n) = γ.1
  rw [Trajectory.stateAt_last, Trajectory.finalState_reverse]

theorem reversedPrefixEquiv_succ (n : ℕ)
    (x : (i : Finset.Iic (n + 1)) → Ω) :
    reversedPrefixEquiv (Ω := Ω) (n + 1) x =
      (x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩,
        reversedPrefixEquiv (Ω := Ω) n
          (fun i => x ⟨i.val,
            Finset.mem_Iic.mpr
              ((Finset.mem_Iic.mp i.property).trans (Nat.le_succ n))⟩)) := by
  apply Trajectory.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change
      (Trajectory.reverse
        (Trajectory.ofFn
          (fun i => x ⟨i.val,
            Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩))).1 =
        x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
    rw [Trajectory.reverse_fst, ← Trajectory.stateAt_last]
    exact congrFun
      (Trajectory.stateAt_ofFn
        (fun i : Fin (n + 2) =>
          x ⟨i.val, Finset.mem_Iic.mpr
            (Nat.le_of_lt_succ i.isLt)⟩))
      (Fin.last (n + 1))
  · change
      Trajectory.stateAt
          (reversedPrefixEquiv (Ω := Ω) (n + 1) x) j.succ =
        Trajectory.stateAt
          (reversedPrefixEquiv (Ω := Ω) n
            (fun i => x ⟨i.val,
              Finset.mem_Iic.mpr
                ((Finset.mem_Iic.mp i.property).trans (Nat.le_succ n))⟩)) j
    simp [reversedPrefixEquiv]

/-- Mapping the first coordinate of a composition-product measure through a
measurable equivalence is the same as mapping the measure and comapping the
kernel. -/
theorem map_compProd_prodMap_equiv
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (μ : Measure A) (κ : ProbabilityTheory.Kernel A C)
    [IsFiniteMeasure μ] [IsMarkovKernel κ] (e : A ≃ᵐ B) :
    (μ ⊗ₘ κ).map (Prod.map e id) =
      μ.map e ⊗ₘ κ.comap e.symm e.symm.measurable := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (e.measurable.prodMap measurable_id) (hs.prod ht)]
  have hpre :
      Prod.map e id ⁻¹' (s ×ˢ t) = (e ⁻¹' s) ×ˢ t := by
    ext x
    simp
  rw [hpre]
  rw [Measure.compProd_apply_prod (hs.preimage e.measurable) ht]
  rw [Measure.compProd_apply_prod hs ht]
  simp_rw [ProbabilityTheory.Kernel.comap_apply]
  simpa using (MeasureTheory.setLIntegral_map (μ := μ) hs
    ((κ.measurable_coe ht).comp e.symm.measurable) e.measurable).symm

theorem historyKernel_comap_reversedPrefixEquiv
    (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    (historyKernel K n).comap
        (reversedPrefixEquiv (Ω := Ω) n).symm
        (reversedPrefixEquiv (Ω := Ω) n).symm.measurable =
      endpointKernel (K n) n := by
  ext γ s hs
  simp [historyKernel, endpointKernel,
    reversedPrefixEquiv_symm_last]

/-- The finite marginal of the Ionescu–Tulcea law, expressed in the internal
reverse-oriented trajectory coordinates. -/
noncomputable def reversedFiniteMarginal
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    Measure (Trajectory Ω n) :=
  (trajectoryMeasure μ₀ K).map
    ((reversedPrefixEquiv (Ω := Ω) n) ∘ Preorder.frestrictLe n)

noncomputable instance instIsProbabilityMeasureReversedFiniteMarginal
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    IsProbabilityMeasure (reversedFiniteMarginal μ₀ K n) := by
  unfold reversedFiniteMarginal
  apply Measure.isProbabilityMeasure_map
  exact ((reversedPrefixEquiv (Ω := Ω) n).measurable.comp
    (measurable_frestrictLe n)).aemeasurable

/-- The finite marginal of the Ionescu–Tulcea law in chronological trajectory
coordinates `(x₀, …, xₙ)`. -/
noncomputable def finiteMarginal
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    Measure (Trajectory Ω n) :=
  (trajectoryMeasure μ₀ K).map (finitePrefix (Ω := Ω) n)

noncomputable instance instIsProbabilityMeasureFiniteMarginal
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    IsProbabilityMeasure (finiteMarginal μ₀ K n) := by
  unfold finiteMarginal
  apply Measure.isProbabilityMeasure_map
  exact (measurable_finitePrefix n).aemeasurable

/-- Every reverse-oriented finite marginal of the Ionescu–Tulcea law is the
recursively constructed finite-horizon forward path measure. -/
theorem reversedFiniteMarginal_eq_reversedForwardPathMeasure
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    reversedFiniteMarginal μ₀ K n =
      reversedForwardPathMeasure μ₀ (fun i : Fin n => K i.val) := by
  induction n with
  | zero =>
      unfold reversedFiniteMarginal
      rw [← Measure.map_map
        (reversedPrefixEquiv (Ω := Ω) 0).measurable
        (measurable_frestrictLe 0)]
      unfold trajectoryMeasure ProbabilityTheory.Kernel.trajMeasure
      rw [Measure.map_comp _ _ (by fun_prop)]
      rw [ProbabilityTheory.Kernel.traj_map_frestrictLe]
      rw [ProbabilityTheory.Kernel.partialTraj_self]
      rw [Measure.id_comp]
      rw [Measure.map_map
        (reversedPrefixEquiv (Ω := Ω) 0).measurable
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => Ω)).symm.measurable]
      simp only [reversedForwardPathMeasure, reversePathMeasure,
        reverseContinuationKernel]
      rw [Measure.compProd_deterministic]
      congr 1
  | succ n ih =>
      let e := reversedPrefixEquiv (Ω := Ω) n
      have hstep := trajectoryMeasure_step μ₀ K n
      have htransport := congrArg
        (fun μ : Measure (((i : Finset.Iic n) → Ω) × Ω) =>
          μ.map (Prod.map e id))
        hstep
      rw [map_compProd_prodMap_equiv] at htransport
      rw [historyKernel_comap_reversedPrefixEquiv] at htransport
      have hprefix :
          ((trajectoryMeasure μ₀ K).map (Preorder.frestrictLe n)).map e =
            reversedFiniteMarginal μ₀ K n := by
        unfold reversedFiniteMarginal
        rw [Measure.map_map e.measurable (measurable_frestrictLe n)]
      rw [hprefix, ih] at htransport
      have hfunctions :
          (((prependEquiv (Ω := Ω) n) ∘ Prod.map e id) ∘
              (fun x : ℕ → Ω =>
                (Preorder.frestrictLe n x, x (n + 1)))) =
            ((reversedPrefixEquiv (Ω := Ω) (n + 1)) ∘
              Preorder.frestrictLe (n + 1)) := by
        funext x
        change
          (x (n + 1), e (Preorder.frestrictLe n x)) =
            reversedPrefixEquiv (Ω := Ω) (n + 1)
              (Preorder.frestrictLe (n + 1) x)
        rw [reversedPrefixEquiv_succ]
        rfl
      unfold reversedFiniteMarginal
      simp only [reversedForwardPathMeasure]
      change
        (trajectoryMeasure μ₀ K).map
            ((reversedPrefixEquiv (Ω := Ω) (n + 1)) ∘
              Preorder.frestrictLe (n + 1)) =
          ((reversedForwardPathMeasure μ₀
              (fun i : Fin n => K i.val) ⊗ₘ
            endpointKernel (K n) n).map
              (prependEquiv (Ω := Ω) n))
      have hmap := congrArg
        (fun μ : Measure (Trajectory Ω n × Ω) =>
          μ.map (prependEquiv (Ω := Ω) n))
        htransport
      rw [Measure.map_map
        (prependEquiv (Ω := Ω) n).measurable
        (e.measurable.prodMap measurable_id)] at hmap
      rw [Measure.map_map
        ((prependEquiv (Ω := Ω) n).measurable.comp
          (e.measurable.prodMap measurable_id))
        ((measurable_frestrictLe n).prodMk
          (measurable_pi_apply (n + 1)))] at hmap
      rw [hfunctions] at hmap
      exact hmap.symm

/-- Every chronological finite-dimensional marginal of the Ionescu–Tulcea law
is exactly the chronological finite-horizon forward path measure. -/
theorem finiteMarginal_eq_chronologicalForwardPathMeasure
    (μ₀ : Measure Ω) (K : ℕ → ProbabilityTheory.Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (n : ℕ) :
    finiteMarginal μ₀ K n =
      chronologicalForwardPathMeasure μ₀
        (fun i : Fin n => K i.val) := by
  unfold finiteMarginal chronologicalForwardPathMeasure
  rw [← reversedFiniteMarginal_eq_reversedForwardPathMeasure μ₀ K n]
  unfold reversedFiniteMarginal
  rw [Measure.map_map
    (Trajectory.reverseMeasurableEquiv Ω n).measurable
    ((reversedPrefixEquiv (Ω := Ω) n).measurable.comp
      (measurable_frestrictLe n))]
  congr 1
  funext x
  change Trajectory.ofFn (fun i : Fin (n + 1) => x i.val) =
    Trajectory.reverse
      (Trajectory.reverse
        (Trajectory.ofFn (fun i : Fin (n + 1) => x i.val)))
  rw [Trajectory.reverse_reverse]

end Markov
end MeasureProtocol
end CrooksJarzynski
