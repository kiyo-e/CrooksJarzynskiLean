/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatLaw
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Concatenation of finite-generator path laws

This module lifts the fixed-sector convolution law to the normalized law on
complete finite-jump paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Reindex a sector and a cut count by the prefix and suffix jump counts. -/
def cutSectorEquiv : (Σ k : ℕ, Fin (k + 1)) ≃ ℕ × ℕ :=
  (Equiv.sigmaCongrRight fun k =>
    (Finset.Nat.antidiagonalEquivFin k).symm).trans
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd

@[simp]
theorem cutSectorEquiv_apply_fst (k : ℕ) (r : Fin (k + 1)) :
    (cutSectorEquiv ⟨k, r⟩).1 = r.val := by
  simp [cutSectorEquiv]

@[simp]
theorem cutSectorEquiv_apply_add (k : ℕ) (r : Fin (k + 1)) :
    (cutSectorEquiv ⟨k, r⟩).1 + (cutSectorEquiv ⟨k, r⟩).2 = k := by
  simp [cutSectorEquiv]
  omega

/-- A fixed jump-count sector, injected into the complete path space. -/
noncomputable def fullSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ProbabilityTheory.Kernel Ω (FullPath Ω) :=
  (G.sectorKernel T n).map (Sigma.mk n)

@[simp]
theorem fullSectorKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) (x : Ω) :
    G.fullSectorKernel T n x =
      FullPath.liftMeasure n (G.sectorLawFrom T x n) := by
  rw [fullSectorKernel, ProbabilityTheory.Kernel.map_apply _
    (FullPath.measurable_mk n)]
  rfl

noncomputable instance instIsFiniteKernelFullSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    IsFiniteKernel (G.fullSectorKernel T n) := by
  unfold fullSectorKernel
  infer_instance

/-- The complete path kernel, written as the sum of its jump-count sectors. -/
noncomputable def pathKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    ProbabilityTheory.Kernel Ω (FullPath Ω) :=
  ProbabilityTheory.Kernel.sum fun n => G.fullSectorKernel T n

@[simp]
theorem pathKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    G.pathKernel T x = G.pathLawFrom T x := by
  rw [pathKernel, ProbabilityTheory.Kernel.sum_apply]
  simp only [fullSectorKernel_apply]
  rfl

noncomputable instance instIsMarkovKernelPathKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    IsMarkovKernel (G.pathKernel T) := by
  constructor
  intro x
  rw [pathKernel_apply]
  infer_instance

/-- A fixed suffix sector started at the terminal state of a complete prefix. -/
noncomputable def continuationFullSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (m : ℕ) :
    ProbabilityTheory.Kernel (FullPath Ω) (FullPath Ω) :=
  (G.fullSectorKernel T m).comap FullPath.terminalState
    FullPath.measurable_terminalState

@[simp]
theorem continuationFullSectorKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (m : ℕ)
    (γ : FullPath Ω) :
    G.continuationFullSectorKernel T m γ =
      FullPath.liftMeasure m
        (G.sectorLawFrom T (FullPath.terminalState γ) m) := by
  rcases γ with ⟨n, γ⟩
  rw [continuationFullSectorKernel,
    ProbabilityTheory.Kernel.comap_apply, fullSectorKernel_apply]

noncomputable instance instIsFiniteKernelContinuationFullSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (m : ℕ) :
    IsFiniteKernel (G.continuationFullSectorKernel T m) := by
  unfold continuationFullSectorKernel
  infer_instance

/-- The continuation path kernel, conditioned on the prefix terminal state. -/
noncomputable def continuationPathKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    ProbabilityTheory.Kernel (FullPath Ω) (FullPath Ω) :=
  ProbabilityTheory.Kernel.sum fun m => G.continuationFullSectorKernel T m

@[simp]
theorem continuationPathKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (γ : FullPath Ω) :
    G.continuationPathKernel T γ =
      G.pathLawFrom T (FullPath.terminalState γ) := by
  rw [continuationPathKernel, ProbabilityTheory.Kernel.sum_apply]
  simp only [continuationFullSectorKernel_apply]
  rfl

noncomputable instance instIsMarkovKernelContinuationPathKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) :
    IsMarkovKernel (G.continuationPathKernel T) := by
  constructor
  intro γ
  rw [continuationPathKernel_apply]
  infer_instance

/-- Concatenating two injected fixed sectors agrees with injecting their
fixed-sector concatenation. -/
theorem map_concat_compProd_liftMeasure
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) (n m : ℕ) :
    ((FullPath.liftMeasure n (G.sectorLawFrom S x n)) ⊗ₘ
        G.continuationFullSectorKernel T m).map
          (fun p => FullPath.concat p.1 p.2) =
      FullPath.liftMeasure (n + m)
        ((G.sectorLawFrom S x n ⊗ₘ
          G.continuationSectorKernel T n m).map
            (fun p => JumpPath.concat p.1 p.2)) := by
  letI : IsFiniteMeasure (G.sectorLawFrom S x n) := by
    change IsFiniteMeasure (G.sectorKernel S n x)
    exact IsFiniteKernel.isFiniteMeasure x
  letI : IsFiniteMeasure
      (FullPath.liftMeasure n (G.sectorLawFrom S x n)) := by
    unfold FullPath.liftMeasure
    infer_instance
  let f := fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2
  let g := fun p : JumpPath Ω n × JumpPath Ω m =>
    JumpPath.concat p.1 p.2
  have hf : Measurable f := FullPath.measurable_concat_prod_of_point x
  have hg : Measurable g := JumpPath.measurable_concat_prod
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [Measure.compProd_apply (hf hs)]
  unfold FullPath.liftMeasure
  rw [lintegral_map
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (hf hs))
    (FullPath.measurable_mk n)]
  rw [Measure.map_apply (FullPath.measurable_mk (n + m)) hs]
  rw [Measure.map_apply hg ((FullPath.measurable_mk (n + m)) hs)]
  rw [Measure.compProd_apply
    (hg ((FullPath.measurable_mk (n + m)) hs))]
  apply lintegral_congr
  intro γ
  rw [continuationFullSectorKernel_apply]
  unfold FullPath.liftMeasure
  rw [Measure.map_apply (FullPath.measurable_mk m)
    (measurable_prodMk_left (hf hs))]
  rfl

theorem liftMeasure_sum {ι : Type*}
    (n : ℕ) (μ : ι → Measure (JumpPath Ω n)) :
    FullPath.liftMeasure n (Measure.sum μ) =
      Measure.sum fun i => FullPath.liftMeasure n (μ i) := by
  unfold FullPath.liftMeasure
  exact Measure.map_sum (FullPath.measurable_mk n).aemeasurable

set_option maxHeartbeats 800000 in
/-- The long-horizon path law, partitioned by its prefix and suffix jump
counts. -/
theorem pathLawFrom_add_lhs_normalForm
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) :
    G.pathLawFrom (S + T) x =
      Measure.sum fun p : ℕ × ℕ =>
        FullPath.liftMeasure (p.1 + p.2)
          ((G.sectorLawFrom (S + T) x (p.1 + p.2)).restrict
            (JumpPath.jumpsBeforeSet S (p.1 + p.2) p.1)) := by
  let M := fun z : Σ k : ℕ, Fin (k + 1) =>
    FullPath.liftMeasure z.1
      ((G.sectorLawFrom (S + T) x z.1).restrict
        (JumpPath.jumpsBeforeSet S z.1 z.2.val))
  let N := fun p : ℕ × ℕ =>
    FullPath.liftMeasure (p.1 + p.2)
      ((G.sectorLawFrom (S + T) x (p.1 + p.2)).restrict
        (JumpPath.jumpsBeforeSet S (p.1 + p.2) p.1))
  have hsum :
      (Measure.sum fun k => Measure.sum fun r : Fin (k + 1) =>
        FullPath.liftMeasure k
          ((G.sectorLawFrom (S + T) x k).restrict
            (JumpPath.jumpsBeforeSet S k r.val))) = Measure.sum M := by
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
    simp_rw [Measure.sum_apply _ hs]
    exact (ENNReal.tsum_sigma fun k (r : Fin (k + 1)) =>
      (FullPath.liftMeasure k
        ((G.sectorLawFrom (S + T) x k).restrict
          (JumpPath.jumpsBeforeSet S k r.val))) s).symm
  calc
    G.pathLawFrom (S + T) x =
        Measure.sum fun k =>
          FullPath.liftMeasure k (G.sectorLawFrom (S + T) x k) := rfl
    _ = Measure.sum fun k => FullPath.liftMeasure k
          (Measure.sum fun r : Fin (k + 1) =>
            (G.sectorLawFrom (S + T) x k).restrict
              (JumpPath.jumpsBeforeSet S k r.val)) := by
      congr 1
      funext k
      rw [← G.sectorLawFrom_eq_sum_restrict_jumpsBefore (S + T) S x k]
    _ = Measure.sum fun k => Measure.sum fun r : Fin (k + 1) =>
          FullPath.liftMeasure k
            ((G.sectorLawFrom (S + T) x k).restrict
              (JumpPath.jumpsBeforeSet S k r.val)) := by
      congr 1
      funext k
      exact liftMeasure_sum k _
    _ = Measure.sum M := hsum
    _ = Measure.sum N := by
      ext s hs
      rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
      rw [← (cutSectorEquiv).tsum_eq (fun p => N p s)]
      apply tsum_congr
      intro z
      rcases z with ⟨k, r⟩
      dsimp [M, N]
      rw [cutSectorEquiv_apply_add, cutSectorEquiv_apply_fst]
    _ = _ := rfl

/-- Stage 6 after injecting both sides into the complete path space. -/
theorem liftMeasure_sectorLawFrom_restrict_jumpsBeforeSet
    (G : FiniteJumpGenerator Ω) (S T : NNReal)
    (hS : 0 < S) (hT : 0 < T) (x : Ω) (n m : ℕ) :
    FullPath.liftMeasure (n + m)
        ((G.sectorLawFrom (S + T) x (n + m)).restrict
          (JumpPath.jumpsBeforeSet S (n + m) n)) =
      ((FullPath.liftMeasure n (G.sectorLawFrom S x n)) ⊗ₘ
        G.continuationFullSectorKernel T m).map
          (fun p => FullPath.concat p.1 p.2) := by
  rw [G.map_concat_compProd_liftMeasure S T x n m]
  rw [G.sectorLawFrom_restrict_jumpsBeforeSet S T hS hT x n m]

/-- The concatenated two-step law, expanded into prefix and suffix sectors. -/
theorem pathLawFrom_add_rhs_normalForm
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) :
    (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel T).map
        (fun p => FullPath.concat p.1 p.2) =
      Measure.sum fun p : ℕ × ℕ =>
        ((FullPath.liftMeasure p.1 (G.sectorLawFrom S x p.1)) ⊗ₘ
          G.continuationFullSectorKernel T p.2).map
            (fun q => FullPath.concat q.1 q.2) := by
  let f := fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2
  have hf : Measurable f := FullPath.measurable_concat_prod_of_point x
  letI (n : ℕ) : IsFiniteMeasure (G.sectorLawFrom S x n) := by
    change IsFiniteMeasure (G.sectorKernel S n x)
    exact IsFiniteKernel.isFiniteMeasure x
  letI (n : ℕ) : IsFiniteMeasure
      (FullPath.liftMeasure n (G.sectorLawFrom S x n)) := by
    unfold FullPath.liftMeasure
    infer_instance
  calc
    (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel T).map f =
        ((Measure.sum fun n => FullPath.liftMeasure n
          (G.sectorLawFrom S x n)) ⊗ₘ
            (ProbabilityTheory.Kernel.sum fun m =>
              G.continuationFullSectorKernel T m)).map f := rfl
    _ = (Measure.sum fun n =>
          (FullPath.liftMeasure n (G.sectorLawFrom S x n) ⊗ₘ
            (ProbabilityTheory.Kernel.sum fun m =>
              G.continuationFullSectorKernel T m))).map f := by
      rw [Measure.compProd_sum_left]
    _ = (Measure.sum fun n => Measure.sum fun m =>
          FullPath.liftMeasure n (G.sectorLawFrom S x n) ⊗ₘ
            G.continuationFullSectorKernel T m).map f := by
      have hinner : (fun n =>
          FullPath.liftMeasure n (G.sectorLawFrom S x n) ⊗ₘ
            (ProbabilityTheory.Kernel.sum fun m =>
              G.continuationFullSectorKernel T m)) =
          (fun n => Measure.sum fun m =>
            FullPath.liftMeasure n (G.sectorLawFrom S x n) ⊗ₘ
              G.continuationFullSectorKernel T m) := by
        funext n
        exact Measure.compProd_sum_right
      rw [hinner]
    _ = Measure.sum fun n => Measure.sum fun m =>
          (FullPath.liftMeasure n (G.sectorLawFrom S x n) ⊗ₘ
            G.continuationFullSectorKernel T m).map f := by
      rw [Measure.map_sum hf.aemeasurable]
      congr 1
      funext n
      rw [Measure.map_sum hf.aemeasurable]
    _ = Measure.sum fun p : ℕ × ℕ =>
          (FullPath.liftMeasure p.1 (G.sectorLawFrom S x p.1) ⊗ₘ
            G.continuationFullSectorKernel T p.2).map f := Measure.sum_sum _
    _ = _ := rfl

/-- **Path-level Chapman--Kolmogorov for positive horizons.**  First sample a
prefix, then a suffix started at its terminal state, and concatenate them. -/
theorem pathLawFrom_add
    (G : FiniteJumpGenerator Ω) (S T : NNReal)
    (hS : 0 < S) (hT : 0 < T) (x : Ω) :
    G.pathLawFrom (S + T) x =
      (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel T).map
        (fun p => FullPath.concat p.1 p.2) := by
  rw [G.pathLawFrom_add_lhs_normalForm S T x]
  rw [G.pathLawFrom_add_rhs_normalForm S T x]
  congr 1
  funext p
  exact G.liftMeasure_sectorLawFrom_restrict_jumpsBeforeSet
    S T hS hT x p.1 p.2

/-- The two-step complete-path kernel obtained by conditional concatenation. -/
noncomputable def concatenatedPathKernel
    (G : FiniteJumpGenerator Ω) (S T : NNReal) :
    ProbabilityTheory.Kernel Ω (FullPath Ω) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x =>
    (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel T).map
      (fun p => FullPath.concat p.1 p.2)

@[simp]
theorem concatenatedPathKernel_apply
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) :
    G.concatenatedPathKernel S T x =
      (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel T).map
        (fun p => FullPath.concat p.1 p.2) := rfl

/-- Kernel form of positive-horizon path-law concatenation. -/
theorem pathKernel_add
    (G : FiniteJumpGenerator Ω) (S T : NNReal)
    (hS : 0 < S) (hT : 0 < T) :
    G.pathKernel (S + T) = G.concatenatedPathKernel S T := by
  apply ProbabilityTheory.Kernel.ext
  intro x
  rw [pathKernel_apply, concatenatedPathKernel_apply]
  exact G.pathLawFrom_add S T hS hT x

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
