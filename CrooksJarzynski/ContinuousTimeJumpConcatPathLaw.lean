/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatLaw
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Probability.HasLaw

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

namespace JumpPath

variable {Ω : Type u}

/-- Transport a fixed-sector path along an equality of jump counts. -/
def reindex {n m : ℕ} (h : n = m) (γ : JumpPath Ω n) : JumpPath Ω m :=
  (γ.1 ∘ Fin.cast (by omega), γ.2 ∘ Fin.cast (by omega))

@[simp]
theorem reindex_rfl {n : ℕ} (γ : JumpPath Ω n) : reindex rfl γ = γ := by
  rfl

@[simp]
theorem jumpTimes_reindex {n m : ℕ} (h : n = m) (γ : JumpPath Ω n)
    (i : Fin (m + 1)) :
    jumpTimes (reindex h γ) i = jumpTimes γ (Fin.cast (by omega) i) := by
  subst h
  rfl

@[simp]
theorem totalHoldingTime_reindex {n m : ℕ} (h : n = m)
    (γ : JumpPath Ω n) :
    (reindex h γ).totalHoldingTime = γ.totalHoldingTime := by
  subst h
  rfl

theorem measurable_reindex [MeasurableSpace Ω] {n m : ℕ} (h : n = m) :
    Measurable (reindex (Ω := Ω) h) := by
  subst m
  convert (measurable_id : Measurable (id : JumpPath Ω n → JumpPath Ω n)) using 1
  funext γ
  exact reindex_rfl γ

/-- The unique chart-shaped path with no jumps, resting at `x`. -/
def zeroJumpPath (x : Ω) : JumpPath Ω 0 :=
  (fun _ => x, fun _ => 0)

/-- A jump-free prefix is a left identity when its state matches the suffix. -/
theorem concat_zeroJumpPath {m : ℕ} (x : Ω) (γ : JumpPath Ω m)
    (hmatch : x = γ.1 0) :
    concat (zeroJumpPath x) γ =
      reindex (Nat.zero_add m).symm γ := by
  subst x
  unfold concat zeroJumpPath reindex
  apply Prod.ext
  · funext i
    change Fin.append (fun _ : Fin 1 => γ.1 0) (γ.1 ∘ Fin.succ)
        (Fin.cast (by omega) i) = γ.1 (Fin.cast (by omega) i)
    rw [Fin.append_left_eq_cons]
    simp only [Function.comp_apply]
    rw [← Fin.cons_self_tail γ.1]
    congr 1
  · funext i
    change Fin.append
        (fun j : Fin 1 => if j = Fin.last 0 then 0 + γ.2 0 else 0)
        (γ.2 ∘ Fin.succ) (Fin.cast (by omega) i) =
      γ.2 (Fin.cast (by omega) i)
    rw [Fin.append_left_eq_cons]
    simp only [Function.comp_apply]
    have hhead : (if (0 : Fin 1) = Fin.last 0 then
        0 + γ.2 0 else 0) = γ.2 0 := by simp
    rw [hhead, ← Fin.cons_self_tail γ.2]
    congr 1

/-- A jump-free suffix is a right identity for fixed-sector concatenation. -/
theorem concat_zeroJumpPath_right {n : ℕ} (γ : JumpPath Ω n) (x : Ω) :
    concat γ (zeroJumpPath x) =
      reindex (Nat.add_zero n).symm γ := by
  unfold concat zeroJumpPath reindex
  apply Prod.ext
  · funext i
    change Fin.append γ.1 ((fun _ : Fin 1 => x) ∘ Fin.succ)
        (Fin.cast (by omega) i) = γ.1 (Fin.cast (by omega) i)
    rw [Fin.append_right_nil _ _ rfl]
    simp only [Function.comp_apply]
    apply congrArg γ.1
    apply Fin.ext
    rfl
  · funext i
    change Fin.append
        (fun j : Fin (n + 1) =>
          if j = Fin.last n then γ.2 j + 0 else γ.2 j)
        ((fun _ : Fin 1 => 0) ∘ Fin.succ) (Fin.cast (by omega) i) =
      γ.2 (Fin.cast (by omega) i)
    rw [Fin.append_right_nil _ _ rfl]
    simp only [Function.comp_apply]
    split <;> simp

end JumpPath

namespace FullPath

variable {Ω : Type u}

/-- Reindexing a fixed-sector representative does not change its complete
path. -/
theorem mk_reindex {n m : ℕ} (h : n = m) (γ : JumpPath Ω n) :
    (⟨n, γ⟩ : FullPath Ω) = ⟨m, JumpPath.reindex h γ⟩ := by
  subst h
  rfl

/-- A seam-matched resting prefix is a left identity on complete paths. -/
theorem concat_rest_left (x : Ω) (γ : FullPath Ω)
    (hmatch : initialState γ = x) :
    concat (rest x) γ = γ := by
  rcases γ with ⟨m, γ⟩
  change (⟨0 + m, JumpPath.concat (JumpPath.zeroJumpPath x) γ⟩ : FullPath Ω) =
    ⟨m, γ⟩
  rw [JumpPath.concat_zeroJumpPath x γ hmatch.symm]
  exact (mk_reindex (Nat.zero_add m).symm γ).symm

/-- A resting suffix is a right identity on complete paths. -/
theorem concat_rest_right (γ : FullPath Ω) (x : Ω) :
    concat γ (rest x) = γ := by
  rcases γ with ⟨n, γ⟩
  change (⟨n + 0, JumpPath.concat γ (JumpPath.zeroJumpPath x)⟩ : FullPath Ω) =
    ⟨n, γ⟩
  rw [JumpPath.concat_zeroJumpPath_right γ x]
  exact (mk_reindex (Nat.add_zero n).symm γ).symm

/-- At horizon zero, validity and exact total holding time determine the
unique resting complete path. -/
theorem eq_rest_of_isValid_zero (x : Ω) (γ : FullPath Ω)
    (hvalid : IsValid 0 γ) (htotal : totalHoldingTime γ = 0)
    (hinitial : initialState γ = x) :
    γ = rest x := by
  rcases γ with ⟨n, γ⟩
  cases n with
  | zero =>
      have hγ : γ = JumpPath.zeroJumpPath x := by
        apply Prod.ext
        · funext i
          rw [Fin.eq_zero i]
          exact hinitial
        · funext i
          rw [Fin.eq_zero i]
          change γ.2 0 = 0
          simpa [FullPath.totalHoldingTime, JumpPath.totalHoldingTime] using htotal
      exact congrArg (Sigma.mk 0) hγ
  | succ n =>
      have hpos := JumpPath.jumpTimes_last_pos_of_pos γ hvalid.1
      have hle := hvalid.2
      norm_num at hle
      linarith

end FullPath

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

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] in
theorem liftMeasure_sum {ι : Type*}
    (n : ℕ) (μ : ι → Measure (JumpPath Ω n)) :
    FullPath.liftMeasure n (Measure.sum μ) =
      Measure.sum fun i => FullPath.liftMeasure n (μ i) := by
  unfold FullPath.liftMeasure
  exact Measure.map_sum (FullPath.measurable_mk n).aemeasurable

set_option maxHeartbeats 800000 in
omit [MeasurableSingletonClass Ω] in
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

/-- The zero-horizon path law is concentrated on the unique resting path at
its prescribed initial state. -/
theorem pathLawFrom_zero
    (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.pathLawFrom 0 x = Measure.dirac (FullPath.rest x) := by
  have hae : (id : FullPath Ω → FullPath Ω) =ᵐ[G.pathLawFrom 0 x]
      fun _ => FullPath.rest x := by
    filter_upwards [G.pathLawFrom_ae_isValid 0 x,
      G.pathLawFrom_ae_totalHoldingTime 0 x,
      G.pathLawFrom_ae_initialState 0 x] with γ hvalid htotal hinitial
    exact FullPath.eq_rest_of_isValid_zero x γ hvalid htotal hinitial
  have hlaw : HasLaw (id : FullPath Ω → FullPath Ω)
      (Measure.dirac (FullPath.rest x)) (G.pathLawFrom 0 x) :=
    hasLaw_dirac_of_ae_eq hae
  simpa using hlaw.map_eq

/-- **Path-level Chapman--Kolmogorov for positive horizons.**  First sample a
prefix, then a suffix started at its terminal state, and concatenate them. -/
theorem pathLawFrom_add_of_pos
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

/-- Concatenation with the zero-horizon prefix law. -/
theorem pathLawFrom_add_zero_left
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    G.pathLawFrom T x =
      (G.pathLawFrom 0 x ⊗ₘ G.continuationPathKernel T).map
        (fun p => FullPath.concat p.1 p.2) := by
  rw [G.pathLawFrom_zero x]
  let f := fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2
  have hf : Measurable f := FullPath.measurable_concat_prod_of_point x
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [Measure.compProd_apply (hf hs)]
  rw [lintegral_dirac' _
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (hf hs))]
  rw [continuationPathKernel_apply, FullPath.terminalState_rest]
  apply measure_congr
  filter_upwards [G.pathLawFrom_ae_initialState T x] with γ hγ
  apply propext
  change (γ ∈ s) ↔ FullPath.concat (FullPath.rest x) γ ∈ s
  rw [FullPath.concat_rest_left x γ hγ]

/-- Concatenation with the zero-horizon continuation law. -/
theorem pathLawFrom_add_zero_right
    (G : FiniteJumpGenerator Ω) (S : NNReal) (x : Ω) :
    G.pathLawFrom S x =
      (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel 0).map
        (fun p => FullPath.concat p.1 p.2) := by
  let f := fun p : FullPath Ω × FullPath Ω => FullPath.concat p.1 p.2
  have hf : Measurable f := FullPath.measurable_concat_prod_of_point x
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [Measure.compProd_apply (hf hs)]
  rw [← lintegral_indicator_one hs]
  apply lintegral_congr
  intro γ
  rw [continuationPathKernel_apply, G.pathLawFrom_zero]
  rw [Measure.dirac_apply' _ (measurable_prodMk_left (hf hs))]
  by_cases hγ : γ ∈ s
  · have hmem : FullPath.rest (FullPath.terminalState γ) ∈
        Prod.mk γ ⁻¹' f ⁻¹' s := by
      change FullPath.concat γ (FullPath.rest (FullPath.terminalState γ)) ∈ s
      rwa [FullPath.concat_rest_right]
    rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]
    rfl
  · have hmem : FullPath.rest (FullPath.terminalState γ) ∉
        Prod.mk γ ⁻¹' f ⁻¹' s := by
      intro hmem
      apply hγ
      change FullPath.concat γ (FullPath.rest (FullPath.terminalState γ)) ∈ s at hmem
      rwa [FullPath.concat_rest_right] at hmem
    rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hmem]

/-- **Path-level Chapman--Kolmogorov at arbitrary nonnegative horizons.** -/
theorem pathLawFrom_add
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) :
    G.pathLawFrom (S + T) x =
      (G.pathLawFrom S x ⊗ₘ G.continuationPathKernel T).map
        (fun p => FullPath.concat p.1 p.2) := by
  rcases eq_zero_or_pos S with rfl | hS
  · simpa using G.pathLawFrom_add_zero_left T x
  rcases eq_zero_or_pos T with rfl | hT
  · simpa using G.pathLawFrom_add_zero_right S x
  exact G.pathLawFrom_add_of_pos S T hS hT x

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

/-- Kernel form of path-law concatenation at arbitrary nonnegative horizons. -/
theorem pathKernel_add
    (G : FiniteJumpGenerator Ω) (S T : NNReal) :
    G.pathKernel (S + T) = G.concatenatedPathKernel S T := by
  apply ProbabilityTheory.Kernel.ext
  intro x
  rw [pathKernel_apply, concatenatedPathKernel_apply]
  exact G.pathLawFrom_add S T x

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
