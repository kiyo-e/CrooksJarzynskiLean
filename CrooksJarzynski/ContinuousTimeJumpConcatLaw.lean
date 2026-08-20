/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatDensity
import Mathlib.MeasureTheory.Group.Prod

/-!
# Concatenation law for finite-generator path measures

This module proves the path-level Chapman--Kolmogorov law for the normalized
fixed-initial law of a finite jump generator.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u}

/-- A path has a jump at `S` when one of its noninitial recorded states starts
at exactly that physical time. -/
def HasJumpAt {n : ℕ} (S : NNReal) (γ : JumpPath Ω n) : Prop :=
  ∃ i : Fin n, jumpTimes γ i.succ = (S : ℝ)

theorem measurableSet_hasJumpAt [MeasurableSpace Ω] {n : ℕ} (S : NNReal) :
    MeasurableSet {γ : JumpPath Ω n | HasJumpAt S γ} := by
  simp only [HasJumpAt, Set.setOf_exists]
  exact MeasurableSet.iUnion fun i =>
    ((measurable_jumpTimes i.succ).eq_const (S : ℝ)).setOf

end JumpPath

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The total holding time is a measurable complete-path observable. -/
@[fun_prop]
theorem measurable_totalHoldingTime :
    Measurable (totalHoldingTime : FullPath Ω → NNReal) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact JumpPath.measurable_totalHoldingTime hs

/-- A complete path has a jump at `S` when its fixed-count representative does. -/
def HasJumpAt (S : NNReal) : FullPath Ω → Prop
  | ⟨_, γ⟩ => JumpPath.HasJumpAt S γ

theorem measurableSet_hasJumpAt (S : NNReal) :
    MeasurableSet {γ : FullPath Ω | HasJumpAt S γ} := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact JumpPath.measurableSet_hasJumpAt S

end FullPath

namespace Simplex

/-- A positive multiple of a nonempty partial sum of free simplex coordinates
has no atoms.  The proof separates the last coordinate in the partial sum;
every section in that coordinate is at most a singleton. -/
theorem volume_partialSum_eq_zero {n : ℕ} (H : NNReal) (hH : 0 < H)
    (S : NNReal) (i : Fin (n + 1)) :
    (volume : Measure (Fin (n + 1) → I))
        {u | ∑ j ∈ Finset.Iic i, (H : ℝ) * (u j : ℝ) = (S : ℝ)} = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) i
  let s : Set (I × (Fin n → I)) :=
    {p | ∑ j ∈ Finset.Iic i,
      (H : ℝ) * ((e.symm p) j : ℝ) = (S : ℝ)}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact ((by fun_prop : Measurable fun p : I × (Fin n → I) =>
      ∑ j ∈ Finset.Iic i, (H : ℝ) * ((e.symm p) j : ℝ)).eq
        measurable_const).setOf
  have hpre : e ⁻¹' s =
      {u | ∑ j ∈ Finset.Iic i, (H : ℝ) * (u j : ℝ) = (S : ℝ)} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    change (∑ j ∈ Finset.Iic i,
      (H : ℝ) * ((e.symm (e u)) j : ℝ)) = (S : ℝ) ↔ _
    rw [e.symm_apply_apply]
  rw [← hpre,
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => I) i).measure_preimage
      hs.nullMeasurableSet]
  change ((volume : Measure I).prod (volume : Measure (Fin n → I))) s = 0
  rw [Measure.prod_apply_symm hs]
  have hsection : ∀ v : Fin n → I,
      (volume : Measure I) ((fun x => (x, v)) ⁻¹' s) = 0 := by
    intro v
    apply Set.Subsingleton.measure_zero
    intro x hx y hy
    have hxi : (e.symm (x, v)) i = x := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hyi : (e.symm (y, v)) i = y := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    have haway : ∀ j, j ≠ i →
        (e.symm (x, v)) j = (e.symm (y, v)) j := by
      intro j hji
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hrest :
        (∑ j ∈ (Finset.Iic i).erase i,
            (H : ℝ) * ((e.symm (x, v)) j : ℝ)) =
          ∑ j ∈ (Finset.Iic i).erase i,
            (H : ℝ) * ((e.symm (y, v)) j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [haway j (Finset.ne_of_mem_erase hj)]
    have hxsum := hx
    have hysum := hy
    change (∑ j ∈ Finset.Iic i,
      (H : ℝ) * ((e.symm (x, v)) j : ℝ)) = (S : ℝ) at hxsum
    change (∑ j ∈ Finset.Iic i,
      (H : ℝ) * ((e.symm (y, v)) j : ℝ)) = (S : ℝ) at hysum
    rw [← Finset.sum_erase_add (Finset.Iic i)
      (fun j => (H : ℝ) * ((e.symm (x, v)) j : ℝ))
      (Finset.mem_Iic.mpr le_rfl)] at hxsum
    rw [← Finset.sum_erase_add (Finset.Iic i)
      (fun j => (H : ℝ) * ((e.symm (y, v)) j : ℝ))
      (Finset.mem_Iic.mpr le_rfl)] at hysum
    rw [hxi] at hxsum
    rw [hyi, ← hrest] at hysum
    apply Subtype.ext
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    nlinarith
  simp_rw [hsection]
  exact lintegral_zero

theorem freeSimplexProbability_partialSum_eq_zero {n : ℕ}
    (H : NNReal) (hH : 0 < H) (S : NNReal) (i : Fin (n + 1)) :
    freeSimplexProbability (n + 1)
        {u | ∑ j ∈ Finset.Iic i, (H : ℝ) * (u j : ℝ) = (S : ℝ)} = 0 := by
  apply ProbabilityTheory.cond_absolutelyContinuous
  exact volume_partialSum_eq_zero H hH S i

theorem freeSimplexProbability_ae_noJumpAt {n : ℕ}
    (H : NNReal) (hH : 0 < H) (S : NNReal) :
    ∀ᵐ u ∂freeSimplexProbability (n + 1), ∀ i : Fin (n + 1),
      (∑ j ∈ Finset.Iic i, (H : ℝ) * (u j : ℝ)) ≠ (S : ℝ) := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simpa only [not_ne_iff] using
    freeSimplexProbability_partialSum_eq_zero H hH S i

/-- Under a positive-horizon simplex chart, no jump occurs at a prescribed
deterministic time almost surely. -/
theorem rawPathProbability_ae_noJumpAt
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (H : NNReal) (hH : 0 < H) (S : NNReal)
    (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂rawPathProbability H stateLaw,
      ¬ JumpPath.HasJumpAt S γ := by
  cases n with
  | zero =>
      exact ae_of_all _ fun γ h => by
        obtain ⟨i, _⟩ := h
        exact Fin.elim0 i
  | succ n =>
      have hset : MeasurableSet
          {γ : JumpPath Ω (n + 1) | ¬ JumpPath.HasJumpAt S γ} :=
        (JumpPath.measurableSet_hasJumpAt S).compl
      unfold rawPathProbability
      rw [ae_map_iff (measurable_assemblePath H).aemeasurable hset]
      apply (Measure.ae_prod_iff_ae_ae ((measurable_assemblePath H) hset)).2
      refine ae_of_all stateLaw fun states => ?_
      filter_upwards [freeSimplexProbability_ae_noJumpAt H hH S] with u hu
      intro h
      obtain ⟨i, hi⟩ := h
      have hi' := hu i
      apply hi'
      have hidx : Finset.Iio i.succ =
          (Finset.Iic i).map Fin.castSuccEmb := by
        rw [Fin.map_castSuccEmb_Iic]
        ext j
        simp only [Finset.mem_Iio, Finset.mem_Iic]
        change j.val < i.val + 1 ↔ j.val ≤ i.val
        omega
      rw [JumpPath.jumpTimes, hidx, Finset.sum_map] at hi
      simpa only [assemblePath, holdingTimesOfFree, Fin.snoc_castSucc,
        Fin.castSuccEmb_apply, NNReal.coe_mul, coe_unitNNReal] using hi

/-! ### Cumulative jump-time coordinates -/

/-- The cumulative-time (`τ`) chart of a vector of physical holding
increments. -/
def cumulativeTimes : (n : ℕ) → (Fin n → ℝ) → Fin n → ℝ
  | 0 => id
  | n + 1 => fun u => Fin.cons (u 0)
      (fun i => u 0 + cumulativeTimes n (Fin.tail u) i)

@[fun_prop]
theorem measurable_cumulativeTimes : ∀ n, Measurable (cumulativeTimes n)
  | 0 => measurable_id
  | n + 1 => by
      unfold cumulativeTimes
      rw [measurable_pi_iff]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_pi_apply 0
      · exact (measurable_pi_apply 0).add
          ((measurable_pi_apply j).comp
            ((measurable_cumulativeTimes n).comp (by fun_prop)))

theorem cumulativeTimes_eq_partialSum : ∀ {n : ℕ}
    (u : Fin n → ℝ) (i : Fin n),
    cumulativeTimes n u i = Fin.partialSum u i.succ
  | 0, _, i => Fin.elim0 i
  | n + 1, u, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · change u 0 = Fin.partialSum u (Fin.succ 0)
        rw [Fin.partialSum_succ]
        simp
      · rw [show cumulativeTimes (n + 1) u (Fin.succ j) =
            u 0 + cumulativeTimes n (Fin.tail u) j from rfl,
          cumulativeTimes_eq_partialSum]
        exact (Fin.partialSum_succ' u j.succ).symm

/-- Passing from holding increments to cumulative times preserves Lebesgue
measure.  The induction uses only product decomposition and the
translation-invariant shear `(x, τ) ↦ (x, x + τ)`. -/
theorem measurePreserving_cumulativeTimes (n : ℕ) :
    MeasurePreserving (cumulativeTimes n) volume volume := by
  induction n with
  | zero =>
      exact MeasurePreserving.id volume
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hsplit : MeasurePreserving e volume
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hrec : MeasurePreserving
          (fun p : ℝ × (Fin n → ℝ) => (p.1, cumulativeTimes n p.2))
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
        convert (MeasurePreserving.id (volume : Measure ℝ)).prod ih using 1
        funext p
        rfl
      have hshear : MeasurePreserving
          (fun p : ℝ × (Fin n → ℝ) => (p.1, fun i => p.1 + p.2 i))
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
        refine MeasurePreserving.skew_product
          (g := fun (x : ℝ) (y : Fin n → ℝ) => fun i => x + y i)
          (MeasurePreserving.id (volume : Measure ℝ)) (by fun_prop) ?_
        refine ae_of_all _ fun x => ?_
        exact (measurePreserving_add_left
          (volume : Measure (Fin n → ℝ)) (fun _ => x)).map_eq
      have hjoin : MeasurePreserving e.symm
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) volume :=
        hsplit.symm e
      have hcomp := hjoin.comp (hshear.comp (hrec.comp hsplit))
      refine hcomp.congr (measurable_cumulativeTimes (n + 1)) ?_
      refine ae_of_all _ fun u => ?_
      apply e.injective
      apply Prod.ext
      · rfl
      · funext i
        rfl

/-- Split a global cumulative-time vector into its first `n` and last `m`
coordinates. -/
noncomputable def splitTimesEquiv (n m : ℕ) : (Fin (n + m) → ℝ) ≃ᵐ
    (Fin n → ℝ) × (Fin m → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin m => ℝ)
    finSumFinEquiv.symm).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ))

theorem measurePreserving_splitTimesEquiv (n m : ℕ) :
    MeasurePreserving (splitTimesEquiv n m) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft
    (fun _ : Fin n ⊕ Fin m => ℝ) (@finSumFinEquiv n m).symm
  have h2 := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin m => ℝ)
  exact h2.comp h1

theorem splitTimesEquiv_apply_left (n m : ℕ) (τ : Fin (n + m) → ℝ)
    (i : Fin n) : (splitTimesEquiv n m τ).1 i = τ (Fin.castAdd m i) := by
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin m => ℝ)
    (@finSumFinEquiv n m).symm τ) (Sum.inl i) = _
  simpa using MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin n ⊕ Fin m => ℝ)
    (@finSumFinEquiv n m).symm τ (Fin.castAdd m i)

theorem splitTimesEquiv_apply_right (n m : ℕ) (τ : Fin (n + m) → ℝ)
    (i : Fin m) : (splitTimesEquiv n m τ).2 i = τ (Fin.natAdd n i) := by
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin m => ℝ)
    (@finSumFinEquiv n m).symm τ) (Sum.inr i) = _
  simpa using MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin n ⊕ Fin m => ℝ)
    (@finSumFinEquiv n m).symm τ (Fin.natAdd n i)

/-- Translate suffix times by the cut level. -/
noncomputable def shiftTimesEquiv (S : ℝ) (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ ((Fin n → ℝ) × (Fin m → ℝ)) :=
  (MeasurableEquiv.refl (Fin n → ℝ)).prodCongr
    (MeasurableEquiv.addLeft (fun _ : Fin m => S))

/-- Join prefix times with suffix times translated by the cut level. -/
noncomputable def joinTimesEquiv (S : ℝ) (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n + m) → ℝ) :=
  (shiftTimesEquiv S n m).trans (splitTimesEquiv n m).symm

theorem measurePreserving_shiftTimesEquiv (S : ℝ) (n m : ℕ) :
    MeasurePreserving (shiftTimesEquiv S n m) volume volume := by
  exact (MeasurePreserving.id (volume : Measure (Fin n → ℝ))).prod
    (measurePreserving_add_left
      (volume : Measure (Fin m → ℝ)) (fun _ => S))

theorem measurePreserving_joinTimesEquiv (S : ℝ) (n m : ℕ) :
    MeasurePreserving (joinTimesEquiv S n m) volume volume := by
  exact ((measurePreserving_splitTimesEquiv n m).symm
    (splitTimesEquiv n m)).comp (measurePreserving_shiftTimesEquiv S n m)

/-- Ordered cumulative jump times in the physical interval `[0, H]`. -/
def orderedSimplexSet (H : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {τ | (∀ i, 0 ≤ τ i ∧ τ i ≤ H) ∧ Monotone τ}

theorem measurableSet_orderedSimplexSet (H : ℝ) (n : ℕ) :
    MeasurableSet (orderedSimplexSet H n) := by
  unfold orderedSimplexSet
  rw [show {τ : Fin n → ℝ | (∀ i, 0 ≤ τ i ∧ τ i ≤ H) ∧ Monotone τ} =
      (⋂ i, {τ | 0 ≤ τ i ∧ τ i ≤ H}) ∩
        ⋂ i, ⋂ j, ⋂ (_h : i ≤ j), {τ | τ i ≤ τ j} by
    ext τ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ =>
        measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)

/-- The global ordered-time sector with `n` prefix times and `m` suffix times. -/
def cutOrderedSimplexSet (S T : ℝ) (n m : ℕ) :
    Set (Fin (n + m) → ℝ) :=
  joinTimesEquiv S n m ''
    (orderedSimplexSet S n ×ˢ orderedSimplexSet T m)

theorem measurableSet_cutOrderedSimplexSet (S T : ℝ) (n m : ℕ) :
    MeasurableSet (cutOrderedSimplexSet S T n m) := by
  exact (joinTimesEquiv S n m).measurableEmbedding.measurableSet_image'
    ((measurableSet_orderedSimplexSet S n).prod
      (measurableSet_orderedSimplexSet T m))

/-- **Simplex splitting in cumulative jump-time coordinates.**  Product
Lebesgue measure on the prefix and suffix ordered simplexes maps to restricted
Lebesgue measure on the global cut sector. -/
theorem map_orderedSimplex_prod_joinTimes (S T : ℝ) (n m : ℕ) :
    (((volume : Measure (Fin n → ℝ)).restrict (orderedSimplexSet S n)).prod
      ((volume : Measure (Fin m → ℝ)).restrict (orderedSimplexSet T m))).map
        (joinTimesEquiv S n m) =
      (volume : Measure (Fin (n + m) → ℝ)).restrict
        (cutOrderedSimplexSet S T n m) := by
  rw [Measure.prod_restrict]
  let A := orderedSimplexSet S n ×ˢ orderedSimplexSet T m
  let B := cutOrderedSimplexSet S T n m
  have hpre : joinTimesEquiv S n m ⁻¹' B = A := by
    apply Set.preimage_image_eq A (joinTimesEquiv S n m).injective
  have h := (measurePreserving_joinTimesEquiv S n m).restrict_preimage
    (measurableSet_cutOrderedSimplexSet S T n m)
  rw [hpre] at h
  exact h.map_eq

end Simplex

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The fixed-initial sector law in its explicit state-sequence/simplex chart.
The initial-state binding is the `fixedInitialWeight x` factor in the pulled
back density. -/
theorem sectorLawFrom_eq_chart
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    G.sectorLawFrom T x n =
      (((G.stateSequenceCountingReference n).prod
          ((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n))).withDensity
        (fun p => JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T p))).map
        (Simplex.assemblePath T) := by
  unfold sectorLawFrom pathMeasure
  rw [G.rawCountingReference_eq T n]
  exact CrooksJarzynski.MeasureProtocol.map_withDensity _ _ _
    (Simplex.measurable_assemblePath T)
    (G.measurable_rateDensity (fixedInitialWeight x) n)

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
/-- The raw counting reference is concentrated on paths that exactly fill the
prescribed horizon. -/
theorem rawCountingReference_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.rawCountingReference T n, γ.totalHoldingTime = T := by
  unfold rawCountingReference
  apply Measure.ae_smul_measure
  simpa [JumpPath.horizonSet] using
    (Simplex.rawPathProbability_ae_horizon T
      (G.stateSequenceCountingReference n))

omit [MeasurableSingletonClass Ω] in
/-- Every fixed-initial sector law exactly fills its prescribed horizon. -/
theorem sectorLawFrom_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    ∀ᵐ γ ∂G.sectorLawFrom T x n, γ.totalHoldingTime = T := by
  have hraw := G.rawCountingReference_ae_totalHoldingTime T n
  unfold sectorLawFrom pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hraw

omit [MeasurableSingletonClass Ω] in
/-- **Exact-horizon support.**  Almost every complete path sampled from the
fixed-initial path law has total holding time equal to its horizon. -/
theorem pathLawFrom_ae_totalHoldingTime
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    (fun γ => FullPath.totalHoldingTime γ) =ᵐ[G.pathLawFrom T x]
      fun _ => T := by
  have hset : MeasurableSet
      {γ : FullPath Ω | FullPath.totalHoldingTime γ = T} :=
    (FullPath.measurable_totalHoldingTime.eq_const T).setOf
  unfold pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable hset]
  exact G.sectorLawFrom_ae_totalHoldingTime T x n

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
theorem rawCountingReference_ae_noJumpAt
    (G : FiniteJumpGenerator Ω) (H S : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.rawCountingReference H n, ¬ JumpPath.HasJumpAt S γ := by
  rcases eq_zero_or_pos H with hH | hH
  · subst H
    cases n with
    | zero =>
        exact ae_of_all _ fun γ h => by
          obtain ⟨i, _⟩ := h
          exact Fin.elim0 i
    | succ n =>
        have href : G.rawCountingReference 0 (n + 1) = 0 := by
          simp [rawCountingReference, simplexSectorMass]
        rw [href]
        simp
  · unfold rawCountingReference
    exact Measure.ae_smul_measure
      (Simplex.rawPathProbability_ae_noJumpAt H hH S
        (G.stateSequenceCountingReference n)) _

omit [MeasurableSingletonClass Ω] in
theorem sectorLawFrom_ae_noJumpAt
    (G : FiniteJumpGenerator Ω) (H : NNReal) (x : Ω) (n : ℕ) (S : NNReal) :
    ∀ᵐ γ ∂G.sectorLawFrom H x n, ¬ JumpPath.HasJumpAt S γ := by
  have hraw := G.rawCountingReference_ae_noJumpAt H S n
  unfold sectorLawFrom pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hraw

omit [MeasurableSingletonClass Ω] in
/-- **A deterministic cut is almost surely not a jump time.** -/
theorem pathLawFrom_ae_noJumpAt
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) :
    ∀ᵐ γ ∂G.pathLawFrom (S + T) x, ¬ FullPath.HasJumpAt S γ := by
  have hset : MeasurableSet
      {γ : FullPath Ω | ¬ FullPath.HasJumpAt S γ} :=
    (FullPath.measurableSet_hasJumpAt S).compl
  unfold pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable hset]
  exact G.sectorLawFrom_ae_noJumpAt (S + T) x n S

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
