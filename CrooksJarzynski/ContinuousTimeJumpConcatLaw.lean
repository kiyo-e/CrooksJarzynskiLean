/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatDensity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Concatenation law for finite-generator path measures

This module proves the path-level Chapman--Kolmogorov law for the normalized
fixed-initial law of a finite jump generator.
-/

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u}

/-- Fixed-sector concatenation is measurable. -/
@[fun_prop]
theorem measurable_concat_prod [MeasurableSpace Ω] {n m : ℕ} :
    Measurable (fun p : JumpPath Ω n × JumpPath Ω m =>
      concat p.1 p.2) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    change Measurable (fun p : JumpPath Ω n × JumpPath Ω m =>
      (concat p.1 p.2).1 i)
    by_cases h : i.val < n + 1
    · let i0 : Fin (n + 1) := ⟨i.val, h⟩
      have hidx : i = Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.castAdd m i0) := by
        apply Fin.ext
        simp [i0]
      have hfun : (fun p : JumpPath Ω n × JumpPath Ω m =>
          (concat p.1 p.2).1 i) = fun p => p.1.1 i0 := by
        funext p
        rw [hidx, concat_fst_castAdd]
      rw [hfun]
      fun_prop


    · have hlt : i.val - (n + 1) < m := by omega
      let j0 : Fin m := ⟨i.val - (n + 1), hlt⟩
      have hidx : i = Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.natAdd (n + 1) j0) := by
        apply Fin.ext
        simp [j0]
        omega
      have hfun : (fun p : JumpPath Ω n × JumpPath Ω m =>
          (concat p.1 p.2).1 i) = fun p => p.2.1 j0.succ := by
        funext p
        rw [hidx, concat_fst_natAdd]
      rw [hfun]
      fun_prop
  · rw [measurable_pi_iff]
    intro i
    change Measurable (fun p : JumpPath Ω n × JumpPath Ω m =>
      (concat p.1 p.2).2 i)
    by_cases h : i.val < n + 1
    · let i0 : Fin (n + 1) := ⟨i.val, h⟩
      have hidx : i = Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.castAdd m i0) := by
        apply Fin.ext
        simp [i0]
      by_cases hlast : i0 = Fin.last n
      · have hfun : (fun p : JumpPath Ω n × JumpPath Ω m =>
            (concat p.1 p.2).2 i) = fun p => p.1.2 i0 + p.2.2 0 := by
          funext p
          rw [hidx, concat_snd_castAdd, if_pos hlast]
        rw [hfun]
        fun_prop
      · have hfun : (fun p : JumpPath Ω n × JumpPath Ω m =>
            (concat p.1 p.2).2 i) = fun p => p.1.2 i0 := by
          funext p
          rw [hidx, concat_snd_castAdd, if_neg hlast]
        rw [hfun]
        fun_prop
    · have hlt : i.val - (n + 1) < m := by omega
      let j0 : Fin m := ⟨i.val - (n + 1), hlt⟩
      have hidx : i = Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.natAdd (n + 1) j0) := by
        apply Fin.ext
        simp [j0]
        omega
      have hfun : (fun p : JumpPath Ω n × JumpPath Ω m =>
          (concat p.1 p.2).2 i) = fun p => p.2.2 j0.succ := by
        funext p
        rw [hidx, concat_snd_natAdd]
      rw [hfun]
      fun_prop

/-- Rate densities built from finite initial weights and finite jump rates are
finite everywhere. -/
theorem rateDensity_ne_top {n : ℕ} (γ : JumpPath Ω n) (w : Ω → ℝ≥0∞)
    (hw : ∀ x, w x ≠ ∞)
    (escapeRate : Fin (n + 1) → Ω → NNReal)
    (jumpRate : Fin n → Ω → Ω → NNReal) :
    rateDensity w escapeRate jumpRate γ ≠ ∞ := by
  unfold rateDensity density
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact hw _
    · apply ENNReal.prod_ne_top
      intro i _
      apply ENNReal.mul_ne_top
      · unfold holdingWeightOfEscapeRate
        exact ENNReal.ofReal_ne_top
      · unfold jumpWeightOfRate
        exact ENNReal.coe_ne_top
  · unfold holdingWeightOfEscapeRate
    exact ENNReal.ofReal_ne_top

/-- A fixed-sector path recorded by its states, cumulative jump times, and
total duration.  The duration coordinate retains the final residual holding
time, which is not visible in the jump times alone. -/
def cumulativeChart {n : ℕ} (γ : JumpPath Ω n) :
    (Fin (n + 1) → Ω) × ((Fin n → ℝ) × NNReal) :=
  (γ.1, (fun i => jumpTimes γ i.succ, γ.totalHoldingTime))

@[fun_prop]
theorem measurable_cumulativeChart [MeasurableSpace Ω] {n : ℕ} :
    Measurable (cumulativeChart : JumpPath Ω n →
      (Fin (n + 1) → Ω) × ((Fin n → ℝ) × NNReal)) := by
  apply Measurable.prodMk measurable_fst
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    exact measurable_jumpTimes i.succ
  · exact measurable_totalHoldingTime

/-- Cumulative jump times together with the total duration recover every
holding increment, so the cumulative chart loses no path information. -/
theorem cumulativeChart_injective {n : ℕ} :
    Function.Injective (cumulativeChart : JumpPath Ω n →
      (Fin (n + 1) → Ω) × ((Fin n → ℝ) × NNReal)) := by
  intro γ δ h
  have hstates : γ.1 = δ.1 := congrArg (fun p => p.1) h
  have htimes : (fun i : Fin n => jumpTimes γ i.succ) =
      fun i : Fin n => jumpTimes δ i.succ :=
    congrArg (fun p => p.2.1) h
  have htotal : γ.totalHoldingTime = δ.totalHoldingTime :=
    congrArg (fun p => p.2.2) h
  have hpre : ∀ i : Fin n, γ.2 i.castSucc = δ.2 i.castSucc := by
    intro i
    have hcur := congrFun htimes i
    have hprev : jumpTimes γ i.castSucc = jumpTimes δ i.castSucc := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [jumpTimes_zero]
          · simpa using congrFun htimes j.castSucc
    unfold jumpTimes at hcur hprev
    have hset : Finset.Iio i.succ =
        insert i.castSucc (Finset.Iio i.castSucc) := by
      ext j
      simp only [Finset.mem_Iio, Finset.mem_insert, Fin.ext_iff]
      change j.val < i.val + 1 ↔ j.val = i.val ∨ j.val < i.val
      omega
    rw [hset, Finset.sum_insert (by simp),
      Finset.sum_insert (by simp)] at hcur
    rw [hprev] at hcur
    exact_mod_cast add_right_cancel hcur
  have hholding : γ.2 = δ.2 := by
    funext i
    by_cases hi : i = Fin.last n
    · subst i
      have hsum : (∑ j : Fin (n + 1), γ.2 j) =
          ∑ j : Fin (n + 1), δ.2 j := by
        simpa only [totalHoldingTime] using htotal
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
      have hpref : (∑ j : Fin n, γ.2 j.castSucc) =
          ∑ j : Fin n, δ.2 j.castSucc := by
        apply Finset.sum_congr rfl
        intro j _
        exact hpre j
      rw [hpref] at hsum
      exact add_left_cancel hsum
    · rcases Fin.exists_castSucc_eq.2 hi with ⟨j, rfl⟩
      exact hpre j
  exact Prod.ext hstates hholding

theorem cumulativeChart_measurableEmbedding
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {n : ℕ} :
    MeasurableEmbedding (cumulativeChart : JumpPath Ω n →
      (Fin (n + 1) → Ω) × ((Fin n → ℝ) × NNReal)) :=
  measurable_cumulativeChart.measurableEmbedding cumulativeChart_injective

/-- A path has a jump at `S` when one of its noninitial recorded states starts
at exactly that physical time. -/
def HasJumpAt {n : ℕ} (S : NNReal) (γ : JumpPath Ω n) : Prop :=
  ∃ i : Fin n, jumpTimes γ i.succ = (S : ℝ)

theorem measurableSet_hasJumpAt [MeasurableSpace Ω] {n : ℕ} (S : NNReal) :
    MeasurableSet {γ : JumpPath Ω n | HasJumpAt S γ} := by
  simp only [HasJumpAt, Set.setOf_exists]
  exact MeasurableSet.iUnion fun i =>
    ((measurable_jumpTimes i.succ).eq_const (S : ℝ)).setOf

/-- At fixed jump counts, the exact prefix horizon and the matched seam recover
both inputs from their concatenation. -/
theorem concat_injective_of_exact_prefix
    {n m : ℕ} {S : NNReal}
    {γ γ' : JumpPath Ω n} {δ δ' : JumpPath Ω m}
    (hconcat : concat γ δ = concat γ' δ')
    (hγtotal : γ.totalHoldingTime = S)
    (hγ'total : γ'.totalHoldingTime = S)
    (hmatch : γ.1 (Fin.last n) = δ.1 0)
    (hmatch' : γ'.1 (Fin.last n) = δ'.1 0) :
    γ = γ' ∧ δ = δ' := by
  have hγfst : γ.1 = γ'.1 := by
    funext i
    rw [← concat_fst_castAdd γ δ i, hconcat,
      concat_fst_castAdd γ' δ' i]
  have hγsndAway : ∀ i : Fin (n + 1), i ≠ Fin.last n → γ.2 i = γ'.2 i := by
    intro i hi
    have h := congrArg
      (fun p : JumpPath Ω (n + m) =>
        p.2 (Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.castAdd m i))) hconcat
    simpa [concat_snd_castAdd, hi] using h
  have hsumAway :
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), γ.2 i) =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), γ'.2 i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hγsndAway i (Finset.ne_of_mem_erase hi)
  have htotal : (∑ i, γ.2 i) = ∑ i, γ'.2 i := by
    simpa only [totalHoldingTime] using hγtotal.trans hγ'total.symm
  have hγlast : γ.2 (Fin.last n) = γ'.2 (Fin.last n) := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) γ.2
      (Finset.mem_univ (Fin.last n))] at htotal
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) γ'.2
      (Finset.mem_univ (Fin.last n))] at htotal
    rw [hsumAway] at htotal
    exact add_left_cancel htotal
  have hγsnd : γ.2 = γ'.2 := by
    funext i
    by_cases hi : i = Fin.last n
    · simpa [hi] using hγlast
    · exact hγsndAway i hi
  have hδfst : δ.1 = δ'.1 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← hmatch, ← hmatch', hγfst]
    · rw [← concat_fst_natAdd γ δ j, hconcat,
        concat_fst_natAdd γ' δ' j]
  have hδzero : δ.2 0 = δ'.2 0 := by
    have h := congrArg
      (fun p : JumpPath Ω (n + m) => p.2 ⟨n, by omega⟩) hconcat
    simp only [concat_snd_boundary] at h
    rw [hγlast] at h
    exact add_left_cancel h
  have hδsnd : δ.2 = δ'.2 := by
    funext i
    refine Fin.cases hδzero (fun j => ?_) i
    rw [← concat_snd_natAdd γ δ j, hconcat,
      concat_snd_natAdd γ' δ' j]
  constructor
  · exact Prod.ext hγfst hγsnd
  · exact Prod.ext hδfst hδsnd

/-- The support on which fixed-sector concatenation is injective. -/
def exactConcatSupport {n m : ℕ} (S : NNReal) :
    Set (JumpPath Ω n × JumpPath Ω m) :=
  {p | p.1.totalHoldingTime = S ∧
    p.1.1 (Fin.last n) = p.2.1 0}

theorem concat_injOn_exactConcatSupport {n m : ℕ} (S : NNReal) :
    Set.InjOn (fun p : JumpPath Ω n × JumpPath Ω m =>
      concat p.1 p.2) (exactConcatSupport S) := by
  intro p hp q hq hpq
  rcases p with ⟨γ, δ⟩
  rcases q with ⟨γ', δ'⟩
  obtain ⟨hγ, hmatch⟩ := hp
  obtain ⟨hγ', hmatch'⟩ := hq
  obtain ⟨rfl, rfl⟩ := concat_injective_of_exact_prefix hpq
    hγ hγ' hmatch hmatch'
  rfl

/-- Number of jumps whose physical jump time is strictly before `S`. -/
noncomputable def jumpsBefore {k : ℕ} (S : NNReal) (γ : JumpPath Ω k) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i =>
    jumpTimes γ i.succ < (S : ℝ)).card

theorem jumpTimes_concat_lt_cut_iff {n m : ℕ} (S : NNReal)
    (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (hγtotal : γ.totalHoldingTime = S)
    (hcut : ¬ HasJumpAt S (concat γ δ))
    (i : Fin (n + m)) :
    jumpTimes (concat γ δ) i.succ < (S : ℝ) ↔ i.val < n := by
  constructor
  · intro hi
    by_contra hin
    have hni : n ≤ i.val := Nat.le_of_not_gt hin
    let j : Fin (m + 1) := ⟨i.val + 1 - n, by omega⟩
    have hj : j ≠ 0 := by
      intro hj0
      have := congrArg Fin.val hj0
      dsimp [j] at this
      omega
    have hidx : i.succ = Fin.cast (by omega : n + (m + 1) = n + m + 1)
        (Fin.natAdd n j) := by
      apply Fin.ext
      simp [j]
      omega
    rw [hidx, jumpTimes_concat_right γ δ j hj, hγtotal] at hi
    have hjnonneg := jumpTimes_nonneg δ j
    linarith
  · intro hin
    let j : Fin n := ⟨i.val, hin⟩
    have hidx : i.succ = Fin.cast (by omega : (n + 1) + m = n + m + 1)
        (Fin.castAdd m j.succ) := by
      apply Fin.ext
      simp [j]
    rw [hidx, jumpTimes_concat_left γ δ j.succ]
    have hle := jumpTimes_le_totalHoldingTime γ j.succ
    rw [hγtotal] at hle
    apply lt_of_le_of_ne hle
    intro heq
    apply hcut
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    simpa [hidx, jumpTimes_concat_left γ δ j.succ] using heq

/-- An exact prefix contributes exactly its own jump count before the cut. -/
theorem jumpsBefore_concat_of_exact_prefix {n m : ℕ} (S : NNReal)
    (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (hγtotal : γ.totalHoldingTime = S)
    (hcut : ¬ HasJumpAt S (concat γ δ)) :
    jumpsBefore S (concat γ δ) = n := by
  unfold jumpsBefore
  have hfilter :
      ((Finset.univ : Finset (Fin (n + m))).filter fun i =>
        jumpTimes (concat γ δ) i.succ < (S : ℝ)) =
      (Finset.univ : Finset (Fin (n + m))).filter fun i => i.val < n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact jumpTimes_concat_lt_cut_iff S γ δ hγtotal hcut i
  rw [hfilter]
  let s := (Finset.univ : Finset (Fin (n + m))).filter fun i => i.val < n
  have hcard : s.card = (Finset.univ : Finset (Fin n)).card := by
    apply Finset.card_bij (fun i hi => (⟨i.val,
      (Finset.mem_filter.mp hi).2⟩ : Fin n))
    · intro i hi
      simp
    · intro i hi j hj hij
      apply Fin.ext
      exact congrArg (fun x : Fin n => x.val) hij
    · intro j hj
      refine ⟨(⟨j.val, by omega⟩ : Fin (n + m)), ?_, ?_⟩
      · simp
      · apply Fin.ext
        rfl
  simpa [s] using hcard

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

omit [MeasurableSpace Ω] in
/-- Number of jumps strictly before `S`, lifted to complete paths. -/
noncomputable def jumpsBefore (S : NNReal) : FullPath Ω → ℕ
  | ⟨_, γ⟩ => JumpPath.jumpsBefore S γ

omit [MeasurableSpace Ω] in
/-- Exact-prefix, no-cut-jump, seam-matched support for complete-path
concatenation. -/
def exactConcatSupport (S : NNReal) :
    Set (FullPath Ω × FullPath Ω) :=
  {p | totalHoldingTime p.1 = S ∧
    ¬ HasJumpAt S (concat p.1 p.2) ∧
    initialState p.2 = terminalState p.1}

omit [MeasurableSpace Ω] in
/-- **A.e.-support injectivity at the path level.**  Once the prefix exhausts
the cut horizon, the cut is not itself a jump, and the seam states match,
concatenation recovers both complete paths. -/
theorem concat_injOn_exactConcatSupport (S : NNReal) :
    Set.InjOn (fun p : FullPath Ω × FullPath Ω => concat p.1 p.2)
      (exactConcatSupport S) := by
  rintro ⟨⟨n, γ⟩, ⟨m, δ⟩⟩ hp ⟨⟨n', γ'⟩, ⟨m', δ'⟩⟩ hq hconcat
  obtain ⟨hγtotal, hcut, hmatch⟩ := hp
  obtain ⟨hγ'total, hcut', hmatch'⟩ := hq
  change γ.totalHoldingTime = S at hγtotal
  change γ'.totalHoldingTime = S at hγ'total
  change ¬ JumpPath.HasJumpAt S (JumpPath.concat γ δ) at hcut
  change ¬ JumpPath.HasJumpAt S (JumpPath.concat γ' δ') at hcut'
  change δ.1 0 = γ.1 (Fin.last n) at hmatch
  change δ'.1 0 = γ'.1 (Fin.last n') at hmatch'
  have hn : n = n' := by
    have hc := congrArg (jumpsBefore S) hconcat
    change JumpPath.jumpsBefore S (JumpPath.concat γ δ) =
      JumpPath.jumpsBefore S (JumpPath.concat γ' δ') at hc
    rw [JumpPath.jumpsBefore_concat_of_exact_prefix S γ δ hγtotal hcut,
      JumpPath.jumpsBefore_concat_of_exact_prefix S γ' δ' hγ'total hcut'] at hc
    exact hc
  have hnm : n + m = n' + m' := congrArg Sigma.fst hconcat
  have hm : m = m' := by omega
  subst n'
  subst m'
  change (⟨n + m, JumpPath.concat γ δ⟩ : FullPath Ω) =
    ⟨n + m, JumpPath.concat γ' δ'⟩ at hconcat
  have hjp : JumpPath.concat γ δ = JumpPath.concat γ' δ' := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hconcat
  obtain ⟨hγ, hδ⟩ := JumpPath.concat_injective_of_exact_prefix hjp
    hγtotal hγ'total hmatch.symm hmatch'.symm
  subst γ'
  subst δ'
  rfl

/-- The jump-count coordinate of a complete path. -/
def jumpCount : FullPath Ω → ℕ := Sigma.fst

theorem measurable_jumpCount : Measurable (jumpCount : FullPath Ω → ℕ) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun _ : JumpPath Ω n => n) ⁻¹' s)
  exact measurable_const hs

omit [MeasurableSpace Ω] in
/-- A canonical inhabitant of every jump-count sector, used only outside that
sector when constructing measurable projections. -/
def defaultPath (x : Ω) (n : ℕ) : JumpPath Ω n :=
  (fun _ => x, fun _ => 0)

/-- Project a complete path to one fixed sector, using a harmless default away
from that sector. -/
noncomputable def sectorProjection (x : Ω) (n : ℕ) :
    FullPath Ω → JumpPath Ω n
  | ⟨k, γ⟩ => if h : k = n then h ▸ γ else defaultPath x n

theorem measurable_sectorProjection (x : Ω) (n : ℕ) :
    Measurable (sectorProjection x n) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro k
  change MeasurableSet
    ((fun γ : JumpPath Ω k => sectorProjection x n ⟨k, γ⟩) ⁻¹' s)
  by_cases h : k = n
  · subst k
    simpa [sectorProjection] using hs
  · have hm : Measurable (fun γ : JumpPath Ω k =>
        sectorProjection x n ⟨k, γ⟩) := by
      simp only [sectorProjection, h, ↓reduceDIte]
      exact measurable_const
    exact hm hs

omit [MeasurableSpace Ω] in
@[simp]
theorem sectorProjection_mk (x : Ω) {n : ℕ} (γ : JumpPath Ω n) :
    sectorProjection x n ⟨n, γ⟩ = γ := by
  simp [sectorProjection]

/-- Complete-path concatenation is jointly measurable.  The point supplies
defaults for the countable fixed-sector decomposition; the resulting function
does not depend on it. -/
theorem measurable_concat_prod_of_point (x : Ω) :
    Measurable (fun p : FullPath Ω × FullPath Ω => concat p.1 p.2) := by
  intro s hs
  rw [show (fun p : FullPath Ω × FullPath Ω => concat p.1 p.2) ⁻¹' s =
      ⋃ n, ⋃ m,
        ({p | jumpCount p.1 = n ∧ jumpCount p.2 = m} ∩
          (fun p => (⟨n + m, JumpPath.concat
            (sectorProjection x n p.1) (sectorProjection x m p.2)⟩ :
              FullPath Ω)) ⁻¹' s) by
    ext p
    rcases p with ⟨⟨n, γ⟩, ⟨m, δ⟩⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro hp
      refine ⟨n, m, ⟨rfl, rfl⟩, ?_⟩
      rw [sectorProjection_mk, sectorProjection_mk]
      change concat ⟨n, γ⟩ ⟨m, δ⟩ ∈ s
      exact hp
    · rintro ⟨n', m', ⟨hn, hm⟩, hp⟩
      change n = n' at hn
      change m = m' at hm
      subst n'
      subst m'
      rw [sectorProjection_mk, sectorProjection_mk] at hp
      change concat ⟨n, γ⟩ ⟨m, δ⟩ ∈ s at hp
      exact hp]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.inter
  · exact (((measurable_jumpCount.comp measurable_fst).eq_const n).setOf).inter
      (((measurable_jumpCount.comp measurable_snd).eq_const m).setOf)
  · exact ((FullPath.measurable_mk (n + m)).comp
      (JumpPath.measurable_concat_prod.comp
        ((measurable_sectorProjection x n).comp measurable_fst |>.prodMk
          ((measurable_sectorProjection x m).comp measurable_snd)))) hs

/-- Complete-path concatenation is jointly measurable. -/
@[fun_prop]
theorem measurable_concat_prod :
    Measurable (fun p : FullPath Ω × FullPath Ω => concat p.1 p.2) := by
  cases isEmpty_or_nonempty Ω with
  | inl hΩ =>
      intro s hs
      convert MeasurableSet.empty
      ext p
      exact isEmptyElim p.1.2.1 0
  | inr hΩ =>
      exact measurable_concat_prod_of_point (Classical.choice hΩ)

end FullPath

/-- Move a measurable map of the first marginal through a composition-product
by comapping the continuation kernel. -/
theorem map_compProd_eq_map_compProd_comap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (κ : Kernel β γ) [SFinite μ] [IsSFiniteKernel κ]
    (f : α → β) (hf : Measurable f) :
    μ.map f ⊗ₘ κ =
      (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [Measure.map_apply (hf.prodMap measurable_id) hs]
  rw [Measure.compProd_apply (hs.preimage (hf.prodMap measurable_id))]
  rw [MeasureTheory.lintegral_map]
  · apply lintegral_congr
    intro a
    rfl
  · exact Kernel.measurable_kernel_prodMk_left hs
  · exact hf

/-- Normalize a reweighted first marginal followed by a reweighted constant
kernel as one density over the product reference measure. -/
theorem withDensity_compProd_const_withDensity
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α → ℝ≥0∞) (g : α → β → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    [IsSFiniteKernel ((Kernel.const α ν).withDensity g)] :
    μ.withDensity f ⊗ₘ (Kernel.const α ν).withDensity g =
      (μ.prod ν).withDensity (fun p => f p.1 * g p.1 p.2) := by
  calc
    _ = (μ.withDensity f ⊗ₘ Kernel.const α ν).withDensity
        (Function.uncurry g) := Measure.compProd_withDensity hg
    _ = (((μ ⊗ₘ Kernel.const α ν).withDensity (f ∘ Prod.fst)).withDensity
        (Function.uncurry g)) := congrArg
          (fun ξ : Measure (α × β) => ξ.withDensity (Function.uncurry g))
          (MeasureProtocol.Markov.compProd_withDensity_fst
            μ (Kernel.const α ν) f hf).symm
    _ = (μ ⊗ₘ Kernel.const α ν).withDensity
        ((f ∘ Prod.fst) * Function.uncurry g) :=
      (MeasureTheory.withDensity_mul (μ ⊗ₘ Kernel.const α ν)
        (hf.comp measurable_fst) hg).symm
    _ = _ := by rw [Measure.compProd_const]; rfl

/-- Exchange the middle coordinates of a fourfold product measure. -/
theorem measurePreserving_prod_shuffle
    {A B U V : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace U] [MeasurableSpace V]
    (μA : Measure A) (μB : Measure B) (μU : Measure U) (μV : Measure V)
    [SFinite μA] [SFinite μB] [SFinite μU] [SFinite μV] :
    MeasurePreserving
      (fun p : (A × U) × (B × V) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μA.prod μU).prod (μB.prod μV))
      ((μA.prod μB).prod (μU.prod μV)) := by
  let e1 : (A × U) × (B × V) ≃ᵐ A × (U × (B × V)) :=
    MeasurableEquiv.prodAssoc
  let e2 : A × (U × (B × V)) ≃ᵐ A × ((U × B) × V) :=
    MeasurableEquiv.refl A |>.prodCongr MeasurableEquiv.prodAssoc.symm
  let e3 : A × ((U × B) × V) ≃ᵐ A × ((B × U) × V) :=
    MeasurableEquiv.refl A |>.prodCongr
      (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl V))
  let e4 : A × ((B × U) × V) ≃ᵐ A × (B × (U × V)) :=
    MeasurableEquiv.refl A |>.prodCongr MeasurableEquiv.prodAssoc
  let e5 : A × (B × (U × V)) ≃ᵐ (A × B) × (U × V) :=
    MeasurableEquiv.prodAssoc.symm
  have h1 := measurePreserving_prodAssoc μA μU (μB.prod μV)
  have h2 : MeasurePreserving e2
      (μA.prod (μU.prod (μB.prod μV)))
      (μA.prod ((μU.prod μB).prod μV)) :=
    (MeasurePreserving.id μA).prod
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc μU μB μV))
  have h3 : MeasurePreserving e3
      (μA.prod ((μU.prod μB).prod μV))
      (μA.prod ((μB.prod μU).prod μV)) :=
    (MeasurePreserving.id μA).prod
      (Measure.measurePreserving_swap.prod (MeasurePreserving.id μV))
  have h4 : MeasurePreserving e4
      (μA.prod ((μB.prod μU).prod μV))
      (μA.prod (μB.prod (μU.prod μV))) :=
    (MeasurePreserving.id μA).prod
      (measurePreserving_prodAssoc μB μU μV)
  have h5 : MeasurePreserving e5
      (μA.prod (μB.prod (μU.prod μV)))
      ((μA.prod μB).prod (μU.prod μV)) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μA μB (μU.prod μV))
  have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert h using 1
  funext p
  rfl

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

theorem joinTimesEquiv_apply_left (S : ℝ) (n m : ℕ)
    (τ : Fin n → ℝ) (υ : Fin m → ℝ) (i : Fin n) :
    joinTimesEquiv S n m (τ, υ) (Fin.castAdd m i) = τ i := by
  calc
    _ = (splitTimesEquiv n m (joinTimesEquiv S n m (τ, υ))).1 i :=
      (splitTimesEquiv_apply_left n m _ i).symm
    _ = τ i := by
      simp only [joinTimesEquiv, MeasurableEquiv.trans_apply]
      rw [MeasurableEquiv.apply_symm_apply]
      rfl

theorem joinTimesEquiv_apply_right (S : ℝ) (n m : ℕ)
    (τ : Fin n → ℝ) (υ : Fin m → ℝ) (i : Fin m) :
    joinTimesEquiv S n m (τ, υ) (Fin.natAdd n i) = S + υ i := by
  calc
    _ = (splitTimesEquiv n m (joinTimesEquiv S n m (τ, υ))).2 i :=
      (splitTimesEquiv_apply_right n m _ i).symm
    _ = S + υ i := by
      simp only [joinTimesEquiv, MeasurableEquiv.trans_apply]
      rw [MeasurableEquiv.apply_symm_apply]
      rfl

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

/-- Number of cumulative jump times strictly before a deterministic cut. -/
noncomputable def timesBefore {k : ℕ} (S : ℝ) (τ : Fin k → ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i => τ i < S).card

theorem timesBefore_eq_sum {k : ℕ} (S : ℝ) (τ : Fin k → ℝ) :
    timesBefore S τ = ∑ i, if τ i < S then 1 else 0 := by
  classical
  simp [timesBefore]

theorem measurable_timesBefore (S : ℝ) (k : ℕ) :
    Measurable (timesBefore (k := k) S) := by
  have h : (timesBefore (k := k) S) = fun τ =>
      ∑ i, if τ i < S then 1 else 0 := by
    funext τ
    exact timesBefore_eq_sum S τ
  rw [h]
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite
    ((measurable_pi_apply i).lt measurable_const).setOf
    measurable_const measurable_const

/-- A monotone finite family is below a level exactly on the initial segment
whose length is its number of entries below that level. -/
theorem monotone_lt_iff_val_lt_timesBefore
    {k : ℕ} (τ : Fin k → ℝ) (hτ : Monotone τ) (S : ℝ) (i : Fin k) :
    τ i < S ↔ i.val < timesBefore S τ := by
  let r := (Finset.univ.filter fun j : Fin k => τ j < S)
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ r := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [r, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hτ hj).trans_lt hi
    have hc := Finset.card_le_card hsub
    simpa [r, timesBefore] using hc
  · intro hi
    change i.val < r.card at hi
    by_contra hnot
    have hsub : r ⊆ Finset.Iio i := by
      intro j hj
      simp only [r, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      have hij : i ≤ j := le_of_not_gt hji
      exact (not_lt_of_ge (hτ hij)) (lt_of_lt_of_le hj (le_of_not_gt hnot))
    have hc := Finset.card_le_card hsub
    have : r.card ≤ i.val := by simpa [r] using hc
    omega

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

theorem cutOrderedSimplexSet_subset_orderedSimplexSet_add
    (S T : NNReal) (n m : ℕ) :
    cutOrderedSimplexSet S T n m ⊆ orderedSimplexSet (S + T) (n + m) := by
  intro τ hτ
  rcases hτ with ⟨p, hp, rfl⟩
  rcases hp with ⟨hα, hβ⟩
  constructor
  · intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · rw [joinTimesEquiv_apply_left]
      exact ⟨(hα.1 a).1,
        (hα.1 a).2.trans (le_add_of_nonneg_right T.coe_nonneg)⟩
    · rw [joinTimesEquiv_apply_right]
      constructor
      · exact add_nonneg S.coe_nonneg (hβ.1 b).1
      · simpa [add_comm] using add_le_add_left (hβ.1 b).2 S
  · intro i j hij
    revert j
    refine Fin.addCases (motive := fun i => ∀ ⦃j⦄, i ≤ j →
        joinTimesEquiv S n m p i ≤ joinTimesEquiv S n m p j)
      (fun a {j} hij => ?_) (fun b {j} hij => ?_) i
    · revert hij
      refine Fin.addCases (motive := fun j => Fin.castAdd m a ≤ j →
          joinTimesEquiv S n m p (Fin.castAdd m a) ≤
            joinTimesEquiv S n m p j)
        (fun c hij => ?_) (fun d hij => ?_) j
      · rw [joinTimesEquiv_apply_left, joinTimesEquiv_apply_left]
        apply hα.2
        apply Fin.le_iff_val_le_val.mpr
        exact Fin.le_iff_val_le_val.mp hij
      · rw [joinTimesEquiv_apply_left, joinTimesEquiv_apply_right]
        exact (hα.1 a).2.trans (le_add_of_nonneg_right (hβ.1 d).1)
    · revert hij
      refine Fin.addCases (motive := fun j => Fin.natAdd n b ≤ j →
          joinTimesEquiv S n m p (Fin.natAdd n b) ≤
            joinTimesEquiv S n m p j)
        (fun c hij => ?_) (fun d hij => ?_) j
      · exfalso
        have hv := Fin.le_iff_val_le_val.mp hij
        change n + b.val ≤ c.val at hv
        have hc := c.isLt
        omega
      · rw [joinTimesEquiv_apply_right, joinTimesEquiv_apply_right]
        simpa [add_comm] using add_le_add_left
          (hβ.2 ((Fin.natAdd_le_natAdd_iff n).mp hij)) S

/-- The disjoint global ordered-time sector with exactly `n` jumps strictly
before the cut. -/
def orderedCountSet (S T : NNReal) (n m : ℕ) :
    Set (Fin (n + m) → ℝ) :=
  orderedSimplexSet (S + T) (n + m) ∩ {τ | timesBefore S τ = n}

theorem measurableSet_orderedCountSet (S T : NNReal) (n m : ℕ) :
    MeasurableSet (orderedCountSet S T n m) :=
  (measurableSet_orderedSimplexSet (S + T) (n + m)).inter
    ((measurable_timesBefore S (n + m)).eq_const n).setOf

theorem orderedCountSet_subset_cutOrderedSimplexSet
    (S T : NNReal) (n m : ℕ) :
    orderedCountSet S T n m ⊆ cutOrderedSimplexSet S T n m := by
  intro τ hτ
  rcases hτ with ⟨hord, hcount⟩
  let p := (joinTimesEquiv S n m).symm τ
  have hjoin : joinTimesEquiv S n m p = τ :=
    (joinTimesEquiv S n m).apply_symm_apply τ
  refine ⟨p, ?_, hjoin⟩
  constructor
  · constructor
    · intro i
      have hi : τ (Fin.castAdd m i) < (S : ℝ) := by
        rw [monotone_lt_iff_val_lt_timesBefore τ hord.2 S]
        rw [hcount]
        simp
      have heq : p.1 i = τ (Fin.castAdd m i) := by
        rw [← hjoin, joinTimesEquiv_apply_left]
      rw [heq]
      exact ⟨(hord.1 (Fin.castAdd m i)).1, hi.le⟩
    · intro i j hij
      have hei : p.1 i = τ (Fin.castAdd m i) := by
        rw [← hjoin, joinTimesEquiv_apply_left]
      have hej : p.1 j = τ (Fin.castAdd m j) := by
        rw [← hjoin, joinTimesEquiv_apply_left]
      rw [hei, hej]
      apply hord.2
      apply Fin.le_iff_val_le_val.mpr
      exact Fin.le_iff_val_le_val.mp hij
  · constructor
    · intro i
      have hnot : ¬ τ (Fin.natAdd n i) < (S : ℝ) := by
        rw [monotone_lt_iff_val_lt_timesBefore τ hord.2 S]
        rw [hcount]
        simp
      have heq : (S : ℝ) + p.2 i = τ (Fin.natAdd n i) := by
        rw [← hjoin, joinTimesEquiv_apply_right]
      have hglobal := hord.1 (Fin.natAdd n i)
      constructor
      · linarith
      · have hupper : τ (Fin.natAdd n i) ≤ (S : ℝ) + T := by
          simpa only [NNReal.coe_add] using hglobal.2
        linarith
    · intro i j hij
      have hei : (S : ℝ) + p.2 i = τ (Fin.natAdd n i) := by
        rw [← hjoin, joinTimesEquiv_apply_right]
      have hej : (S : ℝ) + p.2 j = τ (Fin.natAdd n j) := by
        rw [← hjoin, joinTimesEquiv_apply_right]
      have hmono := hord.2 ((Fin.natAdd_le_natAdd_iff n).2 hij)
      linarith

def cutBoundarySet (S : NNReal) (k : ℕ) : Set (Fin k → ℝ) :=
  {τ | ∃ i, τ i = (S : ℝ)}

theorem measurableSet_cutBoundarySet (S : NNReal) (k : ℕ) :
    MeasurableSet (cutBoundarySet S k) := by
  unfold cutBoundarySet
  rw [show {τ : Fin k → ℝ | ∃ i, τ i = (S : ℝ)} =
      ⋃ i, {τ | τ i = (S : ℝ)} by ext τ; simp]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_eq_fun (measurable_pi_apply i)
      (measurable_const : Measurable fun _ : Fin k → ℝ => (S : ℝ))

theorem volume_cutBoundarySet (S : NNReal) (k : ℕ) :
    (volume : Measure (Fin k → ℝ)) (cutBoundarySet S k) = 0 := by
  unfold cutBoundarySet
  rw [show {τ : Fin k → ℝ | ∃ i, τ i = (S : ℝ)} =
      ⋃ i, {τ | τ i = (S : ℝ)} by ext τ; simp]
  apply measure_iUnion_null
  intro i
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin k => (volume : Measure ℝ)) i S

theorem cutOrderedSimplexSet_subset_orderedCountSet_union_boundary
    (S T : NNReal) (n m : ℕ) :
    cutOrderedSimplexSet S T n m ⊆
      orderedCountSet S T n m ∪ cutBoundarySet S (n + m) := by
  intro τ hτ
  have hord := cutOrderedSimplexSet_subset_orderedSimplexSet_add S T n m hτ
  by_cases hboundary : τ ∈ cutBoundarySet S (n + m)
  · exact Or.inr hboundary
  · left
    refine ⟨hord, ?_⟩
    rcases hτ with ⟨p, hp, hpτ⟩
    rcases hp with ⟨hα, hβ⟩
    have hnone : ∀ i, τ i ≠ (S : ℝ) := by
      intro i hi
      exact hboundary ⟨i, hi⟩
    have hiff : ∀ i : Fin (n + m), τ i < (S : ℝ) ↔ i.val < n := by
      intro i
      rw [← hpτ]
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · rw [joinTimesEquiv_apply_left]
        constructor
        · intro _
          simp
        · intro _
          exact lt_of_le_of_ne (hα.1 a).2 (by
            intro heq
            apply hnone (Fin.castAdd m a)
            rw [← hpτ, joinTimesEquiv_apply_left]
            exact heq)
      · rw [joinTimesEquiv_apply_right]
        constructor
        · intro hlt
          have hnonneg := (hβ.1 b).1
          linarith
        · intro hval
          simp at hval
    change timesBefore S τ = n
    unfold timesBefore
    have hfilter :
        ((Finset.univ : Finset (Fin (n + m))).filter fun i =>
          τ i < (S : ℝ)) =
        (Finset.univ : Finset (Fin (n + m))).filter fun i => i.val < n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hiff i
    rw [hfilter]
    let r := (Finset.univ : Finset (Fin (n + m))).filter fun i => i.val < n
    have hcard : r.card = (Finset.univ : Finset (Fin n)).card := by
      apply Finset.card_bij (fun i hi => (⟨i.val,
        (Finset.mem_filter.mp hi).2⟩ : Fin n))
      · intro i hi
        simp
      · intro i hi j hj hij
        apply Fin.ext
        exact congrArg (fun z : Fin n => z.val) hij
      · intro j hj
        refine ⟨(⟨j.val, by omega⟩ : Fin (n + m)), ?_, ?_⟩
        · simp
        · apply Fin.ext
          rfl
    simpa using hcard

theorem volume_restrict_cutOrdered_eq_orderedCount
    (S T : NNReal) (n m : ℕ) :
    (volume : Measure (Fin (n + m) → ℝ)).restrict
        (cutOrderedSimplexSet S T n m) =
      (volume : Measure (Fin (n + m) → ℝ)).restrict
        (orderedCountSet S T n m) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null
      (show cutOrderedSimplexSet S T n m \ orderedCountSet S T n m ⊆
        cutBoundarySet S (n + m) by
        intro τ hτ
        rcases cutOrderedSimplexSet_subset_orderedCountSet_union_boundary
          S T n m hτ.1 with h | h
        · exact (hτ.2 h).elim
        · exact h)
    exact volume_cutBoundarySet S (n + m)
  · apply measure_mono_null
      (show orderedCountSet S T n m \ cutOrderedSimplexSet S T n m ⊆ ∅ by
        intro τ hτ
        exact (hτ.2 (orderedCountSet_subset_cutOrderedSimplexSet
          S T n m hτ.1)).elim)
    exact measure_empty

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

/-! ### The normalized free-simplex chart in cumulative-time coordinates -/

theorem partialSum_succ_eq_sum_Iic {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    Fin.partialSum u i.succ = ∑ j ∈ Finset.Iic i, u j := by
  unfold Fin.partialSum
  rw [List.sum_take_ofFn]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    change j.val < i.val + 1 ↔ j.val ≤ i.val
    omega
  · simp

theorem cumulativeTimes_eq_sum_Iic {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    cumulativeTimes n u i = ∑ j ∈ Finset.Iic i, u j := by
  rw [cumulativeTimes_eq_partialSum]
  exact partialSum_succ_eq_sum_Iic u i

/-- Nonnegative physical holding increments whose total does not exceed the
horizon. -/
def incrementSimplexSet (H : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ H}

theorem measurableSet_incrementSimplexSet (H : ℝ) (n : ℕ) :
    MeasurableSet (incrementSimplexSet H n) := by
  unfold incrementSimplexSet
  rw [show {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ H} =
      (⋂ i, {u | 0 ≤ u i}) ∩ {u | ∑ i, u i ≤ H} by ext u; simp]
  exact (MeasurableSet.iInter fun i =>
    measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_le (by fun_prop) measurable_const)

theorem preimage_orderedSimplexSet_cumulativeTimes (H : NNReal) (n : ℕ) :
    cumulativeTimes n ⁻¹' orderedSimplexSet H n =
      incrementSimplexSet H n := by
  cases n with
  | zero =>
      ext u
      change ((∀ i : Fin 0, 0 ≤ cumulativeTimes 0 u i ∧
          cumulativeTimes 0 u i ≤ (H : ℝ)) ∧
          Monotone (cumulativeTimes 0 u)) ↔
        ((∀ i : Fin 0, 0 ≤ u i) ∧ ∑ i, u i ≤ (H : ℝ))
      constructor
      · intro _
        constructor
        · intro i
          exact Fin.elim0 i
        · change (0 : ℝ) ≤ H
          exact H.coe_nonneg
      · intro _
        constructor
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
  | succ n =>
      ext u
      simp only [Set.mem_preimage, orderedSimplexSet, Set.mem_setOf_eq,
        incrementSimplexSet]
      constructor
      · rintro ⟨hbounds, hmono⟩
        constructor
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa [cumulativeTimes] using (hbounds 0).1
          · have hstep := hmono
              (show Fin.castSucc j < j.succ from Fin.castSucc_lt_succ).le
            rw [cumulativeTimes_eq_partialSum,
              cumulativeTimes_eq_partialSum] at hstep
            have hright : Fin.partialSum u j.succ.succ =
                Fin.partialSum u (Fin.castSucc j).succ + u j.succ := by
              exact Fin.partialSum_succ u j.succ
            rw [hright] at hstep
            linarith
        · have hlast := (hbounds (Fin.last n)).2
          rw [cumulativeTimes_eq_sum_Iic] at hlast
          have hIic : Finset.Iic (Fin.last n) = Finset.univ := by
            ext i
            simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
            exact Fin.le_last _
          rw [hIic] at hlast
          exact hlast
      · rintro ⟨hnonneg, hsum⟩
        constructor
        · intro i
          constructor
          · rw [cumulativeTimes_eq_sum_Iic]
            exact Finset.sum_nonneg fun j _ => hnonneg j
          · rw [cumulativeTimes_eq_sum_Iic]
            exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hnonneg j)).trans hsum
        · intro i j hij
          rw [cumulativeTimes_eq_sum_Iic, cumulativeTimes_eq_sum_Iic]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Iic_subset_Iic.mpr hij) (fun k _ _ => hnonneg k)

/-- Coordinatewise inclusion of the unit interval into the reals. -/
def coePi (n : ℕ) : (Fin n → I) → (Fin n → ℝ) :=
  fun u i => (u i : ℝ)

theorem measurePreserving_coePi (n : ℕ) :
    MeasurePreserving (coePi n) (volume : Measure (Fin n → I))
      ((volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1)) := by
  constructor
  · rw [measurable_pi_iff]
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  · unfold coePi
    letI (i : Fin n) : SigmaFinite
        ((volume : Measure I).map ((↑) : I → ℝ)) := by
      rw [unitInterval.measurePreserving_coe.map_eq]
      infer_instance
    rw [volume_pi]
    rw [Measure.pi_map_pi
      (X := fun _ : Fin n => I) (Y := fun _ : Fin n => ℝ)
      (f := fun _ => ((↑) : I → ℝ))
      (fun _ => unitInterval.measurePreserving_coe.aemeasurable)]
    simp_rw [unitInterval.measurePreserving_coe.map_eq]
    rw [← Measure.restrict_pi_pi]
    change (volume : Measure (Fin n → ℝ)).restrict
      (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) = _
    rfl

theorem preimage_incrementSimplexSet_coePi (n : ℕ) :
    coePi n ⁻¹' incrementSimplexSet 1 n = freeSimplexSet n := by
  ext u
  simp only [Set.mem_preimage, incrementSimplexSet, Set.mem_setOf_eq,
    coePi, freeSimplexSet]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => (u i).2.1, h⟩

theorem incrementSimplexSet_one_subset_cube (n : ℕ) :
    incrementSimplexSet 1 n ⊆
      Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1 := by
  intro u hu
  rw [Set.mem_pi]
  intro i _
  constructor
  · exact hu.1 i
  · exact (Finset.single_le_sum (fun j _ => hu.1 j)
      (Finset.mem_univ i)).trans hu.2

theorem measurePreserving_coePi_restrict (n : ℕ) :
    MeasurePreserving (coePi n)
      ((volume : Measure (Fin n → I)).restrict (freeSimplexSet n))
      ((volume : Measure (Fin n → ℝ)).restrict
        (incrementSimplexSet 1 n)) := by
  have h := (measurePreserving_coePi n).restrict_preimage
    (measurableSet_incrementSimplexSet 1 n)
  rw [preimage_incrementSimplexSet_coePi] at h
  rw [Measure.restrict_restrict_of_subset
    (incrementSimplexSet_one_subset_cube n)] at h
  exact h

theorem pi_const_smul (c : NNReal) (n : ℕ) :
    Measure.pi (fun _ : Fin n => c • (volume : Measure ℝ)) =
      (c : ℝ≥0∞) ^ n • (volume : Measure (Fin n → ℝ)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply]
  change (c : ℝ≥0∞) ^ n *
      (volume : Measure (Fin n → ℝ)) (Set.univ.pi s) = _
  rw [volume_pi_pi s]
  change (c : ℝ≥0∞) ^ n * ∏ i, volume (s i) =
    ∏ i : Fin n, (c : ℝ≥0∞) * volume (s i)
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp

/-- Coordinatewise multiplication by the physical horizon. -/
def scalePi (H : NNReal) (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun u i => (H : ℝ) * u i

theorem measurePreserving_scalePi (H : NNReal) (hH : H ≠ 0) (n : ℕ) :
    MeasurePreserving (scalePi H n)
      ((H : ℝ≥0∞) ^ n • (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin n → ℝ)) := by
  have hcoord : MeasurePreserving (fun x : ℝ => (H : ℝ) * x)
      (H • (volume : Measure ℝ)) volume := by
    constructor
    · fun_prop
    · rw [Measure.map_smul]
      simpa [abs_of_nonneg H.coe_nonneg] using
        (Real.smul_map_volume_mul_left (show (H : ℝ) ≠ 0 by exact_mod_cast hH))
  constructor
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_const_mul (H : ℝ)).comp (measurable_pi_apply i)
  · rw [← pi_const_smul H n]
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (by
      rw [measurable_pi_iff]
      intro i
      exact (measurable_const_mul (H : ℝ)).comp (measurable_pi_apply i))
      (MeasurableSet.univ_pi hs)]
    have hpre : scalePi H n ⁻¹' (Set.univ.pi s) =
        Set.univ.pi fun i => (fun x : ℝ => (H : ℝ) * x) ⁻¹' s i := by
      ext u
      simp [scalePi]
    rw [hpre, Measure.pi_pi _]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Measure.map_apply hcoord.measurable (hs i), hcoord.map_eq]

theorem preimage_incrementSimplexSet_scalePi (H : NNReal) (hH : 0 < H)
    (n : ℕ) :
    scalePi H n ⁻¹' incrementSimplexSet H n =
      incrementSimplexSet 1 n := by
  ext u
  simp only [Set.mem_preimage, incrementSimplexSet, Set.mem_setOf_eq,
    scalePi]
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  constructor
  · rintro ⟨hnonneg, hsum⟩
    constructor
    · intro i
      have hi := hnonneg i
      nlinarith
    · rw [← Finset.mul_sum] at hsum
      nlinarith
  · rintro ⟨hnonneg, hsum⟩
    constructor
    · intro i
      exact mul_nonneg hHr.le (hnonneg i)
    · rw [← Finset.mul_sum]
      nlinarith

theorem measurePreserving_scalePi_restrict (H : NNReal) (hH : 0 < H)
    (n : ℕ) :
    MeasurePreserving (scalePi H n)
      ((H : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → ℝ)).restrict
          (incrementSimplexSet 1 n))
      ((volume : Measure (Fin n → ℝ)).restrict
        (incrementSimplexSet H n)) := by
  have h := (measurePreserving_scalePi H hH.ne' n).restrict_preimage
    (measurableSet_incrementSimplexSet H n)
  rw [preimage_incrementSimplexSet_scalePi H hH,
    Measure.restrict_smul] at h
  exact h

/-- The physical cumulative jump-time chart used by `assemblePath`. -/
def physicalCumulativeTimes (H : NNReal) (n : ℕ) :
    (Fin n → I) → (Fin n → ℝ) :=
  fun u => cumulativeTimes n (scalePi H n (coePi n u))

/-- The cumulative chart of an assembled path is the physical cumulative-time
chart of its free simplex coordinates. -/
theorem jumpTimes_assemblePath
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (H : NNReal) (states : Fin (n + 1) → Ω)
    (u : Fin n → I) (i : Fin n) :
    JumpPath.jumpTimes (assemblePath H (states, u)) i.succ =
      physicalCumulativeTimes H n u i := by
  rw [JumpPath.jumpTimes]
  rw [show Finset.Iio i.succ = (Finset.Iic i).map Fin.castSuccEmb by
    rw [Fin.map_castSuccEmb_Iic]
    ext j
    simp only [Finset.mem_Iio, Finset.mem_Iic]
    change j.val < i.val + 1 ↔ j.val ≤ i.val
    omega]
  rw [Finset.sum_map]
  simp only [assemblePath, holdingTimesOfFree, Fin.castSuccEmb_apply,
    Fin.snoc_castSucc, NNReal.coe_mul, coe_unitNNReal]
  rw [physicalCumulativeTimes, cumulativeTimes_eq_sum_Iic]
  rfl

theorem measurePreserving_physicalCumulativeTimes_restrict
    (H : NNReal) (hH : 0 < H) (n : ℕ) :
    MeasurePreserving (physicalCumulativeTimes H n)
      ((H : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → I)).restrict
          (freeSimplexSet n))
      ((volume : Measure (Fin n → ℝ)).restrict
        (orderedSimplexSet H n)) := by
  have hcoe : MeasurePreserving (coePi n)
      ((H : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → I)).restrict
          (freeSimplexSet n))
      ((H : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → ℝ)).restrict
          (incrementSimplexSet 1 n)) := by
    constructor
    · exact (measurePreserving_coePi_restrict n).measurable
    · rw [Measure.map_smul, (measurePreserving_coePi_restrict n).map_eq]
  have hscale := (measurePreserving_scalePi_restrict H hH n).comp hcoe
  have hcum := (measurePreserving_cumulativeTimes n).restrict_preimage
    (measurableSet_orderedSimplexSet H n)
  rw [preimage_orderedSimplexSet_cumulativeTimes H n] at hcum
  have h := hcum.comp hscale
  exact h.congr
    ((measurePreserving_cumulativeTimes n).measurable.comp
      ((measurePreserving_scalePi_restrict H hH n).measurable.comp
        (measurePreserving_coePi_restrict n).measurable))
    (ae_of_all _ fun u => rfl)

/-- The normalized free-simplex chart transports to physical ordered jump
times without a Jacobian calculation in holding-increment coordinates. -/
theorem map_scaledFreeSimplex_cumulativeTimes
    (H : NNReal) (hH : 0 < H) (n : ℕ) :
    (((H : ℝ≥0∞) ^ n •
      (volume : Measure (Fin n → I)).restrict
        (freeSimplexSet n)).map
      (physicalCumulativeTimes H n)) =
      (volume : Measure (Fin n → ℝ)).restrict
        (orderedSimplexSet H n) :=
  (measurePreserving_physicalCumulativeTimes_restrict H hH n).map_eq

/-- **Time-coordinate transport for a cut.**  Mapping the product of scaled
free simplexes through their physical cumulative-time charts and then joining
at `S` gives Lebesgue measure restricted to the global cut-ordered simplex. -/
theorem map_prod_scaledFreeSimplex_joinPhysicalCumulativeTimes
    (S T : NNReal) (hS : 0 < S) (hT : 0 < T) (n m : ℕ) :
    ((((S : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → I)).restrict (freeSimplexSet n)).prod
      ((T : ℝ≥0∞) ^ m •
        (volume : Measure (Fin m → I)).restrict (freeSimplexSet m))).map
      (fun p => joinTimesEquiv S n m
        (physicalCumulativeTimes S n p.1,
          physicalCumulativeTimes T m p.2))) =
      (volume : Measure (Fin (n + m) → ℝ)).restrict
        (cutOrderedSimplexSet S T n m) := by
  let μS := (S : ℝ≥0∞) ^ n •
    (volume : Measure (Fin n → I)).restrict (freeSimplexSet n)
  let μT := (T : ℝ≥0∞) ^ m •
    (volume : Measure (Fin m → I)).restrict (freeSimplexSet m)
  have hphysS : Measurable (physicalCumulativeTimes S n) :=
    (measurePreserving_physicalCumulativeTimes_restrict S hS n).measurable
  have hphysT : Measurable (physicalCumulativeTimes T m) :=
    (measurePreserving_physicalCumulativeTimes_restrict T hT m).measurable
  calc
    (μS.prod μT).map
        (fun p => joinTimesEquiv S n m
          (physicalCumulativeTimes S n p.1,
            physicalCumulativeTimes T m p.2)) =
      ((μS.prod μT).map
        (Prod.map (physicalCumulativeTimes S n)
          (physicalCumulativeTimes T m))).map (joinTimesEquiv S n m) := by
        rw [Measure.map_map]
        · rfl
        · exact (joinTimesEquiv S n m).measurable
        · exact hphysS.prodMap hphysT
    _ = ((μS.map (physicalCumulativeTimes S n)).prod
          (μT.map (physicalCumulativeTimes T m))).map
            (joinTimesEquiv S n m) := by
        rw [Measure.map_prod_map μS μT hphysS hphysT]
    _ = ((((volume : Measure (Fin n → ℝ)).restrict
            (orderedSimplexSet S n)).prod
          ((volume : Measure (Fin m → ℝ)).restrict
            (orderedSimplexSet T m))).map (joinTimesEquiv S n m)) := by
        rw [map_scaledFreeSimplex_cumulativeTimes S hS n,
          map_scaledFreeSimplex_cumulativeTimes T hT m]
    _ = _ := map_orderedSimplex_prod_joinTimes S T n m

end Simplex

namespace JumpPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Join two state sequences while dropping the duplicated initial state of
the suffix. -/
def seamJoinStates {n m : ℕ}
    (a : Fin (n + 1) → Ω) (b : Fin (m + 1) → Ω) :
    Fin (n + m + 1) → Ω :=
  fun i => Fin.append (m := n + 1) (n := m) a (b ∘ Fin.succ)
    (Fin.cast (by omega) i)

/-- State-sequence pairs whose boundary states agree. -/
def seamStatePairs (n m : ℕ) :=
  {p : (Fin (n + 1) → Ω) × (Fin (m + 1) → Ω) |
    p.1 (Fin.last n) = p.2 0}

def splitPrefixStates (n m : ℕ) (c : Fin (n + m + 1) → Ω) :
    Fin (n + 1) → Ω := fun i =>
  c (Fin.cast (by omega) (Fin.castAdd m i))

def splitSuffixStates (n m : ℕ) (c : Fin (n + m + 1) → Ω) :
    Fin (m + 1) → Ω :=
  Fin.cons (c ⟨n, by omega⟩) fun j =>
    c (Fin.cast (by omega) (Fin.natAdd (n + 1) j))

omit [MeasurableSpace Ω] in
theorem splitStates_seam (n m : ℕ) (c : Fin (n + m + 1) → Ω) :
    splitPrefixStates n m c (Fin.last n) = splitSuffixStates n m c 0 := by
  apply congrArg c
  apply Fin.ext
  simp

omit [MeasurableSpace Ω] in
theorem seamJoinStates_splitStates (n m : ℕ)
    (c : Fin (n + m + 1) → Ω) :
    seamJoinStates (splitPrefixStates n m c) (splitSuffixStates n m c) = c := by
  funext i
  unfold seamJoinStates
  let i' : Fin ((n + 1) + m) := Fin.cast (by omega) i
  have hi : i = Fin.cast (by omega) i' := by
    apply Fin.ext
    rfl
  rw [hi]
  change Fin.append (splitPrefixStates n m c)
      (splitSuffixStates n m c ∘ Fin.succ) i' = c (Fin.cast (by omega) i')
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i'
  · simp [splitPrefixStates]
  · simp [splitSuffixStates]

omit [MeasurableSpace Ω] in
theorem splitStates_seamJoinStates {n m : ℕ}
    (p : seamStatePairs (Ω := Ω) n m) :
    (splitPrefixStates n m (seamJoinStates p.1.1 p.1.2),
      splitSuffixStates n m (seamJoinStates p.1.1 p.1.2)) = p.1 := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  change a (Fin.last n) = b 0 at hab
  apply Prod.ext
  · funext i
    simp [splitPrefixStates, seamJoinStates]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [splitSuffixStates, Fin.cons_zero]
      change seamJoinStates a b ⟨n, by omega⟩ = b 0
      rw [show (⟨n, by omega⟩ : Fin (n + m + 1)) =
          Fin.cast (by omega : (n + 1) + m = n + m + 1)
            (Fin.castAdd m (Fin.last n)) by
        apply Fin.ext
        simp]
      simpa [seamJoinStates] using hab
    · simp [splitSuffixStates, seamJoinStates]

/-- Seam-matched state-sequence pairs are in bijection with global state
sequences. -/
noncomputable def seamStateEquiv (n m : ℕ) :
    seamStatePairs (Ω := Ω) n m ≃ (Fin (n + m + 1) → Ω) where
  toFun p := seamJoinStates p.1.1 p.1.2
  invFun c := ⟨(splitPrefixStates n m c, splitSuffixStates n m c),
    splitStates_seam n m c⟩
  left_inv p := by
    apply Subtype.ext
    exact splitStates_seamJoinStates p
  right_inv := seamJoinStates_splitStates n m

/-- **Chart-level concatenation square.**  On the two free-simplex supports,
concatenation followed by the cumulative path chart is state-sequence gluing,
translation of suffix jump times by the cut, and addition of durations. -/
theorem cumulativeChart_concat_assemblePath
    {n m : ℕ} (S T : NNReal)
    (a : Fin (n + 1) → Ω) (b : Fin (m + 1) → Ω)
    (u : Fin n → I) (v : Fin m → I)
    (hu : u ∈ Simplex.freeSimplexSet n)
    (hv : v ∈ Simplex.freeSimplexSet m) :
    cumulativeChart
        (concat (Simplex.assemblePath S (a, u))
          (Simplex.assemblePath T (b, v))) =
      (seamJoinStates a b,
        (Simplex.joinTimesEquiv S n m
          (Simplex.physicalCumulativeTimes S n u,
            Simplex.physicalCumulativeTimes T m v), S + T)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change (fun i : Fin (n + m) => jumpTimes
          (concat (Simplex.assemblePath S (a, u))
            (Simplex.assemblePath T (b, v))) i.succ) = _
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change jumpTimes _ (Fin.castAdd m j).succ =
          Simplex.joinTimesEquiv S n m
            (Simplex.physicalCumulativeTimes S n u,
              Simplex.physicalCumulativeTimes T m v) (Fin.castAdd m j)
        rw [Simplex.joinTimesEquiv_apply_left]
        have hidx : (Fin.castAdd m j).succ =
            Fin.cast (by omega : (n + 1) + m = n + m + 1)
              (Fin.castAdd m j.succ) := by
          apply Fin.ext
          rfl
        calc
          _ = jumpTimes (Simplex.assemblePath S (a, u)) j.succ := by
            rw [hidx, jumpTimes_concat_left]
          _ = _ := Simplex.jumpTimes_assemblePath S a u j
      · change jumpTimes _ (Fin.natAdd n j).succ =
          Simplex.joinTimesEquiv S n m
            (Simplex.physicalCumulativeTimes S n u,
              Simplex.physicalCumulativeTimes T m v) (Fin.natAdd n j)
        rw [Simplex.joinTimesEquiv_apply_right]
        have htotal :
            (Simplex.assemblePath S (a, u)).totalHoldingTime = S := by
          exact Simplex.sum_holdingTimesOfFree S u hu
        have hidx : (Fin.natAdd n j).succ = Fin.natAdd n j.succ := by
          apply Fin.ext
          rfl
        calc
          _ = ((Simplex.assemblePath S (a, u)).totalHoldingTime : ℝ) +
              jumpTimes (Simplex.assemblePath T (b, v)) j.succ := by
            rw [hidx]
            convert jumpTimes_concat_right
              (Simplex.assemblePath S (a, u))
              (Simplex.assemblePath T (b, v)) j.succ (by simp) using 1
            congr 1
          _ = (S : ℝ) + Simplex.physicalCumulativeTimes T m v j := by
            rw [htotal, Simplex.jumpTimes_assemblePath]
    · change (concat (Simplex.assemblePath S (a, u))
          (Simplex.assemblePath T (b, v))).totalHoldingTime = S + T
      rw [totalHoldingTime_concat]
      change (∑ i, Simplex.holdingTimesOfFree S u i) +
          ∑ i, Simplex.holdingTimesOfFree T v i = S + T
      rw [Simplex.sum_holdingTimesOfFree S u hu,
        Simplex.sum_holdingTimesOfFree T v hv]

/-- The joint state/cumulative-time chart obtained by gluing two sector
charts at the deterministic cut. -/
noncomputable def jointCumulativeJoin (S T : NNReal) (n m : ℕ) :
    (((Fin (n + 1) → Ω) × (Fin n → I)) ×
      ((Fin (m + 1) → Ω) × (Fin m → I))) →
      ((Fin (n + m + 1) → Ω) × ((Fin (n + m) → ℝ) × NNReal)) := fun p =>
  (seamJoinStates p.1.1 p.2.1,
    (Simplex.joinTimesEquiv S n m
      (Simplex.physicalCumulativeTimes S n p.1.2,
        Simplex.physicalCumulativeTimes T m p.2.2), S + T))

theorem measurable_seamJoinStates [MeasurableSingletonClass Ω] [Countable Ω]
    (n m : ℕ) : Measurable (fun p : (Fin (n + 1) → Ω) ×
      (Fin (m + 1) → Ω) => seamJoinStates p.1 p.2) :=
  Measurable.of_discrete

theorem measurable_physicalCumulativeTimes (H : NNReal) (n : ℕ) :
    Measurable (Simplex.physicalCumulativeTimes H n) := by
  unfold Simplex.physicalCumulativeTimes
  exact (Simplex.measurable_cumulativeTimes n).comp
    ((by unfold Simplex.scalePi; fun_prop :
      Measurable (Simplex.scalePi H n)).comp
        (Simplex.measurePreserving_coePi n).measurable)

theorem measurable_jointCumulativeJoin
    [MeasurableSingletonClass Ω] [Countable Ω]
    (S T : NNReal) (n m : ℕ) :
    Measurable (jointCumulativeJoin (Ω := Ω) S T n m) := by
  unfold jointCumulativeJoin
  apply Measurable.prodMk
  · exact (measurable_seamJoinStates (Ω := Ω) n m).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
  · apply Measurable.prodMk
    · apply (Simplex.joinTimesEquiv S n m).measurable.comp
      exact (measurable_physicalCumulativeTimes S n).comp
          (measurable_snd.comp measurable_fst) |>.prodMk
        ((measurable_physicalCumulativeTimes T m).comp
          (measurable_snd.comp measurable_snd))
    · exact measurable_const

/-- Paths in the global `(n+m)` sector whose cumulative jump times belong to
the chart obtained by cutting after the first `n` jumps. -/
def cutSectorSet (S T : NNReal) (n m : ℕ) : Set (JumpPath Ω (n + m)) :=
  {γ | (cumulativeChart γ).2.1 ∈ Simplex.cutOrderedSimplexSet S T n m}

theorem measurableSet_cutSectorSet (S T : NNReal) (n m : ℕ) :
    MeasurableSet (cutSectorSet (Ω := Ω) S T n m) := by
  exact (Simplex.measurableSet_cutOrderedSimplexSet S T n m).preimage
    (measurable_fst.comp (measurable_snd.comp measurable_cumulativeChart))

omit [MeasurableSpace Ω] in
theorem jumpsBefore_eq_timesBefore {k : ℕ} (S : NNReal) (γ : JumpPath Ω k) :
    jumpsBefore S γ = Simplex.timesBefore S (cumulativeChart γ).2.1 := rfl

theorem measurable_jumpsBefore (S : NNReal) (k : ℕ) :
    Measurable (jumpsBefore (Ω := Ω) (k := k) S) := by
  rw [show jumpsBefore (Ω := Ω) (k := k) S = fun γ =>
      Simplex.timesBefore S (cumulativeChart γ).2.1 by
    funext γ
    exact jumpsBefore_eq_timesBefore S γ]
  exact (Simplex.measurable_timesBefore S k).comp
    (measurable_fst.comp (measurable_snd.comp measurable_cumulativeChart))

def jumpsBeforeSet (S : NNReal) (k n : ℕ) : Set (JumpPath Ω k) :=
  {γ | jumpsBefore S γ = n}

theorem measurableSet_jumpsBeforeSet (S : NNReal) (k n : ℕ) :
    MeasurableSet (jumpsBeforeSet (Ω := Ω) S k n) :=
  ((measurable_jumpsBefore (Ω := Ω) S k).eq_const n).setOf

end JumpPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The fixed-jump-count continuation law, packaged as a kernel in its
prescribed initial state. -/
noncomputable def sectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    Kernel Ω (JumpPath Ω n) :=
  Kernel.ofFunOfCountable fun x => G.sectorLawFrom T x n

@[simp]
theorem sectorKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) (x : Ω) :
    G.sectorKernel T n x = G.sectorLawFrom T x n :=
  rfl

noncomputable instance instIsFiniteKernelSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    IsFiniteKernel (G.sectorKernel T n) := by
  refine ⟨1, ENNReal.one_lt_top, fun x => ?_⟩
  rw [G.sectorKernel_apply, G.sectorLawFrom_univ]
  calc
    G.sectorMassFrom T x n ≤ ∑' k, G.sectorMassFrom T x k :=
      ENNReal.le_tsum n
    _ = 1 := G.tsum_sectorMassFrom T x

/-- A fixed-sector suffix started at the terminal state of its prefix. -/
noncomputable def continuationSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n m : ℕ) :
    Kernel (JumpPath Ω n) (JumpPath Ω m) :=
  (G.sectorKernel T m).comap
    (fun γ => γ.1 (Fin.last n))
    ((measurable_pi_apply (Fin.last n)).comp measurable_fst)

@[simp]
theorem continuationSectorKernel_apply
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n m : ℕ)
    (γ : JumpPath Ω n) :
    G.continuationSectorKernel T n m γ =
      G.sectorLawFrom T (γ.1 (Fin.last n)) m :=
  rfl

noncomputable instance instIsFiniteKernelContinuationSectorKernel
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n m : ℕ) :
    IsFiniteKernel (G.continuationSectorKernel T n m) := by
  unfold continuationSectorKernel
  infer_instance

omit [DecidableEq Ω] in
/-- **Seam counting transport.**  Product counting measure restricted to
matched boundary states maps to counting measure on global state sequences. -/
theorem map_prod_stateSequenceCountingReference_restrict_seamJoinStates
    (G : FiniteJumpGenerator Ω) (n m : ℕ) :
    (((G.stateSequenceCountingReference n).prod
      (G.stateSequenceCountingReference m)).restrict
        {p | p.1 (Fin.last n) = p.2 0}).map
          (fun p => JumpPath.seamJoinStates p.1 p.2) =
      G.stateSequenceCountingReference (n + m) := by
  refine Measure.ext_of_singleton fun c => ?_
  have hjoin : Measurable (fun p : (Fin (n + 1) → Ω) ×
      (Fin (m + 1) → Ω) => JumpPath.seamJoinStates p.1 p.2) :=
    Measurable.of_discrete
  rw [Measure.map_apply hjoin (measurableSet_singleton c)]
  rw [Measure.restrict_apply (hjoin (measurableSet_singleton c))]
  let q := (JumpPath.seamStateEquiv (Ω := Ω) n m).symm c
  have hset :
      (fun p : (Fin (n + 1) → Ω) × (Fin (m + 1) → Ω) =>
          JumpPath.seamJoinStates p.1 p.2) ⁻¹' {c} ∩
          {p | p.1 (Fin.last n) = p.2 0} = {q.1} := by
    ext p
    constructor
    · rintro ⟨hpjoin, hpseam⟩
      have hpjoin' : JumpPath.seamJoinStates p.1 p.2 = c := hpjoin
      have hp : (⟨p, hpseam⟩ : JumpPath.seamStatePairs (Ω := Ω) n m) = q := by
        apply (JumpPath.seamStateEquiv (Ω := Ω) n m).injective
        change JumpPath.seamJoinStates p.1 p.2 =
          JumpPath.seamJoinStates q.1.1 q.1.2
        exact hpjoin'.trans
          ((JumpPath.seamStateEquiv (Ω := Ω) n m).apply_symm_apply c).symm
      simpa using congrArg Subtype.val hp
    · intro hp
      have hpq : p = q.1 := hp
      subst p
      constructor
      · change (JumpPath.seamStateEquiv (Ω := Ω) n m) q = c
        exact (JumpPath.seamStateEquiv (Ω := Ω) n m).apply_symm_apply c
      · exact q.2
  rw [hset]
  change ((Measure.count : Measure (Fin (n + 1) → Ω)).prod
      (Measure.count : Measure (Fin (m + 1) → Ω))) {q.1} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [stateSequenceCountingReference]

omit [DecidableEq Ω] in
/-- **Joint raw-reference transport.**  After restricting to matching seam
states, the two state/simplex references map through the cumulative-time
joining square to the global counting reference over the cut simplex. -/
theorem map_jointChartReference_restrict_seam_jointCumulativeJoin
    (G : FiniteJumpGenerator Ω) (S T : NNReal)
    (hS : 0 < S) (hT : 0 < T) (n m : ℕ) :
    let μn := (G.stateSequenceCountingReference n).prod
      ((S : ℝ≥0∞) ^ n • (volume : Measure (Fin n → I)).restrict
        (Simplex.freeSimplexSet n))
    let μm := (G.stateSequenceCountingReference m).prod
      ((T : ℝ≥0∞) ^ m • (volume : Measure (Fin m → I)).restrict
        (Simplex.freeSimplexSet m))
    ((μn.prod μm).restrict
        {p | p.1.1 (Fin.last n) = p.2.1 0}).map
          (JumpPath.jointCumulativeJoin S T n m) =
      ((G.stateSequenceCountingReference (n + m)).prod
        ((volume : Measure (Fin (n + m) → ℝ)).restrict
          (Simplex.cutOrderedSimplexSet S T n m))).map
        (fun p => (p.1, (p.2, S + T))) := by
  dsimp only
  let cn := G.stateSequenceCountingReference n
  let cm := G.stateSequenceCountingReference m
  let tn := (S : ℝ≥0∞) ^ n •
    (volume : Measure (Fin n → I)).restrict (Simplex.freeSimplexSet n)
  let tm := (T : ℝ≥0∞) ^ m •
    (volume : Measure (Fin m → I)).restrict (Simplex.freeSimplexSet m)
  let shuffle := fun p : ((Fin (n + 1) → Ω) × (Fin n → I)) ×
      ((Fin (m + 1) → Ω) × (Fin m → I)) =>
    ((p.1.1, p.2.1), (p.1.2, p.2.2))
  let seam : Set ((Fin (n + 1) → Ω) × (Fin (m + 1) → Ω)) :=
    {p | p.1 (Fin.last n) = p.2 0}
  let timeJoin := fun p : (Fin n → I) × (Fin m → I) =>
    Simplex.joinTimesEquiv S n m
      (Simplex.physicalCumulativeTimes S n p.1,
        Simplex.physicalCumulativeTimes T m p.2)
  let stateJoin := fun p : (Fin (n + 1) → Ω) × (Fin (m + 1) → Ω) =>
    JumpPath.seamJoinStates p.1 p.2
  have hseam : MeasurableSet seam := by
    dsimp [seam]
    exact (((measurable_pi_apply (Fin.last n)).comp measurable_fst).eq
      ((measurable_pi_apply 0).comp measurable_snd)).setOf
  have hshuffle : MeasurePreserving shuffle
      ((cn.prod tn).prod (cm.prod tm))
      ((cn.prod cm).prod (tn.prod tm)) := by
    exact measurePreserving_prod_shuffle cn cm tn tm
  have hrestrict :
      (((cn.prod tn).prod (cm.prod tm)).restrict
        {p | p.1.1 (Fin.last n) = p.2.1 0}).map shuffle =
        ((cn.prod cm).restrict seam).prod (tn.prod tm) := by
    have hpre : shuffle ⁻¹' (seam ×ˢ Set.univ) =
        {p | p.1.1 (Fin.last n) = p.2.1 0} := by
      ext p
      simp [shuffle, seam]
    calc
      _ = (((cn.prod tn).prod (cm.prod tm)).restrict
          (shuffle ⁻¹' (seam ×ˢ Set.univ))).map shuffle := by rw [hpre]
      _ = (((cn.prod tn).prod (cm.prod tm)).map shuffle).restrict
          (seam ×ˢ Set.univ) :=
        (Measure.restrict_map hshuffle.measurable
          (hseam.prod MeasurableSet.univ)).symm
      _ = (((cn.prod cm).prod (tn.prod tm)).restrict
          (seam ×ˢ Set.univ)) := by rw [hshuffle.map_eq]
      _ = _ := by
        rw [← Measure.prod_restrict]
        simp only [Measure.restrict_univ]
  have hstate : ((cn.prod cm).restrict seam).map stateJoin =
      G.stateSequenceCountingReference (n + m) := by
    exact G.map_prod_stateSequenceCountingReference_restrict_seamJoinStates n m
  have htime : (tn.prod tm).map timeJoin =
      (volume : Measure (Fin (n + m) → ℝ)).restrict
        (Simplex.cutOrderedSimplexSet S T n m) := by
    exact Simplex.map_prod_scaledFreeSimplex_joinPhysicalCumulativeTimes
      S T hS hT n m
  have hstateJoin : Measurable stateJoin := by
    exact JumpPath.measurable_seamJoinStates n m
  have htimeJoin : Measurable timeJoin := by
    exact (Simplex.joinTimesEquiv S n m).measurable.comp
      ((JumpPath.measurable_physicalCumulativeTimes S n).comp measurable_fst |>.prodMk
        ((JumpPath.measurable_physicalCumulativeTimes T m).comp measurable_snd))
  calc
    _ = ((((cn.prod tn).prod (cm.prod tm)).restrict
          {p | p.1.1 (Fin.last n) = p.2.1 0}).map shuffle).map
        (fun p => (stateJoin p.1, (timeJoin p.2, S + T))) := by
      rw [Measure.map_map]
      · rfl
      · exact hstateJoin.comp measurable_fst |>.prodMk
          ((htimeJoin.comp measurable_snd).prodMk measurable_const)
      · exact hshuffle.measurable
    _ = (((cn.prod cm).restrict seam).prod (tn.prod tm)).map
        (fun p => (stateJoin p.1, (timeJoin p.2, S + T))) := by
      rw [hrestrict]
    _ = ((((cn.prod cm).restrict seam).map stateJoin).prod
          ((tn.prod tm).map timeJoin)).map
        (fun p => (p.1, (p.2, S + T))) := by
      rw [Measure.map_prod_map _ _ hstateJoin htimeJoin]
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · exact hstateJoin.prodMap htimeJoin
    _ = _ := by rw [hstate, htime]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The two chart densities multiply to the global concatenated density on the
seam and vanish away from the seam. -/
theorem rateDensity_mul_continuation_eq_seamIndicator
    (G : FiniteJumpGenerator Ω) {n m : ℕ}
    (γ : JumpPath Ω n) (δ : JumpPath Ω m) (x : Ω) :
    JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate γ *
        JumpPath.rateDensity (fixedInitialWeight (γ.1 (Fin.last n)))
          G.pathEscapeRate G.pathJumpRate δ =
      if γ.1 (Fin.last n) = δ.1 0 then
        JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate (JumpPath.concat γ δ)
      else 0 := by
  by_cases hmatch : γ.1 (Fin.last n) = δ.1 0
  · rw [if_pos hmatch]
    rw [hmatch]
    exact (G.rateDensity_concat γ δ x hmatch).symm
  · rw [if_neg hmatch]
    have hsuffix :
        JumpPath.rateDensity (fixedInitialWeight (γ.1 (Fin.last n)))
          G.pathEscapeRate G.pathJumpRate δ = 0 := by
      unfold JumpPath.rateDensity JumpPath.density fixedInitialWeight
      simp [Ne.symm hmatch]
    rw [hsuffix, mul_zero]

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

/-- Concatenation of a prefix sector with its terminal-state continuation can
be computed entirely over the two explicit state/simplex charts. -/
theorem map_concat_compProd_sectorLaw_eq_jointChart
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) (n m : ℕ) :
    (G.sectorLawFrom S x n ⊗ₘ G.continuationSectorKernel T n m).map
        (fun p => JumpPath.concat p.1 p.2) =
      let μn := (G.stateSequenceCountingReference n).prod
        ((S : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))
      let μm := (G.stateSequenceCountingReference m).prod
        ((T : ℝ≥0∞) ^ m •
          (volume : Measure (Fin m → I)).restrict
            (Simplex.freeSimplexSet m))
      let μprefix := μn.withDensity (fun p =>
        JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath S p))
      let suffix : Kernel
          ((Fin (n + 1) → Ω) × (Fin n → I))
          ((Fin (m + 1) → Ω) × (Fin m → I)) :=
        (Kernel.const _ μm).withDensity (fun p q =>
          JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
            G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q))
      (μprefix ⊗ₘ suffix).map (fun p =>
        JumpPath.concat (Simplex.assemblePath S p.1)
          (Simplex.assemblePath T p.2)) := by
  dsimp only
  let μn := (G.stateSequenceCountingReference n).prod
    ((S : ℝ≥0∞) ^ n •
      (volume : Measure (Fin n → I)).restrict (Simplex.freeSimplexSet n))
  let μm := (G.stateSequenceCountingReference m).prod
    ((T : ℝ≥0∞) ^ m •
      (volume : Measure (Fin m → I)).restrict (Simplex.freeSimplexSet m))
  let μprefix := μn.withDensity (fun p =>
    JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath S p))
  let suffix : Kernel
      ((Fin (n + 1) → Ω) × (Fin n → I))
      ((Fin (m + 1) → Ω) × (Fin m → I)) :=
    (Kernel.const _ μm).withDensity (fun p q =>
      JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
        G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q))
  letI : IsFiniteMeasure ((T : ℝ≥0∞) ^ m •
      (volume : Measure (Fin m → I)).restrict
        (Simplex.freeSimplexSet m)) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ,
      Simplex.volume_freeSimplexSet]
    rw [smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (G.stateSequenceCountingReference m) := by
    unfold stateSequenceCountingReference
    infer_instance
  letI : IsFiniteMeasure μm := by
    dsimp [μm]
    infer_instance
  letI : IsSFiniteKernel suffix := by
    dsimp [suffix]
    apply Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    intro p q
    apply JumpPath.rateDensity_ne_top
    intro y
    unfold fixedInitialWeight
    split <;> simp
  have hprefix : G.sectorLawFrom S x n =
      μprefix.map (Simplex.assemblePath S) := by
    exact G.sectorLawFrom_eq_chart S x n
  have hsuffix :
      (G.continuationSectorKernel T n m).comap
          (Simplex.assemblePath S) (Simplex.measurable_assemblePath S) =
        suffix.map (Simplex.assemblePath T) := by
    apply Kernel.ext
    intro p
    change G.sectorLawFrom T (p.1 (Fin.last n)) m = _
    rw [G.sectorLawFrom_eq_chart]
    rw [Kernel.map_apply suffix (Simplex.measurable_assemblePath T)]
    have hg : Measurable (Function.uncurry fun
        (p : (Fin (n + 1) → Ω) × (Fin n → I))
        (q : (Fin (m + 1) → Ω) × (Fin m → I)) =>
        JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
          G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q)) := by
      unfold JumpPath.rateDensity JumpPath.density
        JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
        fixedInitialWeight FiniteJumpGenerator.pathEscapeRate
        FiniteJumpGenerator.pathJumpRate
      apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.ite
          · exact ((by fun_prop : Measurable fun
                (z : ((Fin (n + 1) → Ω) × (Fin n → I)) ×
                  ((Fin (m + 1) → Ω) × (Fin m → I))) =>
                (Simplex.assemblePath T z.2).1 0).eq
              (by fun_prop : Measurable fun
                (z : ((Fin (n + 1) → Ω) × (Fin n → I)) ×
                  ((Fin (m + 1) → Ω) × (Fin m → I))) =>
                z.1.1 (Fin.last n))).setOf
          · exact measurable_const
          · exact measurable_const
        · fun_prop
      · fun_prop
    rw [show suffix p = μm.withDensity (fun q =>
        JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
          G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q)) by
      dsimp [suffix]
      rw [Kernel.withDensity_apply _ hg, Kernel.const_apply]]
  rw [hprefix]
  rw [map_compProd_eq_map_compProd_comap μprefix
    (G.continuationSectorKernel T n m)
    (Simplex.assemblePath S) (Simplex.measurable_assemblePath S)]
  rw [hsuffix]
  rw [Measure.compProd_map (Simplex.measurable_assemblePath T)]
  rw [Measure.map_map JumpPath.measurable_concat_prod
    ((Simplex.measurable_assemblePath S).prodMap measurable_id)]
  rw [Measure.map_map
    (JumpPath.measurable_concat_prod.comp
      ((Simplex.measurable_assemblePath S).prodMap measurable_id))
    (measurable_id.prodMap (Simplex.measurable_assemblePath T))]
  congr 1

/-- The joint prefix/suffix chart is a single density over the product of its
two raw state/simplex reference measures. -/
theorem jointChart_compProd_eq_withDensity
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (x : Ω) (n m : ℕ) :
    let μn := (G.stateSequenceCountingReference n).prod
      ((S : ℝ≥0∞) ^ n • (volume : Measure (Fin n → I)).restrict
        (Simplex.freeSimplexSet n))
    let μm := (G.stateSequenceCountingReference m).prod
      ((T : ℝ≥0∞) ^ m • (volume : Measure (Fin m → I)).restrict
        (Simplex.freeSimplexSet m))
    let f := fun p => JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath S p)
    let g := fun p q =>
      JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
        G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q)
    μn.withDensity f ⊗ₘ (Kernel.const _ μm).withDensity g =
      (μn.prod μm).withDensity (fun p => f p.1 * g p.1 p.2) := by
  dsimp only
  let μn := (G.stateSequenceCountingReference n).prod
    ((S : ℝ≥0∞) ^ n • (volume : Measure (Fin n → I)).restrict
      (Simplex.freeSimplexSet n))
  let μm := (G.stateSequenceCountingReference m).prod
    ((T : ℝ≥0∞) ^ m • (volume : Measure (Fin m → I)).restrict
      (Simplex.freeSimplexSet m))
  let f : ((Fin (n + 1) → Ω) × (Fin n → I)) → ℝ≥0∞ := fun p =>
    JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath S p)
  let g : ((Fin (n + 1) → Ω) × (Fin n → I)) →
      ((Fin (m + 1) → Ω) × (Fin m → I)) → ℝ≥0∞ := fun p q =>
    JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q)
  have hf : Measurable f := by
    exact (G.measurable_rateDensity (fixedInitialWeight x) n).comp
      (Simplex.measurable_assemblePath S)
  have hg : Measurable (Function.uncurry g) := by
    unfold g JumpPath.rateDensity JumpPath.density
      JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
      fixedInitialWeight FiniteJumpGenerator.pathEscapeRate
      FiniteJumpGenerator.pathJumpRate
    apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.ite
        · exact ((by fun_prop : Measurable fun
              (z : ((Fin (n + 1) → Ω) × (Fin n → I)) ×
                ((Fin (m + 1) → Ω) × (Fin m → I))) =>
              (Simplex.assemblePath T z.2).1 0).eq
            (by fun_prop : Measurable fun
              (z : ((Fin (n + 1) → Ω) × (Fin n → I)) ×
                ((Fin (m + 1) → Ω) × (Fin m → I))) =>
              z.1.1 (Fin.last n))).setOf
        · exact measurable_const
        · exact measurable_const
      · fun_prop
    · fun_prop
  letI : IsFiniteMeasure ((S : ℝ≥0∞) ^ n •
      (volume : Measure (Fin n → I)).restrict
        (Simplex.freeSimplexSet n)) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ,
      Simplex.volume_freeSimplexSet]
    rw [smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure ((T : ℝ≥0∞) ^ m •
      (volume : Measure (Fin m → I)).restrict
        (Simplex.freeSimplexSet m)) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ,
      Simplex.volume_freeSimplexSet]
    rw [smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (G.stateSequenceCountingReference n) := by
    unfold stateSequenceCountingReference
    infer_instance
  letI : IsFiniteMeasure (G.stateSequenceCountingReference m) := by
    unfold stateSequenceCountingReference
    infer_instance
  letI : IsFiniteMeasure μn := by dsimp [μn]; infer_instance
  letI : IsFiniteMeasure μm := by dsimp [μm]; infer_instance
  letI : IsSFiniteKernel ((Kernel.const _ μm).withDensity g) := by
    apply Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    intro p q
    apply JumpPath.rateDensity_ne_top
    intro y
    unfold fixedInitialWeight
    split <;> simp
  exact withDensity_compProd_const_withDensity μn μm f g hf hg

/-- The rate density expressed on the injective cumulative-time path chart. -/
noncomputable def cumulativeChartDensity
    (G : FiniteJumpGenerator Ω) (x : Ω) (n : ℕ) :
    ((Fin (n + 1) → Ω) × ((Fin n → ℝ) × NNReal)) → ℝ≥0∞ := fun z =>
  letI : Nonempty Ω := ⟨x⟩
  JumpPath.rateDensity (fixedInitialWeight x)
    (G.pathEscapeRate (n := n)) (G.pathJumpRate (n := n))
    ((JumpPath.cumulativeChart_measurableEmbedding
      (Ω := Ω) (n := n)).invFun z)

theorem measurable_cumulativeChartDensity
    (G : FiniteJumpGenerator Ω) (x : Ω) (n : ℕ) :
    Measurable (G.cumulativeChartDensity x n) := by
  letI : Nonempty Ω := ⟨x⟩
  exact (G.measurable_rateDensity (fixedInitialWeight x) n).comp
    (JumpPath.cumulativeChart_measurableEmbedding
      (Ω := Ω) (n := n)).measurable_invFun

@[simp]
theorem cumulativeChartDensity_cumulativeChart
    (G : FiniteJumpGenerator Ω) (x : Ω) {n : ℕ} (γ : JumpPath Ω n) :
    G.cumulativeChartDensity x n (JumpPath.cumulativeChart γ) =
      JumpPath.rateDensity (fixedInitialWeight x)
        (G.pathEscapeRate (n := n)) (G.pathJumpRate (n := n)) γ := by
  letI : Nonempty Ω := ⟨x⟩
  unfold cumulativeChartDensity
  rw [(JumpPath.cumulativeChart_measurableEmbedding
    (Ω := Ω) (n := n)).leftInverse_invFun γ]

/-- The continuation-sector concatenation in cumulative-chart normal form.
Both sides have now been reduced to the same seam-counting and cut-simplex
reference measure, with the global rate density applied afterward. -/
theorem map_cumulativeChart_concat_compProd_sectorLaw
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (hS : 0 < S) (hT : 0 < T)
    (x : Ω) (n m : ℕ) :
    ((G.sectorLawFrom S x n ⊗ₘ G.continuationSectorKernel T n m).map
      (fun p => JumpPath.concat p.1 p.2)).map JumpPath.cumulativeChart =
      (((G.stateSequenceCountingReference (n + m)).prod
        ((volume : Measure (Fin (n + m) → ℝ)).restrict
          (Simplex.cutOrderedSimplexSet S T n m))).map
            (fun p => (p.1, (p.2, S + T)))).withDensity
        (G.cumulativeChartDensity x (n + m)) := by
  let cn := G.stateSequenceCountingReference n
  let cm := G.stateSequenceCountingReference m
  let tn := (S : ℝ≥0∞) ^ n •
    (volume : Measure (Fin n → I)).restrict (Simplex.freeSimplexSet n)
  let tm := (T : ℝ≥0∞) ^ m •
    (volume : Measure (Fin m → I)).restrict (Simplex.freeSimplexSet m)
  let μn := cn.prod tn
  let μm := cm.prod tm
  let base := μn.prod μm
  let seam : Set (((Fin (n + 1) → Ω) × (Fin n → I)) ×
      ((Fin (m + 1) → Ω) × (Fin m → I))) :=
    {p | p.1.1 (Fin.last n) = p.2.1 0}
  let join := JumpPath.jointCumulativeJoin (Ω := Ω) S T n m
  let concatChart := fun p : ((Fin (n + 1) → Ω) × (Fin n → I)) ×
      ((Fin (m + 1) → Ω) × (Fin m → I)) =>
    JumpPath.concat (Simplex.assemblePath S p.1)
      (Simplex.assemblePath T p.2)
  let f := fun p : (Fin (n + 1) → Ω) × (Fin n → I) =>
    JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath S p)
  let g := fun (p : (Fin (n + 1) → Ω) × (Fin n → I))
      (q : (Fin (m + 1) → Ω) × (Fin m → I)) =>
    JumpPath.rateDensity (fixedInitialWeight (p.1 (Fin.last n)))
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath T q)
  let q := G.cumulativeChartDensity x (n + m)
  have htn : ∀ᵐ u ∂tn, u ∈ Simplex.freeSimplexSet n := by
    exact Measure.ae_smul_measure
      (ae_restrict_mem (Simplex.measurableSet_freeSimplexSet n)) _
  have htm : ∀ᵐ v ∂tm, v ∈ Simplex.freeSimplexSet m := by
    exact Measure.ae_smul_measure
      (ae_restrict_mem (Simplex.measurableSet_freeSimplexSet m)) _
  have hμn : ∀ᵐ p ∂μn, p.2 ∈ Simplex.freeSimplexSet n := by
    apply (Measure.ae_prod_iff_ae_ae
      ((Simplex.measurableSet_freeSimplexSet n).preimage measurable_snd)).2
    exact ae_of_all _ fun _ => htn
  have hμm : ∀ᵐ p ∂μm, p.2 ∈ Simplex.freeSimplexSet m := by
    apply (Measure.ae_prod_iff_ae_ae
      ((Simplex.measurableSet_freeSimplexSet m).preimage measurable_snd)).2
    exact ae_of_all _ fun _ => htm
  have hsupport : ∀ᵐ p ∂base,
      p.1.2 ∈ Simplex.freeSimplexSet n ∧
        p.2.2 ∈ Simplex.freeSimplexSet m := by
    apply (Measure.ae_prod_iff_ae_ae
      (((Simplex.measurableSet_freeSimplexSet n).preimage
        (measurable_snd.comp measurable_fst)).inter
       ((Simplex.measurableSet_freeSimplexSet m).preimage
        (measurable_snd.comp measurable_snd)))).2
    filter_upwards [hμn] with p hp
    filter_upwards [hμm] with r hr
    exact ⟨hp, hr⟩
  have hmap : (fun p => JumpPath.cumulativeChart (concatChart p)) =ᵐ[base] join := by
    filter_upwards [hsupport] with p hp
    exact JumpPath.cumulativeChart_concat_assemblePath S T
      p.1.1 p.2.1 p.1.2 p.2.2 hp.1 hp.2
  have hdensity : (fun p => f p.1 * g p.1 p.2) =ᵐ[base]
      seam.indicator (q ∘ join) := by
    filter_upwards [hsupport] with p hp
    dsimp [f, g]
    simp only [Simplex.assemblePath]
    have hrate := G.rateDensity_mul_continuation_eq_seamIndicator
      (Simplex.assemblePath S p.1) (Simplex.assemblePath T p.2) x
    simp only [Simplex.assemblePath] at hrate
    rw [hrate]
    by_cases hseam : p ∈ seam
    · have hmatch : p.1.1 (Fin.last n) = p.2.1 0 := by
        simpa [seam] using hseam
      rw [Set.indicator_of_mem hseam]
      rw [if_pos hmatch]
      change _ = q (join p)
      have hsquare : JumpPath.cumulativeChart (concatChart p) = join p := by
        dsimp [concatChart, join]
        exact JumpPath.cumulativeChart_concat_assemblePath S T
          p.1.1 p.2.1 p.1.2 p.2.2 hp.1 hp.2
      rw [← hsquare]
      change JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate (concatChart p) =
        q (JumpPath.cumulativeChart (concatChart p))
      exact (G.cumulativeChartDensity_cumulativeChart x (concatChart p)).symm
    · have hseam' : p.1.1 (Fin.last n) ≠ p.2.1 0 := by
        simpa [seam] using hseam
      rw [Set.indicator_of_notMem hseam]
      rw [if_neg hseam']
  have hseamMeas : MeasurableSet seam := by
    dsimp [seam]
    exact ((((measurable_pi_apply (Fin.last n)).comp measurable_fst).comp
      measurable_fst).eq
      (((measurable_pi_apply 0).comp measurable_fst).comp measurable_snd)).setOf
  have hjoin : Measurable join :=
    JumpPath.measurable_jointCumulativeJoin S T n m
  have hq : Measurable q := G.measurable_cumulativeChartDensity x (n + m)
  have hconcatChart : Measurable concatChart := by
    dsimp [concatChart]
    exact JumpPath.measurable_concat_prod.comp
      ((Simplex.measurable_assemblePath S).prodMap
        (Simplex.measurable_assemblePath T))
  rw [G.map_concat_compProd_sectorLaw_eq_jointChart S T x n m]
  dsimp only
  rw [G.jointChart_compProd_eq_withDensity S T x n m]
  change ((base.withDensity (fun p => f p.1 * g p.1 p.2)).map concatChart).map
      JumpPath.cumulativeChart = _
  rw [Measure.map_map JumpPath.measurable_cumulativeChart hconcatChart]
  have hmap' : (JumpPath.cumulativeChart ∘ concatChart) =ᵐ[base] join := by
    simpa [Function.comp_def] using hmap
  rw [Measure.map_congr ((withDensity_absolutelyContinuous base _).ae_le hmap')]
  rw [withDensity_congr_ae hdensity]
  rw [withDensity_indicator hseamMeas]
  rw [← CrooksJarzynski.MeasureProtocol.map_withDensity
    (base.restrict seam) join q hjoin hq]
  rw [G.map_jointChartReference_restrict_seam_jointCumulativeJoin S T hS hT n m]

/-- A global fixed sector in cumulative-chart normal form. -/
theorem map_cumulativeChart_sectorLawFrom
    (G : FiniteJumpGenerator Ω) (H : NNReal) (hH : 0 < H)
    (x : Ω) (k : ℕ) :
    (G.sectorLawFrom H x k).map JumpPath.cumulativeChart =
      (((G.stateSequenceCountingReference k).prod
        ((volume : Measure (Fin k → ℝ)).restrict
          (Simplex.orderedSimplexSet H k))).map
            (fun p => (p.1, (p.2, H)))).withDensity
        (G.cumulativeChartDensity x k) := by
  let c := G.stateSequenceCountingReference k
  let t := (H : ℝ≥0∞) ^ k •
    (volume : Measure (Fin k → I)).restrict (Simplex.freeSimplexSet k)
  let base := c.prod t
  let chart := fun p : (Fin (k + 1) → Ω) × (Fin k → I) =>
    (p.1, (Simplex.physicalCumulativeTimes H k p.2, H))
  let q := G.cumulativeChartDensity x k
  let f := fun p : (Fin (k + 1) → Ω) × (Fin k → I) =>
    JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath H p)
  have ht : ∀ᵐ u ∂t, u ∈ Simplex.freeSimplexSet k := by
    exact Measure.ae_smul_measure
      (ae_restrict_mem (Simplex.measurableSet_freeSimplexSet k)) _
  have hsupport : ∀ᵐ p ∂base, p.2 ∈ Simplex.freeSimplexSet k := by
    apply (Measure.ae_prod_iff_ae_ae
      ((Simplex.measurableSet_freeSimplexSet k).preimage measurable_snd)).2
    exact ae_of_all _ fun _ => ht
  have hchart : (fun p => JumpPath.cumulativeChart
      (Simplex.assemblePath H p)) =ᵐ[base] chart := by
    filter_upwards [hsupport] with p hp
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        exact Simplex.jumpTimes_assemblePath H p.1 p.2 i
      · exact Simplex.sum_holdingTimesOfFree H p.2 hp
  have hdensity : f =ᵐ[base] q ∘ chart := by
    filter_upwards [hsupport] with p hp
    have hc : JumpPath.cumulativeChart (Simplex.assemblePath H p) = chart p := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext i
          exact Simplex.jumpTimes_assemblePath H p.1 p.2 i
        · exact Simplex.sum_holdingTimesOfFree H p.2 hp
    change f p = q (chart p)
    rw [← hc]
    change JumpPath.rateDensity (fixedInitialWeight x)
        G.pathEscapeRate G.pathJumpRate (Simplex.assemblePath H p) =
      q (JumpPath.cumulativeChart (Simplex.assemblePath H p))
    exact (G.cumulativeChartDensity_cumulativeChart x
      (Simplex.assemblePath H p)).symm
  have hchartMeas : Measurable chart := by
    dsimp [chart]
    exact measurable_fst.prodMk
      ((JumpPath.measurable_physicalCumulativeTimes H k).comp measurable_snd |>.prodMk
        measurable_const)
  have hq : Measurable q := G.measurable_cumulativeChartDensity x k
  rw [G.sectorLawFrom_eq_chart H x k]
  rw [Measure.map_map JumpPath.measurable_cumulativeChart
    (Simplex.measurable_assemblePath H)]
  change (base.withDensity f).map
      (JumpPath.cumulativeChart ∘ Simplex.assemblePath H) = _
  have hchart' : (JumpPath.cumulativeChart ∘ Simplex.assemblePath H) =ᵐ[base]
      chart := by simpa [Function.comp_def] using hchart
  rw [Measure.map_congr ((withDensity_absolutelyContinuous base _).ae_le hchart')]
  rw [withDensity_congr_ae hdensity]
  rw [← CrooksJarzynski.MeasureProtocol.map_withDensity base chart q hchartMeas hq]
  congr 1
  have htime := Simplex.map_scaledFreeSimplex_cumulativeTimes H hH k
  calc
    base.map chart =
        ((c.map id).prod (t.map (Simplex.physicalCumulativeTimes H k))).map
          (fun p => (p.1, (p.2, H))) := by
      rw [Measure.map_prod_map c t measurable_id
        (JumpPath.measurable_physicalCumulativeTimes H k)]
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · exact measurable_id.prodMap
          (JumpPath.measurable_physicalCumulativeTimes H k)
    _ = _ := by rw [Measure.map_id, htime]

/-- **Fixed `(n,m)` sector convolution.**  Restricting the global sector to
the cumulative-time chart cut after `n` jumps gives concatenation of the
prefix sector with its terminal-state continuation sector. -/
theorem sectorLawFrom_restrict_cutSectorSet
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (hS : 0 < S) (hT : 0 < T)
    (x : Ω) (n m : ℕ) :
    (G.sectorLawFrom (S + T) x (n + m)).restrict
        (JumpPath.cutSectorSet S T n m) =
      (G.sectorLawFrom S x n ⊗ₘ
        G.continuationSectorKernel T n m).map
          (fun p => JumpPath.concat p.1 p.2) := by
  let cut := Simplex.cutOrderedSimplexSet S T n m
  let chartCut : Set ((Fin (n + m + 1) → Ω) ×
      ((Fin (n + m) → ℝ) × NNReal)) := {z | z.2.1 ∈ cut}
  let raw := (G.stateSequenceCountingReference (n + m)).prod
    ((volume : Measure (Fin (n + m) → ℝ)).restrict
      (Simplex.orderedSimplexSet (S + T) (n + m)))
  let attach := fun p : (Fin (n + m + 1) → Ω) × (Fin (n + m) → ℝ) =>
    (p.1, (p.2, S + T))
  let q := G.cumulativeChartDensity x (n + m)
  have hH : 0 < S + T := add_pos hS hT
  have hchartCut : MeasurableSet chartCut := by
    exact (Simplex.measurableSet_cutOrderedSimplexSet S T n m).preimage
      (measurable_fst.comp measurable_snd)
  have hattach : Measurable attach := by fun_prop
  have hpre : attach ⁻¹' chartCut = Set.univ ×ˢ cut := by
    ext p
    simp [attach, chartCut]
  have hrawRestrict : raw.restrict (Set.univ ×ˢ cut) =
      (G.stateSequenceCountingReference (n + m)).prod
        ((volume : Measure (Fin (n + m) → ℝ)).restrict cut) := by
    dsimp [raw]
    rw [← Measure.prod_restrict]
    rw [Measure.restrict_univ]
    rw [Measure.restrict_restrict_of_subset
      (Simplex.cutOrderedSimplexSet_subset_orderedSimplexSet_add S T n m)]
  have hcutpre : JumpPath.cutSectorSet (Ω := Ω) S T n m =
      JumpPath.cumulativeChart ⁻¹' chartCut := by
    ext γ
    rfl
  apply (JumpPath.cumulativeChart_measurableEmbedding
    (Ω := Ω) (n := n + m)).map_injective
  rw [hcutpre]
  rw [← Measure.restrict_map JumpPath.measurable_cumulativeChart hchartCut]
  rw [G.map_cumulativeChart_sectorLawFrom (S + T) hH x (n + m)]
  rw [MeasureTheory.restrict_withDensity hchartCut]
  rw [Measure.restrict_map hattach hchartCut]
  rw [hpre]
  change ((raw.restrict (Set.univ ×ˢ cut)).map attach).withDensity q = _
  rw [hrawRestrict]
  rw [G.map_cumulativeChart_concat_compProd_sectorLaw S T hS hT x n m]

/-- **Sector convolution on the canonical disjoint cut event.**  The event is
expressed by the number of jumps strictly before `S`; the difference from the
closed cut simplex is exactly the null seam hyperplane. -/
theorem sectorLawFrom_restrict_jumpsBeforeSet
    (G : FiniteJumpGenerator Ω) (S T : NNReal) (hS : 0 < S) (hT : 0 < T)
    (x : Ω) (n m : ℕ) :
    (G.sectorLawFrom (S + T) x (n + m)).restrict
        (JumpPath.jumpsBeforeSet S (n + m) n) =
      (G.sectorLawFrom S x n ⊗ₘ
        G.continuationSectorKernel T n m).map
          (fun p => JumpPath.concat p.1 p.2) := by
  let count : Set (Fin (n + m) → ℝ) :=
    {τ | Simplex.timesBefore S τ = n}
  let chartCount : Set ((Fin (n + m + 1) → Ω) ×
      ((Fin (n + m) → ℝ) × NNReal)) := {z | z.2.1 ∈ count}
  let raw := (G.stateSequenceCountingReference (n + m)).prod
    ((volume : Measure (Fin (n + m) → ℝ)).restrict
      (Simplex.orderedSimplexSet (S + T) (n + m)))
  let attach := fun p : (Fin (n + m + 1) → Ω) × (Fin (n + m) → ℝ) =>
    (p.1, (p.2, S + T))
  let q := G.cumulativeChartDensity x (n + m)
  have hH : 0 < S + T := add_pos hS hT
  have hcount : MeasurableSet count :=
    ((Simplex.measurable_timesBefore S (n + m)).eq_const n).setOf
  have hchartCount : MeasurableSet chartCount :=
    hcount.preimage (measurable_fst.comp measurable_snd)
  have hattach : Measurable attach := by fun_prop
  have hpre : attach ⁻¹' chartCount = Set.univ ×ˢ count := by
    ext p
    simp [attach, chartCount]
  have hrawRestrict : raw.restrict (Set.univ ×ˢ count) =
      (G.stateSequenceCountingReference (n + m)).prod
        ((volume : Measure (Fin (n + m) → ℝ)).restrict
          (Simplex.cutOrderedSimplexSet S T n m)) := by
    dsimp [raw]
    rw [← Measure.prod_restrict]
    rw [Measure.restrict_univ]
    rw [Measure.restrict_restrict hcount]
    rw [show count ∩ Simplex.orderedSimplexSet (S + T) (n + m) =
        Simplex.orderedCountSet S T n m by
      ext τ
      simp [count, Simplex.orderedCountSet, and_comm]]
    change (G.stateSequenceCountingReference (n + m)).prod
        ((volume : Measure (Fin (n + m) → ℝ)).restrict
          (Simplex.orderedCountSet S T n m)) = _
    rw [Simplex.volume_restrict_cutOrdered_eq_orderedCount]
  have hcountpre : JumpPath.jumpsBeforeSet (Ω := Ω) S (n + m) n =
      JumpPath.cumulativeChart ⁻¹' chartCount := by
    ext γ
    change JumpPath.jumpsBefore S γ = n ↔
      Simplex.timesBefore S (JumpPath.cumulativeChart γ).2.1 = n
    rw [JumpPath.jumpsBefore_eq_timesBefore]
  apply (JumpPath.cumulativeChart_measurableEmbedding
    (Ω := Ω) (n := n + m)).map_injective
  rw [hcountpre]
  rw [← Measure.restrict_map JumpPath.measurable_cumulativeChart hchartCount]
  rw [G.map_cumulativeChart_sectorLawFrom (S + T) hH x (n + m)]
  rw [MeasureTheory.restrict_withDensity hchartCount]
  rw [Measure.restrict_map hattach hchartCount]
  rw [hpre]
  change ((raw.restrict (Set.univ ×ˢ count)).map attach).withDensity q = _
  rw [hrawRestrict]
  rw [G.map_cumulativeChart_concat_compProd_sectorLaw S T hS hT x n m]

omit [MeasurableSingletonClass Ω] in
/-- The strictly-before cut events form a measurable disjoint partition of
every fixed jump-count sector. -/
theorem sectorLawFrom_eq_sum_restrict_jumpsBefore
    (G : FiniteJumpGenerator Ω) (H S : NNReal) (x : Ω) (k : ℕ) :
    G.sectorLawFrom H x k = Measure.sum fun r : Fin (k + 1) =>
      (G.sectorLawFrom H x k).restrict
        (JumpPath.jumpsBeforeSet S k r.val) := by
  let A := fun r : Fin (k + 1) =>
    JumpPath.jumpsBeforeSet (Ω := Ω) S k r.val
  have hdisjoint : Pairwise (Disjoint on A) := by
    intro i j hij
    change Disjoint (A i) (A j)
    rw [Set.disjoint_left]
    intro γ hi hj
    change JumpPath.jumpsBefore S γ = i.val at hi
    change JumpPath.jumpsBefore S γ = j.val at hj
    apply hij
    apply Fin.ext
    exact hi.symm.trans hj
  have hmeas : ∀ r, MeasurableSet (A r) := fun r =>
    JumpPath.measurableSet_jumpsBeforeSet S k r.val
  have hunion : (⋃ r, A r) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro γ
    rw [Set.mem_iUnion]
    have hle : JumpPath.jumpsBefore S γ ≤ k := by
      unfold JumpPath.jumpsBefore
      calc
        ((Finset.univ : Finset (Fin k)).filter fun i =>
          JumpPath.jumpTimes γ i.succ < (S : ℝ)).card ≤
            (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
        _ = k := Finset.card_fin k
    exact ⟨⟨JumpPath.jumpsBefore S γ, Nat.lt_succ_of_le hle⟩, rfl⟩
  rw [← Measure.restrict_iUnion hdisjoint hmeas]
  rw [hunion, Measure.restrict_univ]

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
