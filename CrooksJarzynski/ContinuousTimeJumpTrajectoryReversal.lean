/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpConcatLaw
import CrooksJarzynski.ContinuousTimeJumpFullPathReversal

/-!
# Real-time trajectories under path reversal

Record reversal agrees with physical time reversal away from jump times.  The
pointwise statement includes the exact-horizon condition carried almost surely
by the finite-generator path law; `IsValid` alone only says that the terminal
state has been reached by the horizon.
-/

open MeasureTheory
open scoped ENNReal

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u}

/-- Rewrite a partial sum over `Fin` as a sum over a natural-number range. -/
private theorem sum_Iio_eq_sum_range {k : ℕ} (a : Fin k) (f : Fin k → ℝ) :
    (∑ i ∈ Finset.Iio a, f i) =
      ∑ r ∈ Finset.range a.val, if hr : r < k then f ⟨r, hr⟩ else 0 := by
  have ha : a.val < k := a.isLt
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (by simpa using (Finset.mem_Iio.mp hi))
  · intro i _ j _ h
    exact Fin.ext h
  · intro r hr
    have hrlt : r < a.val := Finset.mem_range.mp hr
    have hrk : r < k := lt_trans hrlt ha
    refine ⟨⟨r, hrk⟩, Finset.mem_Iio.mpr ?_, rfl⟩
    simpa [Fin.lt_def] using hrlt
  · intro i hi
    rw [dif_pos i.isLt]

/-- Remove the initial state and holding interval from a path with at least one
jump. -/
def dropFirst {n : ℕ} (γ : JumpPath Ω (n + 1)) : JumpPath Ω n :=
  (fun i => γ.1 i.succ, fun i => γ.2 i.succ)

/-- The first holding interval followed by the jump times of `dropFirst`
recovers the noninitial jump times of the original path. -/
theorem jumpTimes_succ_eq {n : ℕ} (γ : JumpPath Ω (n + 1))
    (k : Fin (n + 1)) :
    jumpTimes γ k.succ = (γ.2 0 : ℝ) + jumpTimes (dropFirst γ) k := by
  unfold jumpTimes dropFirst
  rw [sum_Iio_eq_sum_range (a := k.succ), sum_Iio_eq_sum_range (a := k)]
  change
    (∑ r ∈ Finset.range (k.val + 1),
      if hr : r < n + 2 then (γ.2 ⟨r, hr⟩ : ℝ) else 0) = _
  rw [Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [dif_pos (by omega : i + 1 < n + 2), dif_pos (by omega : i < n + 1)]
  rfl

/-- Dropping the first interval after reversing is the reversal of dropping the
last interval. -/
@[simp]
theorem dropFirst_reverse {n : ℕ} (γ : JumpPath Ω (n + 1)) :
    dropFirst (reverse γ) = reverse (dropLast γ) := by
  apply Prod.ext <;> funext i
  · simp only [dropFirst, reverse, dropLast, Fin.rev_succ]
  · simp only [dropFirst, reverse, dropLast, Fin.rev_succ]

/-- Dropping the first and last intervals commutes. -/
@[simp]
theorem dropFirst_dropLast {n : ℕ} (γ : JumpPath Ω (n + 2)) :
    dropFirst (dropLast γ) = dropLast (dropFirst γ) := by
  rfl

/-- Before the first jump, the trajectory occupies its initial state. -/
theorem trajectory_eq_initial_of_lt_first : ∀ {n : ℕ}
    (γ : JumpPath Ω (n + 1)) (t : ℝ),
    0 ≤ t → t < γ.2 0 → trajectory γ t = γ.1 0
  | 0, γ, t, _, ht => by
      simp only [trajectory]
      rw [if_neg]
      · rfl
      · rw [show jumpTimes γ (Fin.last 1) = (γ.2 0 : ℝ) by
          unfold jumpTimes
          rw [sum_Iio_eq_sum_range]
          simp]
        exact not_le.mpr ht
  | n + 1, γ, t, ht0, ht => by
      rw [trajectory]
      have hlast : ¬ jumpTimes γ (Fin.last (n + 2)) ≤ t := by
        apply not_le.mpr
        calc
          t < (γ.2 0 : ℝ) := ht
          _ = jumpTimes γ (1 : Fin (n + 3)) := by
            unfold jumpTimes
            rw [sum_Iio_eq_sum_range]
            simp
          _ ≤ jumpTimes γ (Fin.last (n + 2)) :=
            jumpTimes_mono γ (by
              apply Fin.le_last)
      rw [if_neg hlast]
      exact trajectory_eq_initial_of_lt_first (dropLast γ) t ht0 ht

/-- After the first holding interval, deleting that interval and shifting the
clock does not change the trajectory. -/
theorem trajectory_dropFirst : ∀ {n : ℕ} (γ : JumpPath Ω (n + 1))
    (t : ℝ), (γ.2 0 : ℝ) ≤ t →
      trajectory γ t = trajectory (dropFirst γ) (t - (γ.2 0 : ℝ))
  | 0, γ, t, ht => by
      simp only [trajectory, dropFirst]
      rw [if_pos (by
        rw [show jumpTimes γ (Fin.last 1) = (γ.2 0 : ℝ) by
          unfold jumpTimes
          rw [sum_Iio_eq_sum_range]
          simp]
        exact ht)]
      apply congrArg γ.1
      apply Fin.ext
      simp
  | n + 1, γ, t, ht => by
      have htime := jumpTimes_succ_eq γ (Fin.last (n + 1))
      have hlast : Fin.last (n + 2) = (Fin.last (n + 1)).succ := by
        apply Fin.ext
        simp
      change
        (if jumpTimes γ (Fin.last (n + 2)) ≤ t then
            γ.1 (Fin.last (n + 2))
          else trajectory (dropLast γ) t) =
        (if jumpTimes (dropFirst γ) (Fin.last (n + 1)) ≤
              t - (γ.2 0 : ℝ) then
            (dropFirst γ).1 (Fin.last (n + 1))
          else trajectory (dropLast (dropFirst γ))
            (t - (γ.2 0 : ℝ)))
      rw [hlast, htime]
      by_cases h : jumpTimes (dropFirst γ) (Fin.last (n + 1)) ≤
          t - (γ.2 0 : ℝ)
      · rw [if_pos (by linarith), if_pos h]
        rfl
      · rw [if_neg (by intro h'; exact h (by linarith)), if_neg h,
          ← dropFirst_dropLast]
        exact trajectory_dropFirst (dropLast γ) t ht

/-- The last jump time is the total holding time of the chart with its terminal
interval removed. -/
theorem jumpTimes_last_eq_totalHoldingTime_dropLast {n : ℕ}
    (γ : JumpPath Ω (n + 1)) :
    jumpTimes γ (Fin.last (n + 1)) =
      (totalHoldingTime (dropLast γ) : ℝ) := by
  unfold jumpTimes totalHoldingTime dropLast
  rw [NNReal.coe_sum, Finset.sum_fin_eq_sum_range,
    sum_Iio_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [dif_pos (by omega : i < n + 2), dif_pos (by omega : i < n + 1)]
  rfl

/-- Removing the terminal interval splits the total holding time into the
remaining prefix and that terminal interval. -/
theorem totalHoldingTime_dropLast_add_last {n : ℕ}
    (γ : JumpPath Ω (n + 1)) :
    totalHoldingTime (dropLast γ) + γ.2 (Fin.last (n + 1)) =
      totalHoldingTime γ := by
  unfold totalHoldingTime dropLast
  exact (Fin.sum_univ_castSucc (fun i => γ.2 i)).symm

/-- **Pointwise physical time reversal.**  On an exact-horizon valid chart,
record reversal evaluates at the mirrored time whenever the mirrored time is
not a noninitial jump time of the original chart. -/
theorem trajectory_reverse_eq_mirror : ∀ {n : ℕ} {T : NNReal}
    (γ : JumpPath Ω n) (_hvalid : IsValid T γ)
    (_htotal : totalHoldingTime γ = T) (t : ℝ)
    (_ht0 : 0 ≤ t) (_htT : t ≤ T)
    (_hnot : ∀ k : Fin n, jumpTimes γ k.succ ≠ (T : ℝ) - t),
    trajectory (reverse γ) t = trajectory γ ((T : ℝ) - t)
  | 0, _, γ, _, _, _, _, _, _ => by
      simp [trajectory, reverse]
  | n + 1, T, γ, hvalid, htotal, t, ht0, htT, hnot => by
      let pre := dropLast γ
      let terminalHolding := γ.2 (Fin.last (n + 1))
      have hsplit : pre.totalHoldingTime + terminalHolding = T := by
        rw [totalHoldingTime_dropLast_add_last]
        exact htotal
      have hsplitReal : (pre.totalHoldingTime : ℝ) +
          (terminalHolding : ℝ) = (T : ℝ) := by
        exact_mod_cast hsplit
      have hjump : jumpTimes γ (Fin.last (n + 1)) =
          (pre.totalHoldingTime : ℝ) :=
        jumpTimes_last_eq_totalHoldingTime_dropLast γ
      have hne : (T : ℝ) - t ≠ (pre.totalHoldingTime : ℝ) := by
        intro h
        apply hnot (Fin.last n)
        simpa [hjump] using h.symm
      rcases lt_or_gt_of_ne hne with hbefore | hafter
      · have htshift : (terminalHolding : ℝ) ≤ t := by
          linarith
        rw [trajectory_dropFirst (reverse γ) t (by simpa [reverse] using htshift),
          dropFirst_reverse]
        have hpreValid : IsValid pre.totalHoldingTime pre := by
          refine ⟨?_, jumpTimes_le_totalHoldingTime pre _⟩
          intro i
          exact hvalid.1 i.castSucc
        have htshift0 : 0 ≤ t - (terminalHolding : ℝ) := sub_nonneg.mpr htshift
        have htshiftT : t - (terminalHolding : ℝ) ≤ pre.totalHoldingTime := by
          linarith
        have hmirror : (pre.totalHoldingTime : ℝ) -
              (t - (terminalHolding : ℝ)) = (T : ℝ) - t := by
          linarith
        have hpreNot : ∀ k : Fin n,
            jumpTimes pre k.succ ≠
              (pre.totalHoldingTime : ℝ) -
                (t - (terminalHolding : ℝ)) := by
          intro k hk
          apply hnot k.castSucc
          rw [← hmirror, ← hk, jumpTimes_dropLast]
          rfl
        change trajectory (reverse pre) (t - (terminalHolding : ℝ)) =
          trajectory γ ((T : ℝ) - t)
        rw [trajectory_reverse_eq_mirror pre hpreValid rfl
          (t - (terminalHolding : ℝ)) htshift0 htshiftT hpreNot,
          hmirror]
        change trajectory (dropLast γ) ((T : ℝ) - t) =
          (if jumpTimes γ (Fin.last (n + 1)) ≤ (T : ℝ) - t then
            γ.1 (Fin.last (n + 1))
          else trajectory (dropLast γ) ((T : ℝ) - t))
        rw [if_neg (by rw [hjump]; exact not_le.mpr hbefore)]
      · have hterminal : trajectory γ ((T : ℝ) - t) =
            γ.1 (Fin.last (n + 1)) := by
          exact trajectory_eq_terminal_of_last_le γ _ (by rw [hjump]; exact hafter.le)
        have htlt : t < (terminalHolding : ℝ) := by
          linarith
        have hreverseInitial : trajectory (reverse γ) t =
            (reverse γ).1 0 :=
          trajectory_eq_initial_of_lt_first (reverse γ) t ht0 (by
            simpa [reverse] using htlt)
        rw [hterminal, hreverseInitial]
        simp [reverse]

end JumpPath

namespace FullPath

variable {Ω : Type u}

/-- **Pointwise physical time reversal for complete paths.**  An exact-horizon
valid complete path agrees with its mirrored trajectory at every deterministic
time whose mirror is not a jump time. -/
theorem trajectory_reverse_eq_mirror {T : NNReal} (γ : FullPath Ω)
    (hvalid : IsValid T γ) (htotal : totalHoldingTime γ = T)
    (t : NNReal) (ht : t ≤ T) (hnot : ¬ HasJumpAt (T - t) γ) :
    trajectory (reverse γ) t = trajectory γ (T - t) := by
  rcases γ with ⟨n, γ⟩
  apply JumpPath.trajectory_reverse_eq_mirror γ hvalid htotal t
      (by positivity) (by exact_mod_cast ht)
  intro k hk
  apply hnot
  refine ⟨k, ?_⟩
  rw [NNReal.coe_sub ht]
  exact hk

end FullPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [MeasurableSingletonClass Ω] in
/-- At every fixed time, sector-law record reversal agrees almost surely with
physical time reversal. -/
theorem sectorLawFrom_ae_trajectory_reverse_eq_mirror
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ)
    (t : NNReal) (ht : t ≤ T) :
    (fun γ => JumpPath.trajectory (JumpPath.reverse γ) t) =ᵐ[G.sectorLawFrom T x n]
      fun γ => JumpPath.trajectory γ (T - t) := by
  filter_upwards [G.sectorLawFrom_ae_isValid T x n,
    G.sectorLawFrom_ae_totalHoldingTime T x n,
    G.sectorLawFrom_ae_noJumpAt T x n (T - t)] with γ hvalid htotal hnot
  apply JumpPath.trajectory_reverse_eq_mirror γ hvalid htotal t
      (by positivity) (by exact_mod_cast ht)
  intro k hk
  apply hnot
  refine ⟨k, ?_⟩
  rw [NNReal.coe_sub ht]
  exact hk

omit [MeasurableSingletonClass Ω] in
/-- **Almost-sure physical time reversal.**  At a fixed observation time,
record reversal under the normalized fixed-initial path law realizes the
mirrored real-time trajectory. -/
theorem pathLawFrom_ae_trajectory_reverse_eq_mirror
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω)
    (t : NNReal) (ht : t ≤ T) :
    (fun γ => FullPath.trajectory (FullPath.reverse γ) t) =ᵐ[G.pathLawFrom T x]
      fun γ => FullPath.trajectory γ (T - t) := by
  filter_upwards [G.pathLawFrom_ae_isValid T x,
    G.pathLawFrom_ae_totalHoldingTime T x,
    (show ∀ᵐ γ ∂G.pathLawFrom T x, ¬ FullPath.HasJumpAt (T - t) γ by
      simpa [tsub_add_cancel_of_le ht] using
        G.pathLawFrom_ae_noJumpAt (T - t) t x)] with γ hvalid htotal hnot
  exact FullPath.trajectory_reverse_eq_mirror γ hvalid htotal t ht hnot

omit [MeasurableSingletonClass Ω] in
/-- **Finite-dimensional physical time reversal.**  Joint evaluation of
record-reversed paths has the same law as joint evaluation of the original
paths at the mirrored deterministic times. -/
theorem map_trajectory_reverse_eq_map_mirror
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) {k : ℕ}
    (time : Fin k → NNReal) (_hmono : Monotone time)
    (htime : ∀ i, time i ≤ T) :
    (G.pathLawFrom T x).map
        (fun γ i => FullPath.trajectory (FullPath.reverse γ) (time i)) =
      (G.pathLawFrom T x).map
        (fun γ i => FullPath.trajectory γ (T - time i)) := by
  apply Measure.map_congr
  apply (ae_all_iff.2 fun i =>
    G.pathLawFrom_ae_trajectory_reverse_eq_mirror T x (time i) (htime i)).mono
  intro γ hγ
  funext i
  exact hγ i

end FiniteJumpGenerator

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
