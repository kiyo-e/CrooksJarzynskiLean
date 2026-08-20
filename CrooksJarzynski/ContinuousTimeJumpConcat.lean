/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTrajectory

/-!
# Concatenation of continuous-time jump paths

Two fixed-jump-count paths can be glued into one longer path when the state
reached by the prefix equals the state recorded at the start of the suffix.
The concatenated path reuses every jump of the prefix, drops the duplicated
boundary state of the suffix, and merges the two holding intervals at the seam
into a single residence interval of the shared boundary state.  This module
records the concatenation, its arithmetic on jump times and holding times, the
gluing laws for the real-time trajectory, sectorwise validity, and the lift to
complete full paths.  It is deliberately pointwise: no measure equality is
proved here.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u}

/-- Glue two jump paths at a shared boundary state.

The prefix contributes all `n + 1` of its states and its first `n + 1`
holding intervals; the suffix contributes its remaining `m` states and
holding intervals after the duplicated initial state.  The residence time at
the seam is the merged holding time `γ.2 (last n) + δ.2 0`.  The resulting
chart has `n + m` jumps, `n + m + 1` states and `n + m + 1` holding
intervals. -/
def concat {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m) : JumpPath Ω (n + m) :=
  ( (fun i : Fin (n + m + 1) =>
      Fin.append (m := n + 1) (n := m) γ.1 (δ.1 ∘ Fin.succ)
        (Fin.cast (by omega) i)),
    (fun i : Fin (n + m + 1) =>
      Fin.append (m := n + 1) (n := m)
        (fun j : Fin (n + 1) =>
          if j = Fin.last n then γ.2 j + δ.2 0 else γ.2 j)
        (δ.2 ∘ Fin.succ) (Fin.cast (by omega) i)) )

/-- Cancelling two `Fin.cast` steps through provably equal sizes. -/
@[simp]
lemma fin_cast_roundtrip {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (i : Fin n) :
    Fin.cast h₂ (Fin.cast h₁ i) = i := by
  rw [Fin.cast_cast]
  rfl

@[simp]
theorem concat_fst_castAdd {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (i : Fin (n + 1)) :
    (concat γ δ).1 (Fin.cast (by omega) (Fin.castAdd m i)) = γ.1 i := by
  simp [concat]

@[simp]
theorem concat_fst_natAdd {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (j : Fin m) :
    (concat γ δ).1 (Fin.cast (by omega) (Fin.natAdd (n + 1) j)) = δ.1 j.succ := by
  simp [concat]

@[simp]
theorem concat_snd_castAdd {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (i : Fin (n + 1)) :
    (concat γ δ).2 (Fin.cast (by omega) (Fin.castAdd m i)) =
      if i = Fin.last n then γ.2 i + δ.2 0 else γ.2 i := by
  simp [concat]

@[simp]
theorem concat_snd_natAdd {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (j : Fin m) :
    (concat γ δ).2 (Fin.cast (by omega) (Fin.natAdd (n + 1) j)) = δ.2 j.succ := by
  simp [concat]

/-- Variant of `concat_snd_natAdd` taking the cast proof explicitly. -/
private theorem concat_snd_natAdd' {n m : ℕ} (h : (n + 1) + m = n + m + 1)
    (γ : JumpPath Ω n) (δ : JumpPath Ω m) (j : Fin m) :
    (concat γ δ).2 (Fin.cast h (Fin.natAdd (n + 1) j)) = δ.2 j.succ := by
  rw [show (Fin.cast h (Fin.natAdd (n + 1) j)) =
      Fin.cast (by omega : (n + 1) + m = n + m + 1) (Fin.natAdd (n + 1) j) by
    apply Fin.ext
    simp]
  simp [concat]

/-- Version of `concat_snd_castAdd` with an explicit cast proof, so it can be
   used when the cast is `Fin.cast h₂` for a user-supplied `h₂` rather than the
   inline `by omega`. -/
private lemma concat_snd_castAdd' {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (h : (n + 1) + m = n + m + 1) (i : Fin (n + 1)) :
    (concat γ δ).2 (Fin.cast h (Fin.castAdd m i)) =
      if i = Fin.last n then γ.2 i + δ.2 0 else γ.2 i := by
  rw [show (Fin.cast h (Fin.castAdd m i) : Fin (n + m + 1)) =
      Fin.cast (by omega) (Fin.castAdd m i) by
    apply Fin.ext
    simp]
  simp [concat]

@[simp]
theorem concat_snd_boundary {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m) :
    (concat γ δ).2 ⟨n, by omega⟩ = γ.2 (Fin.last n) + δ.2 0 := by
  have h : (⟨n, by omega⟩ : Fin (n + m + 1)) =
      Fin.cast (by omega : (n + 1) + m = n + m + 1) (Fin.castAdd m (Fin.last n)) := by
    apply Fin.ext
    simp
  rw [h]
  simp [concat]

@[simp]
theorem concat_state_zero {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m) :
    (concat γ δ).1 0 = γ.1 0 := by
  have h : (0 : Fin (n + m + 1)) =
      Fin.cast (by omega : (n + 1) + m = n + m + 1)
        (Fin.castAdd m (0 : Fin (n + 1))) := by
    apply Fin.ext
    simp
  rw [h]
  simp [concat]

/-- The final state of a concatenation is the final state of the suffix when
both paths agree at the seam. -/
theorem concat_state_last {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (hmatch : γ.1 (Fin.last n) = δ.1 0) :
    (concat γ δ).1 (Fin.last (n + m)) = δ.1 (Fin.last m) := by
  cases m with
  | zero =>
      change (concat γ δ).1 (Fin.last n) = δ.1 0
      have h : (Fin.last n : Fin (n + 1)) =
          Fin.cast (by omega : (n + 1) + 0 = n + 0 + 1)
            (Fin.castAdd 0 (Fin.last n)) := by
        apply Fin.ext
        simp
      rw [h]
      simp only [concat, fin_cast_roundtrip]
      rw [Fin.append_left]
      exact hmatch
  | succ m =>
      have h : (Fin.last (n + (m + 1)) : Fin (n + (m + 1) + 1)) =
          Fin.cast (by omega : (n + 1) + (m + 1) = n + (m + 1) + 1)
            (Fin.natAdd (n + 1) (Fin.last m)) := by
        apply Fin.ext
        simp
        omega
      rw [h]
      simp only [concat]
      rw [fin_cast_roundtrip, Fin.append_right]
      rfl

/-- A partial sum over an initial segment of `Fin k` is the corresponding sum
   over a natural range. -/
private lemma sum_Iio_eq_sum_range {k : ℕ} (a : Fin k) (f : Fin k → ℝ) :
    (∑ i ∈ Finset.Iio a, f i) =
      ∑ r ∈ Finset.range a.val, if hr : r < k then f ⟨r, hr⟩ else 0 := by
  have ha : a.val < k := a.isLt
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (by simpa using (Finset.mem_Iio.mp hi))
  · intro i hi j hj h
    apply Fin.ext
    exact h
  · intro r hr
    have hrlt : r < a.val := Finset.mem_range.mp hr
    have hrk : r < k := lt_trans hrlt ha
    refine ⟨⟨r, hrk⟩, ?_, rfl⟩
    exact Finset.mem_Iio.mpr (by
      simpa [Fin.lt_def] using hrlt)
  · intro i hi
    rw [dif_pos i.isLt]

/-- In the left block of a concatenation (away from the seam) the holding
   intervals are the prefix's own. -/
private lemma concat_snd_range_left {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    {r : ℕ} (hr : r ≠ n) (hrn1 : r < n + 1) :
    (concat γ δ).2 ⟨r, by omega⟩ = γ.2 ⟨r, by omega⟩ := by
  have hcast : (⟨r, by omega⟩ : Fin (n + m + 1)) =
      Fin.cast (by omega : (n + 1) + m = n + m + 1)
        (Fin.castAdd m (⟨r, by omega⟩ : Fin (n + 1))) := by
    apply Fin.ext
    simp
  have hne : (⟨r, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    exact hr (congrArg Fin.val h)
  rw [hcast]
  simp only [concat]
  rw [fin_cast_roundtrip, Fin.append_left]
  simp [hne]

/-- In the right block of a concatenation the holding intervals are those of
   the suffix after its duplicated initial state. -/
private lemma concat_snd_range_right {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    {r : ℕ} (hr : r < m) :
    (concat γ δ).2 ⟨n + 1 + r, by omega⟩ = δ.2 (⟨r, by omega⟩ : Fin m).succ := by
  have hcast : (⟨n + 1 + r, by omega⟩ : Fin (n + m + 1)) =
      Fin.cast (by omega : (n + 1) + m = n + m + 1)
        (Fin.natAdd (n + 1) (⟨r, by omega⟩ : Fin m)) := by
    apply Fin.ext
    simp
  rw [hcast]
  simp only [concat]
  rw [fin_cast_roundtrip, Fin.append_right]
  rfl

/-- The holding interval at every position of a concatenation, expressed by
   the position of the index. -/
private lemma concat_snd_value_at {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    {r : ℕ} (hr : r < n + m + 1) :
    (concat γ δ).2 ⟨r, hr⟩ =
      if hrlt : r < n then γ.2 ⟨r, by omega⟩
      else if _ : r = n then γ.2 (Fin.last n) + δ.2 0
      else δ.2 ⟨r - n, by omega⟩ := by
  by_cases hrlt : r < n
  · have hv := concat_snd_range_left (γ := γ) (δ := δ) (r := r)
      (hr := ne_of_lt hrlt) (hrn1 := by omega)
    simp [hrlt, hv]
  · by_cases hrn : r = n
    · subst hrn
      have hv := concat_snd_boundary (γ := γ) (δ := δ)
      simp [hv]
    · have hnle : n ≤ r := not_lt.mp hrlt
      have hnneq : n ≠ r := by intro h; exact hrn (h.symm)
      have hbig : n < r := lt_of_le_of_ne hnle hnneq
      have hle : n + 1 ≤ r := Nat.succ_le_of_lt hbig
      have hres : r - (n + 1) + (n + 1) = r := Nat.sub_add_cancel hle
      have hval := concat_snd_range_right (γ := γ) (δ := δ) (r := r - (n + 1))
        (hr := by omega)
      have hidx : (⟨r, hr⟩ : Fin (n + m + 1)) = ⟨n + 1 + (r - (n + 1)), by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hidx]
      rw [hval]
      have hsucc : (⟨r - (n + 1), by omega⟩ : Fin m).succ = ⟨r - n, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hsucc]
      simp [hrlt, hrn]

/-- The jump times of a concatenation agree with those of the prefix on the
   whole prefix. -/
theorem jumpTimes_concat_left {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (k : Fin (n + 1)) :
    jumpTimes (concat γ δ) (Fin.cast (by omega : (n + 1) + m = n + m + 1)
      (Fin.castAdd m k)) = jumpTimes γ k := by
  unfold jumpTimes
  rw [sum_Iio_eq_sum_range (a := Fin.cast (by omega : (n + 1) + m = n + m + 1)
      (Fin.castAdd m k)) (f := fun i : Fin (n + m + 1) => ((concat γ δ).2 i : ℝ))]
  rw [sum_Iio_eq_sum_range (a := k) (f := fun i : Fin (n + 1) => (γ.2 i : ℝ))]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r < k.val := Finset.mem_range.mp hr
  have hrn : r < n + 1 := lt_trans hrk k.isLt
  have hrnm : r < n + m + 1 := by omega
  rw [dif_pos hrnm, dif_pos hrn]
  rcases lt_or_eq_of_le (show r ≤ n by omega) with hrlt | hrn0
  · have hv := concat_snd_range_left (γ := γ) (δ := δ) (r := r)
      (hr := ne_of_lt hrlt) (hrn1 := by omega)
    exact congrArg (fun x : NNReal => (x : ℝ)) hv
  · exfalso
    omega

/-- Sum over the left block of a concatenation. -/
private lemma concat_jump_sum_left {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m) :
    (∑ r ∈ Finset.range n, (if hr : r < n + m + 1 then ((concat γ δ).2 ⟨r, hr⟩ : ℝ) else 0)) =
      ∑ r ∈ Finset.range n, (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0) := by
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrl : r < n := Finset.mem_range.mp hr
  have hrn : r < n + 1 := by omega
  have hrb : r < n + m + 1 := by omega
  rw [dif_pos hrb, dif_pos hrn]
  rw [concat_snd_range_left (r := r) (hr := ne_of_lt hrl) (hrn1 := hrn)]

/-- Summing the right part of a jump interval, expressed via the seam. -/
private lemma concat_jump_seam {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (j : Fin (m + 1)) :
    (∑ s ∈ Finset.range j.val,
        (if hs : n + s < n + m + 1 then ((concat γ δ).2 ⟨n + s, hs⟩ : ℝ) else 0)) =
      ∑ s ∈ Finset.range j.val,
      (if s = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
        else if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0) := by
  refine Finset.sum_congr rfl ?_
  intro s hs
  have hsb : s < m + 1 := by
    have hsj := Finset.mem_range.mp hs
    omega
  have hbc : n + s < n + m + 1 := by omega
  by_cases hs0 : s = 0
  · subst hs0
    rw [dif_pos (by omega : n + 0 < n + m + 1)]
    rw [show ((⟨n + 0, by omega⟩ : Fin (n + m + 1)) = ⟨n, by omega⟩) by
      apply Fin.ext; simp]
    rw [concat_snd_boundary]
    simp
  · rw [if_neg hs0, dif_pos hbc, dif_pos hsb]
    rw [show (⟨n + s, by omega⟩ : Fin (n + m + 1)) = ⟨n + 1 + (s - 1), by omega⟩ by
      apply Fin.ext; simp; omega]
    rw [concat_snd_range_right (r := s - 1) (hr := by omega)]
    rw [show (⟨s - 1, by omega⟩ : Fin m).succ = ⟨s, hsb⟩ by
      apply Fin.ext; simp; omega]

/-- The seam sum of a concatenation decomposes into the suffix and the seam. -/
private lemma concat_seam_split {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (j : Fin (m + 1)) (h : j.val = j.val - 1 + 1) :
    (∑ s ∈ Finset.range j.val,
        (if s = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
          else if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0)) =
      (∑ s ∈ Finset.range (j.val - 1),
          (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)) +
        ((γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)) := by
  calc
    (∑ v ∈ Finset.range j.val,
        (if v = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
          else if hs : v < m + 1 then (δ.2 ⟨v, hs⟩ : ℝ) else 0))
        = ∑ v ∈ Finset.range (j.val - 1 + 1),
        (if v = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
          else if hs : v < m + 1 then (δ.2 ⟨v, hs⟩ : ℝ) else 0) := by
          rw [h]
          congr 1
    _ = (∑ v ∈ Finset.range (j.val - 1),
            (if v + 1 = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
              else if hs : v + 1 < m + 1 then (δ.2 ⟨v + 1, hs⟩ : ℝ) else 0)) +
          (if (0 : ℕ) = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
            else if hs : 0 < m + 1 then (δ.2 ⟨0, hs⟩ : ℝ) else 0) := by
          rw [Finset.sum_range_succ' (fun v : ℕ =>
            (if v = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
              else if hs : v < m + 1 then (δ.2 ⟨v, hs⟩ : ℝ) else 0)) (j.val - 1)]
    _ = (∑ v ∈ Finset.range (j.val - 1),
            (if v + 1 = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
              else if hs : v + 1 < m + 1 then (δ.2 ⟨v + 1, hs⟩ : ℝ) else 0)) +
          ((γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)) := by
          rw [show (if (0 : ℕ) = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
            else if hs : 0 < m + 1 then (δ.2 ⟨0, hs⟩ : ℝ) else 0) =
            (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ) by simp]
    _ = (∑ s ∈ Finset.range (j.val - 1),
            (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)) +
          ((γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)) := by
          rw [show (∑ v ∈ Finset.range (j.val - 1),
                (if v + 1 = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
                  else if hs : v + 1 < m + 1 then (δ.2 ⟨v + 1, hs⟩ : ℝ) else 0)) =
              (∑ s ∈ Finset.range (j.val - 1),
                (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)) by
            refine Finset.sum_congr rfl ?_
            intro v hv
            have hnn : v + 1 ≠ 0 := by omega
            rw [if_neg hnn]]

/-- The shifted suffix sum gives back the suffix jump sum. -/
private lemma concat_delta_join {m : ℕ} (δ : JumpPath Ω m) (j : Fin (m + 1))
    (h : j.val = j.val - 1 + 1) :
    (δ.2 0 : ℝ) + (∑ s ∈ Finset.range (j.val - 1),
        (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)) =
      ∑ s ∈ Finset.range j.val, (if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0) := by
  calc
    (δ.2 0 : ℝ) + (∑ s ∈ Finset.range (j.val - 1),
        (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0))
        = ∑ v ∈ Finset.range (j.val - 1 + 1),
            (if hs : v < m + 1 then (δ.2 ⟨v, hs⟩ : ℝ) else 0) := by
          rw [Finset.sum_range_succ' (fun v : ℕ =>
            (if hs : v < m + 1 then (δ.2 ⟨v, hs⟩ : ℝ) else 0)) (j.val - 1)]
          rw [show (if hs : (0 : ℕ) < m + 1 then (δ.2 ⟨0, hs⟩ : ℝ) else 0) = (δ.2 0 : ℝ) by
            rw [dif_pos (Nat.succ_pos m)]
            rfl]
          ac_rfl
    _ = ∑ s ∈ Finset.range j.val, (if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0) := by
          rw [h]
          congr 1

/-- The jump times of a concatenation run through the full holding time of the
   prefix and then the jump times of the suffix. -/
theorem jumpTimes_concat_right {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (j : Fin (m + 1)) (hj : j ≠ 0) :
    jumpTimes (concat γ δ) (Fin.cast (by omega : n + (m + 1) = n + m + 1)
      (Fin.natAdd n j)) = (γ.totalHoldingTime : ℝ) + jumpTimes δ j := by
  unfold jumpTimes totalHoldingTime
  rw [NNReal.coe_sum]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_Iio_eq_sum_range (a := j) (f := fun i : Fin (m + 1) => (δ.2 i : ℝ))]
  rw [sum_Iio_eq_sum_range (a := Fin.cast (by omega : n + (m + 1) = n + m + 1)
      (Fin.natAdd n j)) (f := fun i : Fin (n + m + 1) => ((concat γ δ).2 i : ℝ))]
  have hjgt : 0 < j.val := by
    have hval : j.val ≠ 0 := by
      intro h
      exact hj (Fin.ext (by simp [h]))
    exact Nat.pos_of_ne_zero hval
  have hjun : j.val = (j.val - 1) + 1 := by
    rw [Nat.sub_add_cancel]
    exact Nat.succ_le_of_lt hjgt
  have hjm : j.val ≤ m := Nat.le_of_lt_succ j.isLt
  have hgt : ∀ r ∈ Finset.range n, r < n + m + 1 := by
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    omega
  have hgt2 : ∀ s ∈ Finset.range j.val, n + s < n + m + 1 := by
    intro s hs
    have hsj : s < j.val := Finset.mem_range.mp hs
    omega
  have hgt3 : ∀ s ∈ Finset.range j.val, s < m + 1 := by
    intro s hs
    have hsj : s < j.val := Finset.mem_range.mp hs
    omega
  calc
    (∑ r ∈ Finset.range (n + j.val),
        (if hr : r < n + m + 1 then ((concat γ δ).2 ⟨r, hr⟩ : ℝ) else 0))
        = (∑ r ∈ Finset.range n,
              (if hr : r < n + m + 1 then ((concat γ δ).2 ⟨r, hr⟩ : ℝ) else 0)) +
          (∑ s ∈ Finset.range j.val,
              (if hs : n + s < n + m + 1 then ((concat γ δ).2 ⟨n + s, hs⟩ : ℝ)
                else 0)) := by
          rw [Finset.sum_range_add]
  _ = (∑ r ∈ Finset.range (n + 1),
          (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
      (∑ s ∈ Finset.range j.val, (if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0)) := by
        have hga : (∑ r ∈ Finset.range n, (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
            (γ.2 (Fin.last n) : ℝ) =
            (∑ r ∈ Finset.range (n + 1),
              (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) := by
          rw [Finset.sum_range_succ (fun r : ℕ => (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) n]
          rw [show (if hr : n < n + 1 then (γ.2 ⟨n, hr⟩ : ℝ) else 0) = (γ.2 (Fin.last n) : ℝ) by
            rw [dif_pos (by omega : n < n + 1)]
            rw [show (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n by
              apply Fin.ext
              simp]]
        calc
          (∑ r ∈ Finset.range n,
              (if hr : r < n + m + 1 then ((concat γ δ).2 ⟨r, hr⟩ : ℝ) else 0)) +
            (∑ s ∈ Finset.range j.val,
              (if hs : n + s < n + m + 1 then ((concat γ δ).2 ⟨n + s, hs⟩ : ℝ)
                else 0))
            = (∑ r ∈ Finset.range n, (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
                (∑ s ∈ Finset.range j.val,
                  (if s = 0 then (γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ)
                    else if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0)) := by
              rw [concat_jump_sum_left]
              rw [concat_jump_seam (j := j)]
            _ = (∑ r ∈ Finset.range n, (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
                ((∑ s ∈ Finset.range (j.val - 1),
                    (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)) +
                  ((γ.2 (Fin.last n) : ℝ) + (δ.2 0 : ℝ))) := by
              rw [concat_seam_split (j := j) (h := hjun)]
            _ = (∑ r ∈ Finset.range n, (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
                ((γ.2 (Fin.last n) : ℝ) + ((δ.2 0 : ℝ) +
                  (∑ s ∈ Finset.range (j.val - 1),
                    (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)))) := by
              ac_rfl
            _ = ((∑ r ∈ Finset.range n, (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
                  (γ.2 (Fin.last n) : ℝ)) +
                ((δ.2 0 : ℝ) + (∑ s ∈ Finset.range (j.val - 1),
                  (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0))) := by
              ac_rfl
            _ = (∑ r ∈ Finset.range (n + 1),
                    (if hr : r < n + 1 then (γ.2 ⟨r, hr⟩ : ℝ) else 0)) +
                (∑ s ∈ Finset.range j.val, (if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0)) := by
                  rw [hga]
                  rw [show (δ.2 0 : ℝ) + (∑ s ∈ Finset.range (j.val - 1),
                      (if hs : s + 1 < m + 1 then (δ.2 ⟨s + 1, hs⟩ : ℝ) else 0)) =
                      ∑ s ∈ Finset.range j.val, (if hs : s < m + 1 then (δ.2 ⟨s, hs⟩ : ℝ) else 0) by
                    exact concat_delta_join δ j hjun]
/-- The total holding time of a concatenation is the sum of the holding times
   of its two constituents. -/
theorem totalHoldingTime_concat {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m) :
    (concat γ δ).totalHoldingTime = γ.totalHoldingTime + δ.totalHoldingTime := by
  unfold totalHoldingTime
  have h₂ : (n + 1) + m = n + m + 1 := by omega
  have hre : (∑ i : Fin (n + m + 1), (concat γ δ).2 i) =
      (∑ i : Fin ((n + 1) + m), (concat γ δ).2 (Fin.cast h₂ i)) := by
    refine Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
      (f := fun i : Fin (n + m + 1) => (concat γ δ).2 i)
      (g := fun i : Fin ((n + 1) + m) => (concat γ δ).2 (Fin.cast h₂ i))
      (fun i _ => Fin.cast h₂.symm i) ?_ ?_ ?_ ?_
    · intro i hi
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      apply Fin.ext
      simpa using congrArg Fin.val h
    · intro b hb
      refine ⟨Fin.cast h₂ b, by simp, ?_⟩
      exact fin_cast_roundtrip h₂ h₂.symm b
    · intro a ha
      exact congrArg (fun x : Fin (n + m + 1) => (concat γ δ).2 x)
        (fin_cast_roundtrip h₂.symm h₂ a)
  calc
    (∑ i : Fin (n + m + 1), (concat γ δ).2 i)
        = (∑ i : Fin ((n + 1) + m), (concat γ δ).2 (Fin.cast h₂ i)) := hre
    _ = (∑ i : Fin (n + 1), (concat γ δ).2 (Fin.cast h₂ (Fin.castAdd m i))) +
        (∑ i : Fin m, (concat γ δ).2 (Fin.cast h₂ (Fin.natAdd (n + 1) i))) := by
          rw [Fin.sum_univ_add (a := n + 1) (b := m)
            (f := fun i : Fin ((n + 1) + m) => (concat γ δ).2 (Fin.cast h₂ i))]
    _ = ((∑ i : Fin (n + 1), γ.2 i) + δ.2 0) +
        (∑ i : Fin m, δ.2 i.succ) := by
          have hL : (∑ i : Fin (n + 1), (concat γ δ).2 (Fin.cast h₂ (Fin.castAdd m i))) =
              (∑ i : Fin (n + 1), γ.2 i) + δ.2 0 := by
            rw [show (∑ i : Fin (n + 1), (concat γ δ).2 (Fin.cast h₂ (Fin.castAdd m i))) =
                (∑ i : Fin (n + 1),
                  (if i = Fin.last n then γ.2 i + δ.2 0 else γ.2 i)) by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact concat_snd_castAdd' γ δ h₂ i]
            calc
              (∑ i : Fin (n + 1), (if i = Fin.last n then γ.2 i + δ.2 0 else γ.2 i))
                  = ∑ i : Fin (n + 1), (γ.2 i + if i = Fin.last n then δ.2 0 else 0) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    by_cases h : i = Fin.last n
                    · rw [if_pos h, if_pos h]
                    · rw [if_neg h, if_neg h, add_zero]
              _ = (∑ i : Fin (n + 1), γ.2 i) + (∑ i : Fin (n + 1), if i = Fin.last n then δ.2 0 else 0) := by
                    rw [Finset.sum_add_distrib]
              _ = (∑ i : Fin (n + 1), γ.2 i) + δ.2 0 := by
                    rw [show (∑ i : Fin (n + 1), if i = Fin.last n then δ.2 0 else 0) =
                        δ.2 0 by
                      simp [Finset.sum_ite_eq']]
          have hR : (∑ i : Fin m, (concat γ δ).2 (Fin.cast h₂ (Fin.natAdd (n + 1) i))) =
              (∑ i : Fin m, δ.2 i.succ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact concat_snd_natAdd' h₂ γ δ i
          rw [hL, hR]
    _ = (∑ i : Fin (n + 1), γ.2 i) + (δ.2 0 + (∑ i : Fin m, δ.2 i.succ)) := by
          ac_rfl
    _ = (∑ i : Fin (n + 1), γ.2 i) + (∑ i : Fin (m + 1), δ.2 i) := by
          rw [show (δ.2 0 + (∑ i : Fin m, δ.2 i.succ)) =
              (∑ i : Fin (m + 1), δ.2 i) by
            rw [← Fin.sum_univ_succ (fun i : Fin (m + 1) => δ.2 i)]]

/-- All non-terminal holding intervals of a concatenation are positive when
the corresponding intervals of the two constituents are positive.  (The seam
holding `γ.2 (last n) + δ.2 0` is positive because `δ.2 0` is.) -/
private lemma concat_holding_pos {n m : ℕ} {γ : JumpPath Ω n} {δ : JumpPath Ω m}
    (hγ : ∀ j : Fin n, 0 < γ.2 j.castSucc)
    (hδ : ∀ j : Fin m, 0 < δ.2 j.castSucc) :
    ∀ i : Fin (n + m), 0 < (concat γ δ).2 i.castSucc := by
  intro i
  by_cases h1 : (i : ℕ) < n
  · rw [show (concat γ δ).2 i.castSucc = γ.2 ⟨(i : ℕ), by omega⟩ by
      rw [show (i.castSucc : Fin (n + m + 1)) = ⟨(i : ℕ), by omega⟩ by
        apply Fin.ext
        simp]
      rw [concat_snd_range_left (γ := γ) (δ := δ) (r := (i : ℕ))
        (hr := by intro hiv; omega) (hrn1 := by omega)]]
    simpa using hγ ⟨(i : ℕ), h1⟩
  · by_cases h2 : (i : ℕ) = n
    · have hgt0 : 0 < δ.2 0 := by
        rw [show (0 : Fin (m + 1)) = (⟨0, by omega⟩ : Fin m).castSucc by
          apply Fin.ext
          simp]
        exact hδ ⟨0, by omega⟩
      have hseam : (concat γ δ).2 i.castSucc = γ.2 (Fin.last n) + δ.2 0 := by
        rw [show (i.castSucc : Fin (n + m + 1)) = ⟨n, by omega⟩ by
          apply Fin.ext
          simp [h2]]
        rw [concat_snd_boundary (γ := γ) (δ := δ)]
      rw [hseam]
      exact add_pos_of_nonneg_of_pos (NNReal.coe_nonneg _) hgt0
    · have hgtn : n + 1 ≤ (i : ℕ) := by omega
      let r : ℕ := (i : ℕ) - (n + 1)
      have hr : r < m := by omega
      have hseam : (concat γ δ).2 i.castSucc = δ.2 (⟨r, hr⟩ : Fin m).succ := by
        have hcast : (i.castSucc : Fin (n + m + 1)) = ⟨n + 1 + r, by omega⟩ := by
          apply Fin.ext
          simp [r]
          omega
        conv_lhs => rw [hcast]
        rw [concat_snd_range_right (γ := γ) (δ := δ) (r := r) (hr := hr)]
      rw [hseam]
      have hr1 : r + 1 < m := by omega
      rw [show (⟨r, hr⟩ : Fin m).succ = (⟨r + 1, by omega⟩ : Fin m).castSucc by
        apply Fin.ext
        simp]
      exact hδ ⟨r + 1, by omega⟩

/-- Concatenating two valid charts is valid for the summed horizon, provided
each constituent's full holding time fits its own horizon.  The extra holding
time bounds are genuinely needed: `IsValid` only bounds the holding intervals
strictly before the final one, while the concatenated jump time adds the
terminal (and seam) intervals. -/
theorem isValid_concat {T₁ T₂ : NNReal} {n m : ℕ}
    (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    (hγ : IsValid T₁ γ) (hδ : IsValid T₂ δ)
    (hγtotal : γ.totalHoldingTime ≤ T₁)
    (hδtotal : δ.totalHoldingTime ≤ T₂) :
    IsValid (T₁ + T₂) (concat γ δ) := by
  constructor
  · exact concat_holding_pos hγ.1 hδ.1
  · calc
      jumpTimes (concat γ δ) (Fin.last (n + m)) ≤ (totalHoldingTime (concat γ δ) : ℝ) :=
        jumpTimes_le_totalHoldingTime (concat γ δ) (Fin.last (n + m))
      _ = (γ.totalHoldingTime : ℝ) + (δ.totalHoldingTime : ℝ) := by
        rw [← NNReal.coe_add]
        exact_mod_cast totalHoldingTime_concat γ δ
      _ ≤ (T₁ : ℝ) + (T₂ : ℝ) := by
        exact_mod_cast add_le_add hγtotal hδtotal
      _ = ((T₁ + T₂ : NNReal) : ℝ) := by
        rw [NNReal.coe_add]

/-- The concatenation starts at the same state as the prefix, so both
real-time trajectories agree at time zero. -/
theorem trajectory_concat_zero {n m : ℕ} {γ : JumpPath Ω n} {δ : JumpPath Ω m}
    (hγ : ∀ i : Fin n, 0 < γ.2 i.castSucc)
    (hδ : ∀ i : Fin m, 0 < δ.2 i.castSucc) :
    trajectory (concat γ δ) 0 = trajectory γ 0 := by
  rw [trajectory_zero_of_pos (concat γ δ) (concat_holding_pos hγ hδ),
    trajectory_zero_of_pos γ hγ]
  rw [show (concat γ δ).1 (0 : Fin (n + m + 1)) = γ.1 (0 : Fin (n + 1)) by
    change Fin.append (m := n + 1) (n := m) γ.1 (δ.1 ∘ Fin.succ)
        (Fin.cast (by omega) (0 : Fin (n + m + 1))) = γ.1 (0 : Fin (n + 1))
    rw [show (Fin.cast (by omega) (0 : Fin (n + m + 1)) : Fin (n + 1 + m)) =
        Fin.castAdd m (0 : Fin (n + 1)) by
      apply Fin.ext
      simp]
    rw [Fin.append_left (u := γ.1) (v := δ.1 ∘ Fin.succ) (i := (0 : Fin (n + 1)))]
]

/-- The state at every position of a concatenation, expressed by the position
of the index. -/
private lemma concat_fst_value_at {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m)
    {r : ℕ} (hr : r < n + m + 1) :
    (concat γ δ).1 ⟨r, hr⟩ =
      if h : r < n + 1 then γ.1 ⟨r, h⟩ else δ.1 ⟨r - n, by omega⟩ := by
  by_cases h : r < n + 1
  · have hidx : (⟨r, hr⟩ : Fin (n + m + 1)) =
        Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.castAdd m (⟨r, h⟩ : Fin (n + 1))) := by
      apply Fin.ext
      simp
    rw [hidx, concat_fst_castAdd]
    simp [h]
  · have hrm : r - (n + 1) < m := by omega
    have hidx : (⟨r, hr⟩ : Fin (n + m + 1)) =
        Fin.cast (by omega : (n + 1) + m = n + m + 1)
          (Fin.natAdd (n + 1) (⟨r - (n + 1), hrm⟩ : Fin m)) := by
      apply Fin.ext
      simp
      omega
    rw [hidx, concat_fst_natAdd]
    rw [show (⟨r - (n + 1), hrm⟩ : Fin m).succ = ⟨r - n, by omega⟩ by
      apply Fin.ext
      simp
      omega]
    simp [h]

/-- Unfold one successor step of the real-time trajectory. -/
private lemma trajectory_succ {k : ℕ} (γ : JumpPath Ω (k + 1)) (t : ℝ) :
    trajectory γ t =
      if jumpTimes γ (Fin.last (k + 1)) ≤ t then γ.1 (Fin.last (k + 1))
      else trajectory (dropLast γ) t := rfl

/-- Dropping the final state preserves all earlier jump times. -/
theorem jumpTimes_dropLast {n : ℕ} (γ : JumpPath Ω (n + 1)) (k : Fin (n + 1)) :
    jumpTimes (dropLast γ) k = jumpTimes γ k.castSucc := by
  unfold jumpTimes
  rw [sum_Iio_eq_sum_range (a := k)
      (f := fun i : Fin (n + 1) => ((dropLast γ).2 i : ℝ))]
  rw [sum_Iio_eq_sum_range (a := k.castSucc)
      (f := fun i : Fin (n + 2) => (γ.2 i : ℝ))]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r < n + 1 := by
    exact lt_trans (Finset.mem_range.mp hr) k.isLt
  rw [dif_pos hrn, dif_pos (by omega : r < n + 2)]
  rfl

/-- Dropping the final state commutes with concatenation when the suffix has
at least one jump. -/
theorem dropLast_concat {n m : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω (m + 1)) :
    @dropLast Ω (n + m) (@concat Ω n (m + 1) γ δ) =
      @concat Ω n m γ (@dropLast Ω m δ) := by
  apply Prod.ext
  · funext i
    obtain ⟨r, hr⟩ := i
    rw [show (@dropLast Ω (n + m) (@concat Ω n (m + 1) γ δ)).1 ⟨r, hr⟩ =
        (@concat Ω n (m + 1) γ δ).1 ⟨r, by omega⟩ from rfl]
    rw [concat_fst_value_at, concat_fst_value_at]
    by_cases h : r < n + 1
    · simp [h]
    · simp only [dif_neg h]
      rfl
  · funext i
    obtain ⟨r, hr⟩ := i
    rw [show (@dropLast Ω (n + m) (@concat Ω n (m + 1) γ δ)).2 ⟨r, hr⟩ =
        (@concat Ω n (m + 1) γ δ).2 ⟨r, by omega⟩ from rfl]
    rw [concat_snd_value_at, concat_snd_value_at]
    by_cases hlt : r < n
    · simp [hlt]
    · by_cases heq : r = n
      · subst r
        have hzero : (dropLast δ).2 0 = δ.2 0 := by
          apply congrArg δ.2
          apply Fin.ext
          simp
        simp [hzero]
      · simp only [dif_neg hlt, dif_neg heq]
        change δ.2 ⟨r - n, by omega⟩ =
          δ.2 (⟨r - n, by omega⟩ : Fin (m + 1)).castSucc
        apply congrArg δ.2
        apply Fin.ext
        simp

/-- The trajectory depends only on the state sequence and jump times. -/
theorem trajectory_congr : ∀ {n : ℕ} (γ γ' : JumpPath Ω n),
    γ.1 = γ'.1 → (∀ k, jumpTimes γ k = jumpTimes γ' k) →
    ∀ t : ℝ, trajectory γ t = trajectory γ' t
  | 0, γ, γ', hstates, _, t => by
      simp only [trajectory]
      rw [hstates]
  | n + 1, γ, γ', hstates, htimes, t => by
      rw [trajectory_succ γ t, trajectory_succ γ' t,
        htimes (Fin.last (n + 1)), hstates]
      by_cases h : jumpTimes γ' (Fin.last (n + 1)) ≤ t
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        exact trajectory_congr (dropLast γ) (dropLast γ')
          (funext fun i => congrFun hstates i.castSucc)
          (fun k => by rw [jumpTimes_dropLast, jumpTimes_dropLast, htimes]) t

private lemma concat_zero_states {n : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω 0) :
    (concat γ δ).1 = γ.1 := by
  funext i
  obtain ⟨r, hr⟩ := i
  rw [concat_fst_value_at]
  simp [show r < n + 1 by omega]

private lemma jumpTimes_concat_zero_right {n : ℕ} (γ : JumpPath Ω n)
    (δ : JumpPath Ω 0) (k : Fin (n + 1)) :
    jumpTimes (concat γ δ) k = jumpTimes γ k := by
  unfold jumpTimes
  rw [sum_Iio_eq_sum_range (a := k)
      (f := fun i : Fin (n + 1) => ((concat γ δ).2 i : ℝ))]
  rw [sum_Iio_eq_sum_range (a := k)
      (f := fun i : Fin (n + 1) => (γ.2 i : ℝ))]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r < n := by
    have hrk := Finset.mem_range.mp hr
    omega
  rw [dif_pos (by omega : r < n + 1), dif_pos (by omega : r < n + 1)]
  rw [concat_snd_value_at]
  simp [hrn]

private lemma trajectory_concat_zero_right {n : ℕ} (γ : JumpPath Ω n)
    (δ : JumpPath Ω 0) (t : ℝ) :
    trajectory (concat γ δ) t = trajectory γ t := by
  exact trajectory_congr (concat γ δ) γ (concat_zero_states γ δ)
    (jumpTimes_concat_zero_right γ δ) t

private lemma jumpTimes_concat_last {n m : ℕ} (γ : JumpPath Ω n)
    (δ : JumpPath Ω (m + 1)) :
    jumpTimes (concat γ δ) (Fin.last (n + m + 1)) =
      (γ.totalHoldingTime : ℝ) + jumpTimes δ (Fin.last (m + 1)) := by
  change jumpTimes (concat γ δ) (Fin.last (n + (m + 1))) =
    (γ.totalHoldingTime : ℝ) + jumpTimes δ (Fin.last (m + 1))
  have hj : Fin.last (m + 1) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hidx : Fin.last (n + (m + 1)) =
      Fin.cast (by omega : n + ((m + 1) + 1) = n + (m + 1) + 1)
        (Fin.natAdd n (Fin.last (m + 1))) := by
    apply Fin.ext
    simp
  rw [hidx]
  exact jumpTimes_concat_right γ δ (Fin.last (m + 1)) hj

/-- After the prefix has exhausted its total holding time, the concatenated
trajectory follows the suffix on the shifted clock. -/
theorem trajectory_concat_right : ∀ {m n : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m),
    γ.1 (Fin.last n) = δ.1 0 →
    ∀ t : ℝ, (γ.totalHoldingTime : ℝ) ≤ t →
    trajectory (concat γ δ) t = trajectory δ (t - (γ.totalHoldingTime : ℝ))
  | 0, n, γ, δ, hmatch, t, ht => by
      rw [trajectory_concat_zero_right γ δ t]
      rw [show trajectory δ (t - (γ.totalHoldingTime : ℝ)) = δ.1 0 from rfl, ← hmatch]
      exact trajectory_eq_terminal_of_last_le γ t
        (le_trans (jumpTimes_le_totalHoldingTime γ (Fin.last n)) ht)
  | m + 1, n, γ, δ, hmatch, t, ht => by
      change (if jumpTimes (@concat Ω n (m + 1) γ δ) (Fin.last (n + m + 1)) ≤ t then
          (@concat Ω n (m + 1) γ δ).1 (Fin.last (n + m + 1))
        else trajectory (@dropLast Ω (n + m) (@concat Ω n (m + 1) γ δ)) t) =
        trajectory δ (t - (γ.totalHoldingTime : ℝ))
      rw [trajectory_succ δ (t - (γ.totalHoldingTime : ℝ)),
        jumpTimes_concat_last γ δ]
      by_cases h : jumpTimes δ (Fin.last (m + 1)) ≤
          t - (γ.totalHoldingTime : ℝ)
      · rw [if_pos (by linarith), if_pos h]
        exact concat_state_last γ δ hmatch
      · rw [if_neg (by intro hc; exact h (by linarith)), if_neg h, dropLast_concat]
        exact trajectory_concat_right γ (dropLast δ) hmatch t ht

/-- Strictly before the prefix's total holding time the concatenated
trajectory is the prefix's own. -/
theorem trajectory_concat_left : ∀ {m n : ℕ} (γ : JumpPath Ω n) (δ : JumpPath Ω m),
    ∀ t : ℝ, t < (γ.totalHoldingTime : ℝ) →
    trajectory (concat γ δ) t = trajectory γ t
  | 0, n, γ, δ, t, _ => trajectory_concat_zero_right γ δ t
  | m + 1, n, γ, δ, t, ht => by
      change (if jumpTimes (@concat Ω n (m + 1) γ δ) (Fin.last (n + m + 1)) ≤ t then
          (@concat Ω n (m + 1) γ δ).1 (Fin.last (n + m + 1))
        else trajectory (@dropLast Ω (n + m) (@concat Ω n (m + 1) γ δ)) t) = trajectory γ t
      rw [if_neg (by
        rw [jumpTimes_concat_last γ δ]
        have h0 : 0 ≤ jumpTimes δ (Fin.last (m + 1)) := jumpTimes_nonneg δ _
        linarith)]
      rw [dropLast_concat]
      exact trajectory_concat_left γ (dropLast δ) t ht

end JumpPath

namespace FullPath

variable {Ω : Type u}

/-- Glue two complete finite-jump paths into one global real-time path.  The
boundary state of the suffix is merged with the final state of the prefix. -/
def concat (γ δ : FullPath Ω) : FullPath Ω :=
  ⟨γ.1 + δ.1, JumpPath.concat γ.2 δ.2⟩

/-- The jump-free complete path resting at `x`. -/
def rest (x : Ω) : FullPath Ω :=
  ⟨0, fun _ => x, fun _ => 0⟩

@[simp]
theorem initialState_rest (x : Ω) : initialState (rest x) = x := rfl

@[simp]
theorem terminalState_rest (x : Ω) : terminalState (rest x) = x := rfl

/-- The total holding time of a complete path. -/
def totalHoldingTime : FullPath Ω → NNReal
  | ⟨_, γ⟩ => γ.totalHoldingTime

@[simp]
theorem totalHoldingTime_rest (x : Ω) : totalHoldingTime (rest x) = 0 := by
  simp [totalHoldingTime, rest, JumpPath.totalHoldingTime]

/-- Complete-path concatenation adds total holding times. -/
theorem totalHoldingTime_concat (γ δ : FullPath Ω) :
    totalHoldingTime (concat γ δ) = totalHoldingTime γ + totalHoldingTime δ := by
  rcases γ with ⟨n, γ⟩
  rcases δ with ⟨m, δ⟩
  exact JumpPath.totalHoldingTime_concat γ δ

/-- Complete-path concatenation preserves the prefix's initial state. -/
theorem initialState_concat (γ δ : FullPath Ω) :
    initialState (concat γ δ) = initialState γ := by
  rcases γ with ⟨n, γ⟩
  rcases δ with ⟨m, δ⟩
  exact JumpPath.concat_state_zero γ δ

/-- A matched concatenation ends at the suffix's terminal state. -/
theorem terminalState_concat (γ δ : FullPath Ω)
    (hmatch : terminalState γ = initialState δ) :
    terminalState (concat γ δ) = terminalState δ := by
  rcases γ with ⟨n, γ⟩
  rcases δ with ⟨m, δ⟩
  exact JumpPath.concat_state_last γ δ hmatch

/-- Valid complete paths concatenate over the summed horizon when each full
holding time fits its constituent horizon. -/
theorem isValid_concat {T₁ T₂ : NNReal} {γ δ : FullPath Ω}
    (hγ : IsValid T₁ γ) (hδ : IsValid T₂ δ)
    (hγtotal : totalHoldingTime γ ≤ T₁)
    (hδtotal : totalHoldingTime δ ≤ T₂) :
    IsValid (T₁ + T₂) (concat γ δ) := by
  rcases γ with ⟨n, γ⟩
  rcases δ with ⟨m, δ⟩
  exact JumpPath.isValid_concat γ δ hγ hδ hγtotal hδtotal

/-- Before the prefix's total holding time, a complete-path concatenation
follows the prefix. -/
theorem trajectory_concat_left (γ δ : FullPath Ω) {t : ℝ}
    (ht : t < (totalHoldingTime γ : ℝ)) :
    trajectory (concat γ δ) t = trajectory γ t := by
  rcases γ with ⟨n, γ⟩
  rcases δ with ⟨m, δ⟩
  exact JumpPath.trajectory_concat_left γ δ t ht

/-- From the prefix's total holding time onward, a matched complete-path
concatenation follows the suffix on the shifted clock. -/
theorem trajectory_concat_right (γ δ : FullPath Ω)
    (hmatch : terminalState γ = initialState δ) {t : ℝ}
    (ht : (totalHoldingTime γ : ℝ) ≤ t) :
    trajectory (concat γ δ) t = trajectory δ (t - (totalHoldingTime γ : ℝ)) := by
  rcases γ with ⟨n, γ⟩
  rcases δ with ⟨m, δ⟩
  exact JumpPath.trajectory_concat_right γ δ hmatch t ht

/-- With a fixed prefix, concatenating a complete path is measurable in the
suffix. -/
private theorem measurable_concat_fixed_fst [MeasurableSpace Ω] {n m : ℕ}
    (γ : JumpPath Ω n) :
    Measurable (fun δ : JumpPath Ω m => JumpPath.concat γ δ) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    by_cases h : (i : ℕ) < n + 1
    · let i0 : Fin (n + 1) := ⟨i, h⟩
      have hcast : (Fin.cast (by omega) i : Fin (n + 1 + m)) = Fin.castAdd m i0 := by
        apply Fin.ext
        simp [i0]
      have hterm :
        (fun δ : JumpPath Ω m =>
          Fin.append (m := n + 1) (n := m) γ.1 (δ.1 ∘ Fin.succ) (Fin.cast (by omega) i)) =
          fun _ : JumpPath Ω m => γ.1 i0 := by
        funext δ
        rw [hcast]
        exact Fin.append_left (u := γ.1) (v := δ.1 ∘ Fin.succ) (i := i0)
      rw [hterm]
      exact measurable_const
    · have hlt : i.val - (n + 1) < m := by
        have hiv : (i : ℕ) < n + m + 1 := i.isLt
        omega
      let j0 : Fin m := ⟨i.val - (n + 1), hlt⟩
      have hcast : (Fin.cast (by omega) i : Fin (n + 1 + m)) = Fin.natAdd (n + 1) j0 := by
        apply Fin.ext
        simp [j0]
        omega
      have hterm :
        (fun δ : JumpPath Ω m =>
          Fin.append (m := n + 1) (n := m) γ.1 (δ.1 ∘ Fin.succ) (Fin.cast (by omega) i)) =
          fun δ : JumpPath Ω m => (δ.1 ∘ Fin.succ) j0 := by
        funext δ
        rw [hcast]
        exact Fin.append_right (u := γ.1) (v := δ.1 ∘ Fin.succ) (i := j0)
      rw [hterm]
      exact ((measurable_pi_apply (Fin.succ j0)).comp measurable_fst)
  · rw [measurable_pi_iff]
    intro i
    by_cases h : (i : ℕ) < n + 1
    · let i0 : Fin (n + 1) := ⟨i, h⟩
      have hcast : (Fin.cast (by omega) i : Fin (n + 1 + m)) = Fin.castAdd m i0 := by
        apply Fin.ext
        simp [i0]
      have hterm :
        (fun δ : JumpPath Ω m =>
          Fin.append (m := n + 1) (n := m)
            (fun j : Fin (n + 1) =>
              if j = Fin.last n then γ.2 j + δ.2 0 else γ.2 j)
            (δ.2 ∘ Fin.succ) (Fin.cast (by omega) i)) =
          fun δ : JumpPath Ω m =>
            (if i0 = Fin.last n then γ.2 i0 + δ.2 0 else γ.2 i0) := by
        funext δ
        rw [hcast]
        exact Fin.append_left (u := (fun j : Fin (n + 1) =>
          if j = Fin.last n then γ.2 j + δ.2 0 else γ.2 j)) (v := δ.2 ∘ Fin.succ) (i := i0)
      rw [hterm]
      by_cases hseam : i0 = Fin.last n
      · have hfun : (fun δ : JumpPath Ω m =>
            (if i0 = Fin.last n then γ.2 i0 + δ.2 0 else γ.2 i0)) =
            fun δ : JumpPath Ω m => γ.2 i0 + δ.2 0 := by
          funext δ
          simp [hseam]
        rw [hfun]
        exact (Measurable.add (measurable_const :
            Measurable (fun _ : JumpPath Ω m => (γ.2 i0 : NNReal)))
          ((measurable_pi_apply (0 : Fin (m + 1))).comp measurable_snd))
      · have hfun : (fun δ : JumpPath Ω m =>
            (if i0 = Fin.last n then γ.2 i0 + δ.2 0 else γ.2 i0)) =
            fun _ : JumpPath Ω m => γ.2 i0 := by
          funext δ
          rw [if_neg hseam]
        rw [hfun]
        exact measurable_const
    · have hlt : i.val - (n + 1) < m := by
        have hiv : (i : ℕ) < n + m + 1 := i.isLt
        omega
      let j0 : Fin m := ⟨i.val - (n + 1), hlt⟩
      have hcast : (Fin.cast (by omega) i : Fin (n + 1 + m)) = Fin.natAdd (n + 1) j0 := by
        apply Fin.ext
        simp [j0]
        omega
      have hterm :
        (fun δ : JumpPath Ω m =>
          Fin.append (m := n + 1) (n := m)
            (fun j : Fin (n + 1) =>
              if j = Fin.last n then γ.2 j + δ.2 0 else γ.2 j)
            (δ.2 ∘ Fin.succ) (Fin.cast (by omega) i)) =
          fun δ : JumpPath Ω m => (δ.2 ∘ Fin.succ) j0 := by
        funext δ
        rw [hcast]
        exact Fin.append_right (u := (fun j : Fin (n + 1) =>
          if j = Fin.last n then γ.2 j + δ.2 0 else γ.2 j)) (v := δ.2 ∘ Fin.succ) (i := j0)
      rw [hterm]
      exact ((measurable_pi_apply (Fin.succ j0)).comp measurable_snd)
/-- Concatenating a complete path with a fixed prefix is measurable in the
suffix. -/
theorem measurable_concat [MeasurableSpace Ω] (γ : FullPath Ω) :
    Measurable (fun δ : FullPath Ω => concat γ δ) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro m
  change MeasurableSet
    ((fun δ' : JumpPath Ω m => Sigma.mk (γ.1 + m) (JumpPath.concat γ.2 δ')) ⁻¹' s)
  exact measurable_concat_fixed_fst γ.2 (FullPath.measurable_mk (γ.1 + m) hs)

end FullPath

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
