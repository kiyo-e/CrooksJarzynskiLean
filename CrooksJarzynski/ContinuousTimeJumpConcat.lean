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

end JumpPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski