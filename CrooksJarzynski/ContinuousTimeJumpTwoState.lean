/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpSimplex
import CrooksJarzynski.ContinuousTimeJumpRateFull
import Mathlib.Probability.UniformOn

/-!
# A concrete symmetric two-state continuous-time Markov chain

This module instantiates the fixed-horizon simplex reference and the rate-level
Crooks theorem for the unit-rate chain on two states.  At each jump the state is
flipped, and the escape rate is one.  The initial state is uniform.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- The state space of the concrete continuous-time chain. -/
inductive State
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace State := ⊤

/-- The unique state different from the current state. -/
def flip : State → State
  | .zero => .one
  | .one => .zero

@[simp]
theorem flip_flip (x : State) : flip (flip x) = x := by
  cases x <;> rfl

@[simp]
theorem flip_ne (x : State) : flip x ≠ x := by
  cases x <;> decide

/-- Iteration of the deterministic state flip. -/
def iterateFlip : ℕ → State → State
  | 0, x => x
  | k + 1, x => flip (iterateFlip k x)

@[simp]
theorem iterateFlip_zero (x : State) : iterateFlip 0 x = x := rfl

@[simp]
theorem iterateFlip_succ (k : ℕ) (x : State) :
    iterateFlip (k + 1) x = flip (iterateFlip k x) := rfl

/-- The state sequence determined by an initial state and `n` flips. -/
def alternatingStates (n : ℕ) (x : State) : Fin (n + 1) → State :=
  fun i => iterateFlip i.1 x

/-- A state sequence changes to the other state at every jump. -/
def Alternates {n : ℕ} (states : Fin (n + 1) → State) : Prop :=
  ∀ i : Fin n, states i.succ = flip (states i.castSucc)

/-- The explicitly generated sequence alternates. -/
theorem alternatingStates_alternates (n : ℕ) (x : State) :
    Alternates (alternatingStates n x) := by
  intro i
  simp [alternatingStates]

/-- Alternation is a measurable condition on a finite state sequence. -/
theorem measurableSet_alternates {n : ℕ} :
    MeasurableSet {states : Fin (n + 1) → State | Alternates states} := by
  exact MeasurableSet.of_discrete

/-- Reversing an alternating state sequence preserves alternation. -/
theorem alternates_reverse {n : ℕ} {states : Fin (n + 1) → State}
    (h : Alternates states) : Alternates (fun i => states i.rev) := by
  intro i
  change states i.succ.rev = flip (states i.castSucc.rev)
  rw [Fin.rev_succ, Fin.rev_castSucc]
  have hi := h i.rev
  simpa using (congrArg flip hi).symm

/-- The uniform initial state distribution. -/
noncomputable def initialStateLaw : Measure State :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance instIsProbabilityMeasureInitialStateLaw :
    IsProbabilityMeasure initialStateLaw := by
  unfold initialStateLaw
  infer_instance

/-- The law of the complete alternating state sequence in the `n`-jump sector. -/
noncomputable def alternatingStateLaw (n : ℕ) :
    Measure (Fin (n + 1) → State) :=
  initialStateLaw.map (alternatingStates n)

noncomputable instance instIsProbabilityMeasureAlternatingStateLaw (n : ℕ) :
    IsProbabilityMeasure (alternatingStateLaw n) := by
  unfold alternatingStateLaw
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- The alternating state law is concentrated on alternating sequences. -/
theorem alternatingStateLaw_ae_alternates (n : ℕ) :
    ∀ᵐ states ∂alternatingStateLaw n, Alternates states := by
  unfold alternatingStateLaw
  rw [ae_map_iff Measurable.of_discrete.aemeasurable measurableSet_alternates]
  exact ae_of_all initialStateLaw fun x => alternatingStates_alternates n x

/-- The geometric mass of the horizon-`T`, `n`-jump holding-time simplex. -/
noncomputable def simplexMass (T : NNReal) (n : ℕ) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞)

/-- A concrete, nonzero, fixed-horizon and reversal-invariant sector reference. -/
noncomputable def sectorReference (T : NNReal) (n : ℕ) :
    Measure (JumpPath State n) :=
  Simplex.reference T (alternatingStateLaw n) (simplexMass T n)

/-- The sector reference is reversal invariant. -/
theorem map_sectorReference_reverse (T : NNReal) (n : ℕ) :
    (sectorReference T n).map JumpPath.reverse = sectorReference T n := by
  exact Simplex.map_reference_reverse T (alternatingStateLaw n) (simplexMass T n)

/-- The sector reference has exactly the simplex volume as total mass. -/
theorem sectorReference_univ (T : NNReal) (n : ℕ) :
    sectorReference T n Set.univ = simplexMass T n := by
  exact Simplex.reference_univ T (alternatingStateLaw n) (simplexMass T n)

/-- For a positive horizon, every sector reference is nonzero. -/
theorem sectorReference_ne_zero {T : NNReal} (hT : 0 < T) (n : ℕ) :
    sectorReference T n ≠ 0 := by
  apply Simplex.reference_ne_zero T (alternatingStateLaw n)
  unfold simplexMass
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hT.ne'
  exact ne_of_gt (ENNReal.div_pos (pow_ne_zero n hT0) (by simp))

/-- The sector reference is concentrated on paths of duration `T`. -/
theorem sectorReference_ae_horizon (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂sectorReference T n,
      γ ∈ JumpPath.horizonSet (Ω := State) (n := n) T :=
  Simplex.reference_ae_horizon T (alternatingStateLaw n) (simplexMass T n)

/-- The unit escape rate. -/
def escapeRate {n : ℕ} : Fin (n + 1) → State → NNReal :=
  fun _ _ => 1

/-- The unit rate for the unique allowed state flip. -/
def jumpRate {n : ℕ} : Fin n → State → State → NNReal :=
  fun _ x y => if y = flip x then 1 else 0

/-- The two-state jump rates are symmetric under reversal. -/
theorem jumpRate_symm {n : ℕ} (i : Fin n) (x y : State) :
    jumpRate i x y = jumpRate i y x := by
  cases x <;> cases y <;> rfl

/-- Evaluation of a discrete jump-rate factor along a path is measurable. -/
@[fun_prop]
theorem measurable_jumpWeight_eval {n : ℕ} (i : Fin n)
    (a b : Fin (n + 1)) :
    Measurable (fun γ : JumpPath State n =>
      JumpPath.jumpWeightOfRate (jumpRate (n := n)) i (γ.1 a) (γ.1 b)) := by
  unfold JumpPath.jumpWeightOfRate
  exact (Measurable.of_discrete :
    Measurable (fun states : Fin (n + 1) → State =>
      (jumpRate i (states a) (states b) : ℝ≥0∞))).comp measurable_fst

/-- There is no thermodynamic work in this equilibrium example. -/
def boundaryWork : State → State → ℝ≥0∞ :=
  fun _ _ => 1

/-- There is no jump work in this equilibrium example. -/
def jumpWork {n : ℕ} : Fin n → State → State → ℝ≥0∞ :=
  fun _ _ _ => 1

/-- The initial and final density factors relative to the state-sequence
reference are both one. -/
def endpointWeight : State → ℝ≥0∞ :=
  fun _ => 1

/-- The rate density of the two-state model is measurable. -/
theorem measurable_rateDensity (T : NNReal) (n : ℕ) :
    Measurable
      (JumpPath.rateDensity endpointWeight
        (escapeRate (n := n)) (jumpRate (n := n))) := by
  unfold JumpPath.rateDensity JumpPath.density
    JumpPath.holdingWeightOfEscapeRate endpointWeight escapeRate
  fun_prop

/-- The aligned reverse rate density is measurable. -/
theorem measurable_alignedReverseRateDensity (T : NNReal) (n : ℕ) :
    Measurable
      (JumpPath.alignedReverseRateDensity endpointWeight
        (escapeRate (n := n)) (jumpRate (n := n))) := by
  unfold JumpPath.alignedReverseRateDensity JumpPath.alignedReverseDensity
    JumpPath.holdingWeightOfEscapeRate endpointWeight escapeRate
  fun_prop

/-- The work weight is the constant one function. -/
theorem rateWorkWeight_eq_one {n : ℕ} (γ : JumpPath State n) :
    JumpPath.rateWorkWeight boundaryWork (jumpWork (n := n)) γ = 1 := by
  simp [JumpPath.rateWorkWeight, JumpPath.factorizedWorkWeight,
    boundaryWork, jumpWork]

/-- The work weight is measurable. -/
theorem measurable_rateWorkWeight (n : ℕ) :
    Measurable (JumpPath.rateWorkWeight boundaryWork (jumpWork (n := n))) := by
  simpa only [funext fun γ => rateWorkWeight_eq_one γ] using
    (measurable_const : Measurable (fun _ : JumpPath State n => (1 : ℝ≥0∞)))

/-- Fixed-sector Crooks relation for the symmetric two-state unit-rate chain. -/
theorem sector_crooks (T : NNReal) (n : ℕ) :
    CrooksRelation
      (pathMeasure (sectorReference T n)
        (JumpPath.rateDensity endpointWeight escapeRate jumpRate))
      (JumpPath.timeReversedMeasure
        (pathMeasure (sectorReference T n)
          (JumpPath.reverseRateDensity endpointWeight escapeRate jumpRate)))
      (JumpPath.rateWorkWeight boundaryWork jumpWork) 1 := by
  apply JumpPath.crooks_of_rate_local_balance
    (sectorReference T n) endpointWeight endpointWeight
    escapeRate escapeRate jumpRate jumpRate
    boundaryWork jumpWork 1
  · exact map_sectorReference_reverse T n
  · exact measurable_rateDensity T n
  · exact measurable_alignedReverseRateDensity T n
  · exact measurable_rateWorkWeight n
  · intro x y
    simp [endpointWeight, boundaryWork]
  · intro i x
    rfl
  · intro i x y
    simp [JumpPath.jumpWeightOfRate, jumpWork, jumpRate_symm]

/-- Full finite-jump Crooks relation obtained by summing every two-state sector. -/
theorem full_crooks (T : NNReal) :
    CrooksRelation
      (FullPath.measure
        (FullPath.forwardRateSectorMeasure (sectorReference T) endpointWeight
          (fun _ => escapeRate) (fun _ => jumpRate)))
      (FullPath.measure
        (FullPath.reversedRateSectorMeasure (sectorReference T) endpointWeight
          (fun _ => escapeRate) (fun _ => jumpRate)))
      (FullPath.weight
        (FullPath.rateWorkWeightFamily boundaryWork (fun _ => jumpWork)))
      1 := by
  apply FullPath.crooks_of_rate_local_balance
    (sectorReference T) endpointWeight endpointWeight
    (fun _ => escapeRate) (fun _ => escapeRate)
    (fun _ => jumpRate) (fun _ => jumpRate)
    boundaryWork (fun _ => jumpWork) 1
  · exact map_sectorReference_reverse T
  · exact measurable_rateDensity T
  · exact measurable_alignedReverseRateDensity T
  · exact measurable_rateWorkWeight
  · intro x y
    simp [endpointWeight, boundaryWork]
  · intro n i x
    rfl
  · intro n i x y
    simp [JumpPath.jumpWeightOfRate, jumpWork, jumpRate_symm]

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
