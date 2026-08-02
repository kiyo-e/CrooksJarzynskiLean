/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDriven
import CrooksJarzynski.ContinuousTimeJumpSimplexReversal

/-!
# Rate detailed balance for driven jump windows

This module records the division-free finite-state detailed-balance hypothesis
used by every driven window and proves the finite-path telescoping identity for
its jump-rate factors. It also proves that the unsymmetrized finite-state
counting chart is already invariant under path reversal, and exposes finite-sum
partition functions for the counting-measure Gibbs specialization used by
finite-state protocols.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω]

/-- Division-free detailed balance for nonnegative state weights and jump
rates. -/
def IsDetailedBalanceWeight
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞) : Prop :=
  ∀ x y,
    weight x * (G.jumpRate x y : ℝ≥0∞) =
      weight y * (G.jumpRate y x : ℝ≥0∞)

/-- Instantaneous Gibbs detailed balance for an energy landscape. -/
def IsGibbsDetailedBalance
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ) : Prop :=
  IsDetailedBalanceWeight G
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x)))

/-- Detailed balance telescopes along every finite state sequence: the forward
jump-rate product weighted at the initial state equals the reversed jump-rate
product weighted at the terminal state. -/
theorem weight_mul_jumpProduct_eq_reverse
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞)
    (hbalance : G.IsDetailedBalanceWeight weight)
    {n : ℕ} (states : Fin (n + 1) → Ω) :
    weight (states 0) * G.jumpProduct states =
      weight (states (Fin.last n)) *
        ∏ i : Fin n,
          (G.jumpRate (states i.succ) (states i.castSucc) : ℝ≥0∞) := by
  induction n with
  | zero =>
      simp [jumpProduct]
  | succ n ih =>
      let forwardTail : ℝ≥0∞ :=
        ∏ i : Fin n,
          (G.jumpRate (states i.succ.castSucc)
            (states i.succ.succ) : ℝ≥0∞)
      let reverseTail : ℝ≥0∞ :=
        ∏ i : Fin n,
          (G.jumpRate (states i.succ.succ)
            (states i.succ.castSucc) : ℝ≥0∞)
      have htail :
          weight (states 1) * forwardTail =
            weight (states (Fin.last (n + 1))) * reverseTail := by
        simpa [forwardTail, reverseTail, jumpProduct, Fin.succ_last] using
          ih (fun i : Fin (n + 1) => states i.succ)
      rw [jumpProduct, Fin.prod_univ_succ, Fin.prod_univ_succ]
      change
        weight (states 0) *
            ((G.jumpRate (states 0) (states 1) : ℝ≥0∞) * forwardTail) =
          weight (states (Fin.last (n + 1))) *
            ((G.jumpRate (states 1) (states 0) : ℝ≥0∞) * reverseTail)
      calc
        weight (states 0) *
              ((G.jumpRate (states 0) (states 1) : ℝ≥0∞) * forwardTail) =
            (weight (states 0) *
              (G.jumpRate (states 0) (states 1) : ℝ≥0∞)) *
                forwardTail := by ac_rfl
        _ = (weight (states 1) *
              (G.jumpRate (states 1) (states 0) : ℝ≥0∞)) *
                forwardTail := by
              rw [hbalance]
        _ = (G.jumpRate (states 1) (states 0) : ℝ≥0∞) *
              (weight (states 1) * forwardTail) := by ac_rfl
        _ = (G.jumpRate (states 1) (states 0) : ℝ≥0∞) *
              (weight (states (Fin.last (n + 1))) * reverseTail) := by
              rw [htail]
        _ = weight (states (Fin.last (n + 1))) *
              ((G.jumpRate (states 1) (states 0) : ℝ≥0∞) *
                reverseTail) := by ac_rfl

/-- Gibbs detailed balance gives the pathwise jump-product identity in the
exact Boltzmann-weight form used by driven windows. -/
theorem gibbsWeight_mul_jumpProduct_eq_reverse
    (G : FiniteJumpGenerator Ω) (β : ℝ) (energy : Ω → ℝ)
    (hbalance : G.IsGibbsDetailedBalance β energy)
    {n : ℕ} (states : Fin (n + 1) → Ω) :
    ENNReal.ofReal (Real.exp (-β * energy (states 0))) *
        G.jumpProduct states =
      ENNReal.ofReal
          (Real.exp (-β * energy (states (Fin.last n)))) *
        ∏ i : Fin n,
          (G.jumpRate (states i.succ) (states i.castSucc) : ℝ≥0∞) := by
  exact G.weight_mul_jumpProduct_eq_reverse
    (fun x => ENNReal.ofReal (Real.exp (-β * energy x))) hbalance states

section RawReferenceReversal

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Reverse a finite state sequence. -/
private def reverseStatesEquiv (n : ℕ) :
    (Fin (n + 1) → Ω) ≃ (Fin (n + 1) → Ω) where
  toFun states := fun i => states i.rev
  invFun states := fun i => states i.rev
  left_inv states := by
    funext i
    simp
  right_inv states := by
    funext i
    simp

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
private theorem reverse_assemblePath_zero
    (T : NNReal) (states : Fin 1 → Ω) (u : Fin 0 → I) :
    JumpPath.reverse (Simplex.assemblePath T (states, u)) =
      Simplex.assemblePath T (states, u) := by
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · funext i
    fin_cases i
    rfl

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
private theorem reverse_assemblePath_succ {n : ℕ}
    (T : NNReal) (states : Fin (n + 2) → Ω)
    (u : Fin (n + 1) → I)
    (hu : u ∈ Simplex.freeSimplexSet (n + 1)) :
    JumpPath.reverse (Simplex.assemblePath T (states, u)) =
      Simplex.assemblePath T
        ((fun i => states i.rev), Simplex.reverseFree u) := by
  apply Prod.ext
  · rfl
  · exact (Simplex.holdingTimesOfFree_reverseFree T u hu).symm

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
private theorem lintegral_reverse_assemblePath_succ {n : ℕ}
    (H : JumpPath Ω (n + 1) → ℝ≥0∞) (hH : Measurable H)
    (T : NNReal) (states : Fin (n + 2) → Ω) :
    (∫⁻ u, H (JumpPath.reverse
          (Simplex.assemblePath T (states, u)))
        ∂((T : ℝ≥0∞) ^ (n + 1) •
          (volume : Measure (Fin (n + 1) → I)).restrict
            (Simplex.freeSimplexSet (n + 1)))) =
      ∫⁻ u, H
          (Simplex.assemblePath T ((fun i => states i.rev), u))
        ∂((T : ℝ≥0∞) ^ (n + 1) •
          (volume : Measure (Fin (n + 1) → I)).restrict
            (Simplex.freeSimplexSet (n + 1))) := by
  rw [lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  calc
    (∫⁻ u in Simplex.freeSimplexSet (n + 1),
        H (JumpPath.reverse
          (Simplex.assemblePath T (states, u)))) =
        ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          H (Simplex.assemblePath T
            ((fun i => states i.rev), Simplex.reverseFree u)) := by
      apply setLIntegral_congr_fun
        (Simplex.measurableSet_freeSimplexSet (n + 1))
      intro u hu
      simpa only using
        congrArg H (reverse_assemblePath_succ T states u hu)
    _ = ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          H (Simplex.assemblePath T ((fun i => states i.rev), u)) := by
      exact Simplex.lintegral_freeSimplex_reverseFree
        (fun u => H (Simplex.assemblePath T
          ((fun i => states i.rev), u)))
        (hH.comp
          ((Simplex.measurable_assemblePath T).comp
            (Measurable.prodMk measurable_const measurable_id)))

/-- The unsymmetrized counting reference is already reversal invariant at the
level of all measurable nonnegative integrals. -/
theorem lintegral_rawCountingReference_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ)
    (H : JumpPath Ω n → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ γ, H (JumpPath.reverse γ) ∂G.rawCountingReference T n) =
      ∫⁻ γ, H γ ∂G.rawCountingReference T n := by
  rw [G.rawCountingReference_eq T n]
  have hassemble := Simplex.measurable_assemblePath
    (Ω := Ω) (n := n) T
  have hleft : Measurable (fun p :
      (Fin (n + 1) → Ω) × (Fin n → I) =>
        H (JumpPath.reverse (Simplex.assemblePath T p))) :=
    (hH.comp JumpPath.measurable_reverse).comp hassemble
  have hright : Measurable (fun p :
      (Fin (n + 1) → Ω) × (Fin n → I) =>
        H (Simplex.assemblePath T p)) :=
    hH.comp hassemble
  change (∫⁻ γ, (H ∘ JumpPath.reverse) γ
      ∂Measure.map (Simplex.assemblePath T)
        ((G.stateSequenceCountingReference n).prod
          ((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n)))) =
    ∫⁻ γ, H γ
      ∂Measure.map (Simplex.assemblePath T)
        ((G.stateSequenceCountingReference n).prod
          ((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n)))
  rw [lintegral_map' (hH.comp JumpPath.measurable_reverse).aemeasurable
      hassemble.aemeasurable,
    lintegral_map' hH.aemeasurable hassemble.aemeasurable]
  change (∫⁻ p, H (JumpPath.reverse (Simplex.assemblePath T p))
      ∂(G.stateSequenceCountingReference n).prod
        ((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))) =
    ∫⁻ p, H (Simplex.assemblePath T p)
      ∂(G.stateSequenceCountingReference n).prod
        ((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))
  rw [lintegral_prod _ hleft.aemeasurable,
    lintegral_prod _ hright.aemeasurable]
  unfold stateSequenceCountingReference
  rw [lintegral_fintype, lintegral_fintype]
  simp only [Measure.count_singleton, mul_one]
  cases n with
  | zero =>
      apply Finset.sum_congr rfl
      intro states _
      apply lintegral_congr
      intro u
      rw [reverse_assemblePath_zero T states u]
  | succ n =>
      simp_rw [lintegral_reverse_assemblePath_succ H hH T]
      exact Fintype.sum_equiv (reverseStatesEquiv (Ω := Ω) (n + 1))
        _ _ (fun _ => rfl)

/-- The raw counting reference itself is invariant under path reversal. -/
theorem map_rawCountingReference_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    (G.rawCountingReference T n).map JumpPath.reverse =
      G.rawCountingReference T n := by
  ext s hs
  rw [Measure.map_apply JumpPath.measurable_reverse hs]
  have h := G.lintegral_rawCountingReference_reverse T n
    (s.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hs)
  have hcomp :
      (fun γ => s.indicator (fun _ => (1 : ℝ≥0∞))
        (JumpPath.reverse γ)) =
        (JumpPath.reverse ⁻¹' s).indicator
          (fun _ => (1 : ℝ≥0∞)) := by
    funext γ
    by_cases hγ : JumpPath.reverse γ ∈ s
    · rw [Set.indicator_of_mem hγ]
      rw [Set.indicator_of_mem
        (show γ ∈ JumpPath.reverse ⁻¹' s from hγ)]
    · rw [Set.indicator_of_notMem hγ]
      rw [Set.indicator_of_notMem
        (show γ ∉ JumpPath.reverse ⁻¹' s from hγ)]
  rw [hcomp, lintegral_indicator
      (hs.preimage JumpPath.measurable_reverse),
    lintegral_indicator hs, setLIntegral_one, setLIntegral_one] at h
  exact h

/-- Since the raw counting chart is reversal invariant, the canonical
symmetrized counting reference coincides with it. -/
theorem countingReference_eq_rawCountingReference
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    G.countingReference T n = G.rawCountingReference T n := by
  unfold countingReference Simplex.reference Simplex.pathProbability
    Simplex.symmetrizePathMeasure
  calc
    simplexSectorMass T n •
        ((2 : ℝ≥0∞)⁻¹ •
          (Simplex.rawPathProbability T
              (G.stateSequenceCountingReference n) +
            (Simplex.rawPathProbability T
              (G.stateSequenceCountingReference n)).map JumpPath.reverse)) =
        (2 : ℝ≥0∞)⁻¹ •
          ((simplexSectorMass T n •
              Simplex.rawPathProbability T
                (G.stateSequenceCountingReference n)) +
            (simplexSectorMass T n •
              Simplex.rawPathProbability T
                (G.stateSequenceCountingReference n)).map JumpPath.reverse) := by
      rw [Measure.map_smul]
      module
    _ = (2 : ℝ≥0∞)⁻¹ •
          (G.rawCountingReference T n +
            (G.rawCountingReference T n).map JumpPath.reverse) := by
      rfl
    _ = G.rawCountingReference T n := by
      rw [G.map_rawCountingReference_reverse T n]
      ext s hs
      simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]
      rw [← two_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel
          (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
          (show (2 : ℝ≥0∞) ≠ ∞ by norm_num),
        one_mul]

end RawReferenceReversal

section FiniteGibbs

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The finite-state partition function as an explicit finite sum. -/
noncomputable def finitePartitionFunction
    (β : ℝ) (energy : Ω → ℝ) : ℝ :=
  ∑ x, Real.exp (-β * energy x)

/-- The general counting-measure partition function is the explicit finite
Boltzmann sum. -/
theorem partitionFunction_count_eq
    (β : ℝ) (energy : Ω → ℝ) :
    Gibbs.partitionFunction (Measure.count : Measure Ω) β energy =
      finitePartitionFunction β energy := by
  simp [Gibbs.partitionFunction, finitePartitionFunction]

/-- The finite-state Helmholtz free energy written using the explicit partition
sum. -/
noncomputable def finiteFreeEnergy
    (β : ℝ) (energy : Ω → ℝ) : ℝ :=
  -Real.log (finitePartitionFunction β energy) / β

/-- The counting-measure Gibbs free energy agrees with the finite-sum form. -/
theorem freeEnergy_count_eq
    (β : ℝ) (energy : Ω → ℝ) :
    Gibbs.freeEnergy (Measure.count : Measure Ω) β energy =
      finiteFreeEnergy β energy := by
  simp [Gibbs.freeEnergy, finiteFreeEnergy, partitionFunction_count_eq]

end FiniteGibbs

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
