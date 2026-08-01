/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorPathLaw
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricRenewalEquation

/-!
# Peeling the first holding coordinate

The renewal equation runs in the horizon direction, so it needs the holding-time
integral of an `(n+1)`-jump sector expressed through the `n`-jump one on a
shorter horizon.  Splitting off the *first* coordinate is what achieves that:
the remaining coordinates then describe the same process started from the state
reached by the first jump.

Everything here happens at a fixed chart scale `T`, with only the available
fraction `ρ` shrinking.  That is what keeps a rescaling of the chart -- and its
Jacobian -- out of the argument entirely.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

open TwoState.AsymmetricExample (cubeExpWeight residualAt)

universe u

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The holding-time integral of one state sequence on a variable available
fraction `ρ` of the horizon, with the horizon scale `T` held fixed.  At `ρ = 1`
this is `holdingIntegral`. -/
noncomputable def holdingIntegralAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in TwoState.AsymmetricExample.freeSimplexSetAt n ρ,
    cubeExpWeight (G.stateEscapeRates states) T u *
      ENNReal.ofReal
        (Real.exp
          (-((G.escapeRate (states (Fin.last n)) : ℝ) * (T : ℝ) *
            residualAt ρ u)))

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem holdingIntegralAt_one
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    G.holdingIntegralAt T states 1 = G.holdingIntegral T states := by
  unfold holdingIntegralAt holdingIntegral
    TwoState.AsymmetricExample.freeSimplexSetAt Simplex.freeSimplexSet
    residualAt TwoState.AsymmetricExample.residual
  simp only [Simplex.coe_unitNNReal]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The escape rates of the shifted sequence are the tail of the original ones:
coordinate `j` of the shifted sequence is spent in the same state as coordinate
`j + 1` of the original. -/
theorem stateEscapeRates_succ
    (G : FiniteJumpGenerator Ω) {n : ℕ} (states : Fin (n + 2) → Ω) :
    G.stateEscapeRates (fun i : Fin (n + 1) => states i.succ) =
      fun j : Fin n => G.stateEscapeRates states j.succ := by
  funext j
  simp only [stateEscapeRates]
  rw [Fin.succ_castSucc]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem stateEscapeRates_zero
    (G : FiniteJumpGenerator Ω) {n : ℕ} (states : Fin (n + 2) → Ω) :
    G.stateEscapeRates states 0 = G.escapeRate (states 0) := by
  simp [stateEscapeRates]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **Peeling the first holding coordinate.**  The first jump leaves at a time
`T v`, and the rest of the path is the same construction for the shifted state
sequence on the remaining fraction `ρ - v`.

The chart scale never changes, so no rescaling of the simplex is involved: only
the available fraction shrinks. -/
theorem holdingIntegralAt_succ
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 2) → Ω) (ρ : ℝ) :
    G.holdingIntegralAt T states ρ =
      ∫⁻ v : I,
        ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * (v : ℝ)))) *
          G.holdingIntegralAt T (fun i : Fin (n + 1) => states i.succ)
            (ρ - (v : ℝ)) := by
  classical
  set r : Fin (n + 1) → NNReal := G.stateEscapeRates states with hr
  set c : NNReal := G.escapeRate (states (Fin.last (n + 1))) with hc
  set head : I → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (Real.exp (-((r 0 : ℝ) * (T : ℝ) * (a : ℝ)))) with hhead
  set tail : ℝ → (Fin n → I) → ℝ≥0∞ := fun frac w =>
    cubeExpWeight (fun j : Fin n => r j.succ) T w *
      ENNReal.ofReal
        (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt frac w))) with htail
  set g : I × (Fin n → I) → ℝ≥0∞ :=
    {p : I × (Fin n → I) | (p.1 : ℝ) + ∑ j, (p.2 j : ℝ) ≤ ρ}.indicator
      (fun p => head p.1 * tail (ρ - (p.1 : ℝ)) p.2) with hg
  have hcond : MeasurableSet
      {p : I × (Fin n → I) | (p.1 : ℝ) + ∑ j, (p.2 j : ℝ) ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hbody : Measurable
      fun p : I × (Fin n → I) => head p.1 * tail (ρ - (p.1 : ℝ)) p.2 := by
    simp only [hhead, htail, residualAt]
    refine Measurable.mul (by fun_prop) (Measurable.mul ?_ (by fun_prop))
    exact (TwoState.AsymmetricExample.measurable_cubeExpWeight
      (fun j : Fin n => r j.succ) T).comp measurable_snd
  have hgmeas : Measurable g := hbody.indicator hcond
  -- The pulled-back integrand is the indicator of the full simplex.
  have hpull : ∀ u : Fin (n + 1) → I,
      g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0 u) =
        (TwoState.AsymmetricExample.freeSimplexSetAt (n + 1) ρ).indicator
          (fun w => cubeExpWeight r T w *
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt ρ w)))) u := by
    intro u
    have hchart :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0 u) =
          (u 0, fun j : Fin n => u j.succ) := rfl
    have hsum : (u 0 : ℝ) + ∑ j : Fin n, (u j.succ : ℝ) =
        ∑ i : Fin (n + 1), (u i : ℝ) :=
      (Fin.sum_univ_succ (fun i : Fin (n + 1) => (u i : ℝ))).symm
    rw [hchart]
    simp only [hg, Set.indicator_apply,
      TwoState.AsymmetricExample.freeSimplexSetAt, Set.mem_setOf_eq, hsum]
    split_ifs with hmem
    · have hres : residualAt (ρ - (u 0 : ℝ)) (fun j : Fin n => u j.succ) =
          residualAt ρ u := by
        simp only [residualAt]
        rw [← hsum]
        ring
      have hprod : head (u 0) *
          cubeExpWeight (fun j : Fin n => r j.succ) T
            (fun j : Fin n => u j.succ) = cubeExpWeight r T u := by
        simp only [hhead, TwoState.AsymmetricExample.cubeExpWeight]
        rw [Fin.prod_univ_succ]
      rw [htail]
      dsimp only
      rw [hres, ← mul_assoc, hprod]
    · rfl
  -- Transport to the product chart and use Fubini.
  have hstep :
      G.holdingIntegralAt T states ρ =
        ∫⁻ a : I, ∫⁻ w : Fin n → I, g (a, w) := by
    unfold holdingIntegralAt
    rw [← hr, ← hc,
      ← lintegral_indicator
        (TwoState.AsymmetricExample.measurableSet_freeSimplexSetAt (n + 1) ρ)]
    rw [show (∫⁻ u : Fin (n + 1) → I,
        (TwoState.AsymmetricExample.freeSimplexSetAt (n + 1) ρ).indicator
          (fun w => cubeExpWeight r T w *
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * residualAt ρ w)))) u) =
        ∫⁻ u : Fin (n + 1) → I,
          g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0 u) from
      lintegral_congr fun u => (hpull u).symm]
    rw [(volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => I) 0).lintegral_comp hgmeas]
    rw [Measure.volume_eq_prod, lintegral_prod _ hgmeas.aemeasurable]
  rw [hstep]
  refine lintegral_congr fun a => ?_
  have hinner : ∀ w : Fin n → I,
      g (a, w) =
        (TwoState.AsymmetricExample.freeSimplexSetAt n (ρ - (a : ℝ))).indicator
          (fun w => head a * tail (ρ - (a : ℝ)) w) w := by
    intro w
    simp only [hg, Set.indicator_apply,
      TwoState.AsymmetricExample.freeSimplexSetAt, Set.mem_setOf_eq]
    have hiff : ((a : ℝ) + ∑ j, (w j : ℝ) ≤ ρ) ↔ (∑ j, (w j : ℝ) ≤ ρ - (a : ℝ)) := by
      constructor <;> intro h <;> linarith
    simp only [hiff]
  simp_rw [hinner]
  rw [lintegral_indicator
    (TwoState.AsymmetricExample.measurableSet_freeSimplexSetAt n (ρ - (a : ℝ)))]
  rw [lintegral_const_mul' _ _ (by simp [hhead] : head a ≠ ∞)]
  congr 1


/-! ### Measurability in the available fraction -/

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The holding-time integral is measurable in the available fraction.  Both the
domain and the residual factor move with `ρ`, so this goes through the jointly
measurable integrand rather than through any continuity in `ρ`. -/
theorem measurable_holdingIntegralAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    Measurable fun ρ : ℝ => G.holdingIntegralAt T states ρ := by
  classical
  set F : ℝ × (Fin n → I) → ℝ≥0∞ :=
    {q : ℝ × (Fin n → I) | ∑ j, (q.2 j : ℝ) ≤ q.1}.indicator
      (fun q => cubeExpWeight (G.stateEscapeRates states) T q.2 *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (states (Fin.last n)) : ℝ) * (T : ℝ) *
              residualAt q.1 q.2)))) with hF
  have hset : MeasurableSet
      {q : ℝ × (Fin n → I) | ∑ j, (q.2 j : ℝ) ≤ q.1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hbody : Measurable fun q : ℝ × (Fin n → I) =>
      cubeExpWeight (G.stateEscapeRates states) T q.2 *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (states (Fin.last n)) : ℝ) * (T : ℝ) *
              residualAt q.1 q.2))) := by
    simp only [residualAt]
    refine Measurable.mul ?_ (by fun_prop)
    exact (TwoState.AsymmetricExample.measurable_cubeExpWeight
      (G.stateEscapeRates states) T).comp measurable_snd
  have hFmeas : Measurable F := hbody.indicator hset
  have hrw : ∀ ρ : ℝ,
      G.holdingIntegralAt T states ρ = ∫⁻ u : Fin n → I, F (ρ, u) := by
    intro ρ
    rw [holdingIntegralAt,
      ← lintegral_indicator
        (TwoState.AsymmetricExample.measurableSet_freeSimplexSetAt n ρ)]
    refine lintegral_congr fun u => ?_
    simp only [hF, Set.indicator_apply,
      TwoState.AsymmetricExample.freeSimplexSetAt, Set.mem_setOf_eq]
  simp_rw [hrw]
  exact hFmeas.lintegral_prod_right'

/-! ### The sequence mass on a variable fraction -/

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Splitting the first jump out of the realized jump-rate product. -/
theorem jumpProduct_succ
    (G : FiniteJumpGenerator Ω) {n : ℕ} (states : Fin (n + 2) → Ω) :
    G.jumpProduct states =
      (G.jumpRate (states 0) (states 1) : ℝ≥0∞) *
        G.jumpProduct (fun i : Fin (n + 1) => states i.succ) := by
  unfold jumpProduct
  rw [Fin.prod_univ_succ]
  congr 1

/-- The unnormalized mass of one state sequence on a variable available fraction
`ρ`, at fixed horizon scale `T`. -/
noncomputable def sequenceMassAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) (ρ : ℝ) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n * G.jumpProduct states * G.holdingIntegralAt T states ρ

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sequenceMassAt_one
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    G.sequenceMassAt T states 1 = G.sequenceMass T states := by
  rw [sequenceMassAt, G.holdingIntegralAt_one T states, sequenceMass]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **First-jump decomposition of a single state sequence.**  One factor of the
horizon scale is spent on the jump that leaves the initial state; the rest of
the sequence carries the same construction on the remaining fraction. -/
theorem sequenceMassAt_succ
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 2) → Ω) (ρ : ℝ) :
    G.sequenceMassAt T states ρ =
      (T : ℝ≥0∞) * (G.jumpRate (states 0) (states 1) : ℝ≥0∞) *
        ∫⁻ v : I,
          ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * (v : ℝ)))) *
            G.sequenceMassAt T (fun i : Fin (n + 1) => states i.succ)
              (ρ - (v : ℝ)) := by
  have hconst : (T : ℝ≥0∞) ^ n * G.jumpProduct
      (fun i : Fin (n + 1) => states i.succ) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (G.jumpProduct_ne_top _)
  rw [sequenceMassAt, G.holdingIntegralAt_succ T states ρ,
    G.jumpProduct_succ states]
  have hpull :
      (∫⁻ v : I,
          ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * (v : ℝ)))) *
            G.sequenceMassAt T (fun i : Fin (n + 1) => states i.succ)
              (ρ - (v : ℝ))) =
        ((T : ℝ≥0∞) ^ n *
            G.jumpProduct (fun i : Fin (n + 1) => states i.succ)) *
          ∫⁻ v : I,
            ENNReal.ofReal
                (Real.exp
                  (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * (v : ℝ)))) *
              G.holdingIntegralAt T (fun i : Fin (n + 1) => states i.succ)
                (ρ - (v : ℝ)) := by
    rw [← lintegral_const_mul' _ _ hconst]
    refine lintegral_congr fun v => ?_
    rw [sequenceMassAt]
    ring
  rw [hpull]
  ring

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem measurable_sequenceMassAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    Measurable fun ρ : ℝ => G.sequenceMassAt T states ρ := by
  simp only [sequenceMassAt]
  exact measurable_const.mul (G.measurable_holdingIntegralAt T states)

/-! ### Folding the branching sum over the state reached by the first jump

Summing the single-sequence decomposition over all state sequences is what
turns the jump-rate prefactor into a genuine renewal kernel: the head of the
sequence is pinned to the initial state, and the state reached by the first
jump becomes the branching index. -/

/-- The mass the `n`-jump sector sends from `x` to `y` on a variable available
fraction `ρ` of the horizon, at fixed horizon scale `T`.  At `ρ = 1` this is
`sectorTerminalMassFrom`. -/
noncomputable def sectorTerminalMassAtFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ) (ρ : ℝ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → Ω,
    fixedInitialWeight x (states 0) *
      (fixedInitialWeight y (states (Fin.last n)) * G.sequenceMassAt T states ρ)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sectorTerminalMassAtFrom_one
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ) :
    G.sectorTerminalMassAtFrom T x y n 1 = G.sectorTerminalMassFrom T x y n :=
  Finset.sum_congr rfl fun states _ => by rw [G.sequenceMassAt_one T states]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem measurable_sectorTerminalMassAtFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ) :
    Measurable fun ρ : ℝ => G.sectorTerminalMassAtFrom T x y n ρ := by
  simp only [sectorTerminalMassAtFrom]
  exact Finset.measurable_sum _ fun states _ =>
    measurable_const.mul (measurable_const.mul (G.measurable_sequenceMassAt T states))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **First-jump renewal for the sector terminal mass.**  The initial state
survives the first holding interval, jumps to some state `z`, and the remaining
`n` jumps have to land on `y` within the fraction that is left. -/
theorem sectorTerminalMassAtFrom_succ
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ) (ρ : ℝ) :
    G.sectorTerminalMassAtFrom T x y (n + 1) ρ =
      (T : ℝ≥0∞) *
        ∫⁻ v : I,
          ENNReal.ofReal
              (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
            ∑ z : Ω,
              (G.jumpRate x z : ℝ≥0∞) *
                G.sectorTerminalMassAtFrom T z y n (ρ - (v : ℝ)) := by
  classical
  -- The branching sum, already folded onto the state the first jump reaches.
  set H : ℝ → ℝ≥0∞ := fun s =>
    ∑ rest : Fin (n + 1) → Ω,
      (G.jumpRate x (rest 0) : ℝ≥0∞) *
        (fixedInitialWeight y (rest (Fin.last n)) * G.sequenceMassAt T rest s)
    with hH
  have hfold : ∀ s : ℝ,
      (∑ z : Ω, (G.jumpRate x z : ℝ≥0∞) *
        G.sectorTerminalMassAtFrom T z y n s) = H s := by
    intro s
    simp only [hH, sectorTerminalMassAtFrom, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun rest _ => ?_
    have hterm : ∀ z : Ω,
        (G.jumpRate x z : ℝ≥0∞) *
            (fixedInitialWeight z (rest 0) *
              (fixedInitialWeight y (rest (Fin.last n)) *
                G.sequenceMassAt T rest s)) =
          if rest 0 = z then
            (G.jumpRate x (rest 0) : ℝ≥0∞) *
              (fixedInitialWeight y (rest (Fin.last n)) *
                G.sequenceMassAt T rest s)
          else 0 := by
      intro z
      by_cases h : rest 0 = z
      · subst h; simp [fixedInitialWeight]
      · simp [fixedInitialWeight, h]
    simp only [hterm]
    rw [Finset.sum_ite_eq]
    simp
  simp only [hfold]
  -- Split the state sequence into its initial state and the rest.
  have hreindex :
      G.sectorTerminalMassAtFrom T x y (n + 1) ρ =
        ∑ z : Ω, fixedInitialWeight x z *
          ∑ rest : Fin (n + 1) → Ω,
            fixedInitialWeight y (rest (Fin.last n)) *
              G.sequenceMassAt T (Fin.cons z rest) ρ := by
    rw [sectorTerminalMassAtFrom,
      ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 2) => Ω)
        (fun states : Fin (n + 2) → Ω =>
          fixedInitialWeight x (states 0) *
            (fixedInitialWeight y (states (Fin.last (n + 1))) *
              G.sequenceMassAt T states ρ)),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun rest _ => ?_
    have hlast : (Fin.cons z rest : Fin (n + 2) → Ω) (Fin.last (n + 1)) =
        rest (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    show fixedInitialWeight x ((Fin.cons z rest : Fin (n + 2) → Ω) 0) *
        (fixedInitialWeight y ((Fin.cons z rest : Fin (n + 2) → Ω)
            (Fin.last (n + 1))) *
          G.sequenceMassAt T (Fin.cons z rest) ρ) = _
    rw [Fin.cons_zero, hlast]
  rw [hreindex]
  -- The initial weight pins the head of the sequence to `x`.
  have hhead : ∀ F : Ω → ℝ≥0∞, (∑ z : Ω, fixedInitialWeight x z * F z) = F x := by
    intro F
    simp [fixedInitialWeight]
  rw [hhead fun z => ∑ rest : Fin (n + 1) → Ω,
    fixedInitialWeight y (rest (Fin.last n)) *
      G.sequenceMassAt T (Fin.cons z rest) ρ]
  -- Decompose each surviving sequence at its first jump.
  have hcons : ∀ rest : Fin (n + 1) → Ω,
      G.sequenceMassAt T (Fin.cons x rest) ρ =
        (T : ℝ≥0∞) * (G.jumpRate x (rest 0) : ℝ≥0∞) *
          ∫⁻ v : I,
            ENNReal.ofReal
                (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
              G.sequenceMassAt T rest (ρ - (v : ℝ)) := by
    intro rest
    have htail : (fun i : Fin (n + 1) => (Fin.cons x rest : Fin (n + 2) → Ω) i.succ) =
        rest := funext fun i => Fin.cons_succ _ _ _
    have hone : (Fin.cons x rest : Fin (n + 2) → Ω) 1 = rest 0 := by
      rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
    rw [G.sequenceMassAt_succ T (Fin.cons x rest) ρ]
    simp only [Fin.cons_zero, hone, htail]
  simp only [hcons]
  -- Move the sequence-dependent constants inside the integral, then exchange the
  -- finite sum with it.
  have hpull : ∀ rest : Fin (n + 1) → Ω,
      fixedInitialWeight y (rest (Fin.last n)) *
          ((T : ℝ≥0∞) * (G.jumpRate x (rest 0) : ℝ≥0∞) *
            ∫⁻ v : I,
              ENNReal.ofReal
                  (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
                G.sequenceMassAt T rest (ρ - (v : ℝ))) =
        (T : ℝ≥0∞) *
          ∫⁻ v : I,
            ENNReal.ofReal
                (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
              ((G.jumpRate x (rest 0) : ℝ≥0∞) *
                (fixedInitialWeight y (rest (Fin.last n)) *
                  G.sequenceMassAt T rest (ρ - (v : ℝ)))) := by
    intro rest
    have hne : (G.jumpRate x (rest 0) : ℝ≥0∞) *
        fixedInitialWeight y (rest (Fin.last n)) ≠ ∞ := by
      refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
      unfold fixedInitialWeight
      split <;> simp
    have hconst :
        (∫⁻ v : I,
            ENNReal.ofReal
                (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
              ((G.jumpRate x (rest 0) : ℝ≥0∞) *
                (fixedInitialWeight y (rest (Fin.last n)) *
                  G.sequenceMassAt T rest (ρ - (v : ℝ))))) =
          ((G.jumpRate x (rest 0) : ℝ≥0∞) *
              fixedInitialWeight y (rest (Fin.last n))) *
            ∫⁻ v : I,
              ENNReal.ofReal
                  (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
                G.sequenceMassAt T rest (ρ - (v : ℝ)) := by
      rw [← lintegral_const_mul' _ _ hne]
      exact lintegral_congr fun v => by ring
    rw [hconst]
    ring
  simp only [hpull]
  have hmeas : ∀ rest : Fin (n + 1) → Ω,
      Measurable fun v : I =>
        ENNReal.ofReal
            (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
          ((G.jumpRate x (rest 0) : ℝ≥0∞) *
            (fixedInitialWeight y (rest (Fin.last n)) *
              G.sequenceMassAt T rest (ρ - (v : ℝ)))) := by
    intro rest
    refine Measurable.mul (by fun_prop)
      (measurable_const.mul (measurable_const.mul ?_))
    exact (G.measurable_sequenceMassAt T rest).comp
      (measurable_const.sub measurable_subtype_coe)
  rw [← Finset.mul_sum,
    (lintegral_finsetSum (μ := (volume : Measure I)) Finset.univ
      fun rest _ => hmeas rest).symm]
  refine congrArg _ (lintegral_congr fun v => ?_)
  simp only [hH, Finset.mul_sum]

/-! ### The jump-free base case

With no jumps there is nothing left to integrate over: the chart is a single
point and the whole available fraction is spent surviving in the initial
state. -/

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem holdingIntegralAt_zero
    (G : FiniteJumpGenerator Ω) (T : NNReal) (states : Fin 1 → Ω) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    G.holdingIntegralAt T states ρ =
      ENNReal.ofReal
        (Real.exp (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * ρ))) := by
  have hset : TwoState.AsymmetricExample.freeSimplexSetAt 0 ρ = Set.univ := by
    ext u
    simp [TwoState.AsymmetricExample.freeSimplexSetAt, hρ]
  have hpoint : (Fin.last 0 : Fin 1) = 0 := rfl
  have huniv : (volume : Measure (Fin 0 → I)) Set.univ = 1 := by simp
  rw [holdingIntegralAt, hset, Measure.restrict_univ]
  have hbody : ∀ u : Fin 0 → I,
      cubeExpWeight (G.stateEscapeRates states) T u *
          ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (states (Fin.last 0)) : ℝ) * (T : ℝ) *
                residualAt ρ u))) =
        ENNReal.ofReal
          (Real.exp (-((G.escapeRate (states 0) : ℝ) * (T : ℝ) * ρ))) := by
    intro u
    simp [cubeExpWeight, residualAt, hpoint]
  simp only [hbody]
  rw [lintegral_const, huniv, mul_one]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Without a jump the sector can only stay where it started. -/
theorem sectorTerminalMassAtFrom_zero
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    G.sectorTerminalMassAtFrom T x y 0 ρ =
      if x = y then
        ENNReal.ofReal (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * ρ)))
      else 0 := by
  classical
  have hmain : G.sectorTerminalMassAtFrom T x y 0 ρ =
      fixedInitialWeight x x *
        (fixedInitialWeight y x * G.sequenceMassAt T (fun _ : Fin 1 => x) ρ) := by
    rw [sectorTerminalMassAtFrom]
    refine Finset.sum_eq_single (fun _ : Fin 1 => x) (fun states _ hne => ?_)
      (by simp)
    have h0 : states 0 ≠ x := fun h =>
      hne (funext fun i => by rw [Subsingleton.elim i 0, h])
    rw [fixedInitialWeight_of_ne h0, zero_mul]
  rw [hmain, fixedInitialWeight_self, one_mul, sequenceMassAt,
    G.holdingIntegralAt_zero T (fun _ : Fin 1 => x) hρ]
  by_cases h : x = y
  · simp [h, fixedInitialWeight, jumpProduct]
  · simp [fixedInitialWeight, h]

/-! ### The renewal equation for the transition mass

Summing the sector renewal over the jump count closes the recursion: the whole
tail of the expansion reassembles into the transition mass on the remaining
fraction.  Interchanging the sum with the integral is unconditional here
because everything is `ℝ≥0∞`-valued. -/

/-- The terminal transition mass on a variable available fraction `ρ` of the
horizon, at fixed horizon scale `T`.  At `ρ = 1` this is `transitionMass`. -/
noncomputable def transitionMassAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (ρ : ℝ) : ℝ≥0∞ :=
  ∑' n, G.sectorTerminalMassAtFrom T x y n ρ

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem transitionMassAt_one
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    G.transitionMassAt T x y 1 = G.transitionMass T x y :=
  tsum_congr fun n => G.sectorTerminalMassAtFrom_one T x y n

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem measurable_transitionMassAt
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    Measurable fun ρ : ℝ => G.transitionMassAt T x y ρ :=
  Measurable.tsum fun n => G.measurable_sectorTerminalMassAtFrom T x y n

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **The renewal equation for the transition mass.**  Either the initial state
survives the whole available fraction without jumping, or it jumps at some
point inside it and the process starts afresh from wherever it lands. -/
theorem transitionMassAt_renewal
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    G.transitionMassAt T x y ρ =
      (if x = y then
        ENNReal.ofReal (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * ρ)))
      else 0) +
        (T : ℝ≥0∞) *
          ∫⁻ v : I,
            ENNReal.ofReal
                (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
              ∑ z : Ω,
                (G.jumpRate x z : ℝ≥0∞) *
                  G.transitionMassAt T z y (ρ - (v : ℝ)) := by
  classical
  have hmeas : ∀ n : ℕ, Measurable fun v : I =>
      ENNReal.ofReal
          (Real.exp (-((G.escapeRate x : ℝ) * (T : ℝ) * (v : ℝ)))) *
        ∑ z : Ω, (G.jumpRate x z : ℝ≥0∞) *
          G.sectorTerminalMassAtFrom T z y n (ρ - (v : ℝ)) := by
    intro n
    refine Measurable.mul (by fun_prop) (Finset.measurable_sum _ fun z _ => ?_)
    exact measurable_const.mul
      ((G.measurable_sectorTerminalMassAtFrom T z y n).comp
        (measurable_const.sub measurable_subtype_coe))
  rw [transitionMassAt, tsum_eq_zero_add' ENNReal.summable,
    G.sectorTerminalMassAtFrom_zero T x y hρ]
  refine congrArg _ ?_
  simp only [G.sectorTerminalMassAtFrom_succ T x y _ ρ]
  rw [ENNReal.tsum_mul_left]
  refine congrArg _ ?_
  rw [← lintegral_tsum fun n => (hmeas n).aemeasurable]
  refine lintegral_congr fun v => ?_
  rw [ENNReal.tsum_mul_left]
  refine congrArg _ ?_
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  exact Finset.sum_congr rfl fun z _ => ENNReal.tsum_mul_left

/-! ### Vanishing past the horizon and a uniform bound

The two facts the real-valued form needs.  A negative fraction leaves nothing
for the holding times, so the chart is empty.  And shrinking the fraction only
changes the residual survival factor, by a factor the rate bound controls,
which reduces every bound to the already-proved `rho = 1` normalization. -/

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem holdingIntegralAt_of_neg
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) {ρ : ℝ} (hρ : ρ < 0) :
    G.holdingIntegralAt T states ρ = 0 := by
  have hempty : TwoState.AsymmetricExample.freeSimplexSetAt n ρ = ∅ := by
    ext u
    simp only [TwoState.AsymmetricExample.freeSimplexSetAt, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hρ (Finset.sum_nonneg fun i _ => (u i).2.1)
  rw [holdingIntegralAt, hempty, Measure.restrict_empty, lintegral_zero_measure]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sequenceMassAt_of_neg
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) {ρ : ℝ} (hρ : ρ < 0) :
    G.sequenceMassAt T states ρ = 0 := by
  rw [sequenceMassAt, G.holdingIntegralAt_of_neg T states hρ, mul_zero]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sectorTerminalMassAtFrom_of_neg
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ)
    {ρ : ℝ} (hρ : ρ < 0) :
    G.sectorTerminalMassAtFrom T x y n ρ = 0 :=
  Finset.sum_eq_zero fun states _ => by
    rw [G.sequenceMassAt_of_neg T states hρ, mul_zero, mul_zero]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- A negative fraction leaves no room for even the first holding time. -/
theorem transitionMassAt_of_neg
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) {ρ : ℝ} (hρ : ρ < 0) :
    G.transitionMassAt T x y ρ = 0 := by
  rw [transitionMassAt]
  simp [G.sectorTerminalMassAtFrom_of_neg T x y _ hρ]

/-- The factor by which shrinking the available fraction can inflate a residual
survival factor. -/
noncomputable def fractionBound (G : FiniteJumpGenerator Ω) (T : NNReal) : ℝ :=
  Real.exp ((G.rateBound : ℝ) * (T : ℝ))

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem one_le_fractionBound (G : FiniteJumpGenerator Ω) (T : NNReal) :
    1 ≤ G.fractionBound T :=
  Real.one_le_exp (by positivity)

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem holdingIntegralAt_le
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    G.holdingIntegralAt T states ρ ≤
      ENNReal.ofReal (G.fractionBound T) * G.holdingIntegral T states := by
  set c : ℝ := (G.escapeRate (states (Fin.last n)) : ℝ) with hc
  have hc0 : 0 ≤ c := (G.escapeRate _).coe_nonneg
  have hcb : c ≤ (G.rateBound : ℝ) := by
    exact_mod_cast G.escapeRate_le_rateBound (states (Fin.last n))
  have hsub : TwoState.AsymmetricExample.freeSimplexSetAt n ρ ⊆
      Simplex.freeSimplexSet n := by
    intro u hu
    exact le_trans hu h1
  have hpt : ∀ u : Fin n → I,
      cubeExpWeight (G.stateEscapeRates states) T u *
          ENNReal.ofReal
            (Real.exp (-(c * (T : ℝ) * residualAt ρ u))) ≤
        ENNReal.ofReal (G.fractionBound T) *
          (cubeExpWeight (G.stateEscapeRates states) T u *
            ENNReal.ofReal
              (Real.exp
                (-(c * (T : ℝ) *
                  TwoState.AsymmetricExample.residual u)))) := by
    intro u
    have hexp : Real.exp (-(c * (T : ℝ) * residualAt ρ u)) ≤
        G.fractionBound T *
          Real.exp (-(c * (T : ℝ) * TwoState.AsymmetricExample.residual u)) := by
      rw [fractionBound, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hT : (0 : ℝ) ≤ (T : ℝ) := T.coe_nonneg
      have hstep : c * (T : ℝ) * (1 - ρ) ≤ (G.rateBound : ℝ) * (T : ℝ) := by
        have h1' : c * (T : ℝ) * (1 - ρ) ≤ c * (T : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc0 hT)
        have h2' : c * (T : ℝ) ≤ (G.rateBound : ℝ) * (T : ℝ) :=
          mul_le_mul_of_nonneg_right hcb hT
        linarith
      simp only [residualAt, TwoState.AsymmetricExample.residual]
      nlinarith [hstep]
    calc cubeExpWeight (G.stateEscapeRates states) T u *
            ENNReal.ofReal (Real.exp (-(c * (T : ℝ) * residualAt ρ u)))
        ≤ cubeExpWeight (G.stateEscapeRates states) T u *
            ENNReal.ofReal
              (G.fractionBound T *
                Real.exp
                  (-(c * (T : ℝ) *
                    TwoState.AsymmetricExample.residual u))) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hexp) _
      _ = ENNReal.ofReal (G.fractionBound T) *
            (cubeExpWeight (G.stateEscapeRates states) T u *
              ENNReal.ofReal
                (Real.exp
                  (-(c * (T : ℝ) *
                    TwoState.AsymmetricExample.residual u)))) := by
          rw [ENNReal.ofReal_mul (le_trans zero_le_one (G.one_le_fractionBound T))]
          ring
  calc G.holdingIntegralAt T states ρ
      ≤ ∫⁻ u in Simplex.freeSimplexSet n,
          cubeExpWeight (G.stateEscapeRates states) T u *
            ENNReal.ofReal
              (Real.exp (-(c * (T : ℝ) * residualAt ρ u))) :=
        lintegral_mono_set hsub
    _ ≤ ∫⁻ u in Simplex.freeSimplexSet n,
          ENNReal.ofReal (G.fractionBound T) *
            (cubeExpWeight (G.stateEscapeRates states) T u *
              ENNReal.ofReal
                (Real.exp
                  (-(c * (T : ℝ) *
                    TwoState.AsymmetricExample.residual u)))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (G.fractionBound T) * G.holdingIntegral T states := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, holdingIntegral]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sequenceMassAt_le
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    G.sequenceMassAt T states ρ ≤
      ENNReal.ofReal (G.fractionBound T) * G.sequenceMass T states := by
  rw [sequenceMassAt, sequenceMass]
  calc (T : ℝ≥0∞) ^ n * G.jumpProduct states * G.holdingIntegralAt T states ρ
      ≤ (T : ℝ≥0∞) ^ n * G.jumpProduct states *
          (ENNReal.ofReal (G.fractionBound T) * G.holdingIntegral T states) :=
        mul_le_mul_right (G.holdingIntegralAt_le T states h0 h1) _
    _ = ENNReal.ofReal (G.fractionBound T) *
          ((T : ℝ≥0∞) ^ n * G.jumpProduct states *
            G.holdingIntegral T states) := by ring

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sectorTerminalMassAtFrom_le
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    G.sectorTerminalMassAtFrom T x y n ρ ≤
      ENNReal.ofReal (G.fractionBound T) * G.sectorTerminalMassFrom T x y n := by
  rw [sectorTerminalMassAtFrom, sectorTerminalMassFrom, Finset.mul_sum]
  refine Finset.sum_le_sum fun states _ => ?_
  calc fixedInitialWeight x (states 0) *
          (fixedInitialWeight y (states (Fin.last n)) *
            G.sequenceMassAt T states ρ)
      ≤ fixedInitialWeight x (states 0) *
          (fixedInitialWeight y (states (Fin.last n)) *
            (ENNReal.ofReal (G.fractionBound T) * G.sequenceMass T states)) :=
        mul_le_mul_right (mul_le_mul_right (G.sequenceMassAt_le T states h0 h1) _) _
    _ = ENNReal.ofReal (G.fractionBound T) *
          (fixedInitialWeight x (states 0) *
            (fixedInitialWeight y (states (Fin.last n)) *
              G.sequenceMass T states)) := by ring

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem transitionMass_le_one
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    G.transitionMass T x y ≤ 1 := by
  rw [← G.sum_transitionMass T x]
  exact Finset.single_le_sum (f := fun y : Ω => G.transitionMass T x y)
    (fun _ _ => zero_le) (Finset.mem_univ y)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **A uniform bound on the whole fraction range.**  Everything reduces to the
normalization already proved at `rho = 1`. -/
theorem transitionMassAt_le
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    G.transitionMassAt T x y ρ ≤ ENNReal.ofReal (G.fractionBound T) := by
  calc G.transitionMassAt T x y ρ
      ≤ ∑' n, ENNReal.ofReal (G.fractionBound T) *
          G.sectorTerminalMassFrom T x y n :=
        ENNReal.tsum_le_tsum fun n =>
          G.sectorTerminalMassAtFrom_le T x y n h0 h1
    _ = ENNReal.ofReal (G.fractionBound T) * G.transitionMass T x y :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (G.fractionBound T) * 1 :=
        mul_le_mul_right (G.transitionMass_le_one T x y) _
    _ = ENNReal.ofReal (G.fractionBound T) := mul_one _

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem transitionMassAt_ne_top
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    G.transitionMassAt T x y ρ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (G.transitionMassAt_le T x y h0 h1)

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
