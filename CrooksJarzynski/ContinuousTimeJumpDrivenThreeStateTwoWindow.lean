/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenConnectedPath
import CrooksJarzynski.ContinuousTimeJumpDrivenWorkDistribution

/-!
# A two-window driven protocol on three states

The one-window specialization only exercises the base case of the driven
machinery.  This module instantiates a genuinely multi-window protocol: three
states, three energy landscapes, and two distinct generators, each in
instantaneous Gibbs detailed balance with the energy landscape of its own
window.

The protocol raises the middle state's energy and then lowers it back.  The
initial and final landscapes coincide, so the free-energy difference vanishes,
while the endpoint work observable is genuinely nonconstant: it separates two
boundary-consistent carrier points, one hopping through the raised state and
one resting, and every window mark of both points is a valid real-time
trajectory chart with positive pre-jump holding times.  (This is a statement
about the work observable on the carrier.) For positive window widths, the
forward law is additionally proved to give positive probability to the work
values `0` and `log 2`, so its pushforward work distribution is nondegenerate.
The example also pins the `Fin.castSucc` orientation of the window-indexed
balance hypothesis on a case where the two windows differ.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven
namespace ThreeStateTwoWindow

/-- The three energy landscapes: flat, raised middle state, flat again. -/
noncomputable def energy : Fin 3 → Fin 3 → ℝ :=
  ![![0, 0, 0], ![0, Real.log 2, 0], ![0, 0, 0]]

/-- First window: the symmetric Y-shaped generator with unit rates on the
edges `0 ↔ 1` and `0 ↔ 2`. -/
def genFlat : FiniteJumpGenerator (Fin 3) where
  jumpRate := ![![0, 1, 1], ![1, 0, 0], ![1, 0, 0]]
  jumpRate_self := by intro x; fin_cases x <;> rfl

/-- Second window: the same Y shape, with the rate out of the raised middle
state doubled so that the chain is reversible for the tilted landscape. -/
def genTilted : FiniteJumpGenerator (Fin 3) where
  jumpRate := ![![0, 1, 1], ![2, 0, 0], ![1, 0, 0]]
  jumpRate_self := by intro x; fin_cases x <;> rfl

/-- The two-window generator protocol. -/
def generator : Fin 2 → FiniteJumpGenerator (Fin 3) :=
  ![genFlat, genTilted]

/-- The flat-window generator is symmetric, hence in detailed balance with the
flat landscape. -/
theorem genFlat_isGibbsDetailedBalance :
    genFlat.IsGibbsDetailedBalance 1 (energy 0) := by
  intro x y
  fin_cases x <;> fin_cases y <;> simp [genFlat, energy]

/-- The tilted-window generator is in detailed balance with the raised
landscape: the doubled escape rate from the middle state exactly compensates
its halved Boltzmann weight. -/
theorem genTilted_isGibbsDetailedBalance :
    genTilted.IsGibbsDetailedBalance 1 (energy 1) := by
  have h2 : ENNReal.ofReal (Real.exp (-(1 : ℝ) * Real.log 2)) * 2 =
      ENNReal.ofReal (Real.exp (-(1 : ℝ) * 0)) * 1 := by
    rw [show (-(1 : ℝ) * Real.log 2) = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      show (-(1 : ℝ) * 0) = 0 by ring, Real.exp_zero,
      ENNReal.ofReal_one, one_mul,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  intro x y
  fin_cases x <;> fin_cases y <;>
    first
      | (simp [genTilted, energy]; done)
      | (simpa [genTilted, energy] using h2.symm)
      | (simpa [genTilted, energy] using h2)

/-- Every window's generator satisfies instantaneous Gibbs detailed balance
with its own initial landscape — the hypothesis of the driven headlines, with
the `Fin.castSucc` orientation exercised on two genuinely different windows. -/
theorem generator_isGibbsDetailedBalance :
    ∀ i : Fin 2,
      (generator i).IsGibbsDetailedBalance 1 (energy i.castSucc) := by
  intro i
  fin_cases i
  · exact genFlat_isGibbsDetailedBalance
  · exact genTilted_isGibbsDetailedBalance

/-- The protocol returns to its initial landscape, so the free-energy
difference vanishes. -/
theorem deltaFreeEnergy_eq_zero :
    deltaFreeEnergy (Measure.count : Measure (Fin 3)) 1 energy = 0 := by
  rw [deltaFreeEnergy_count_eq_finite]
  have h : energy (Fin.last 2) = energy 0 := by
    show energy 2 = energy 0
    simp [energy]
  rw [h, sub_self]

/-- **Crooks relation for the two-window three-state protocol.** -/
theorem crooks (duration : Fin 2 → NNReal) :
    CrooksRelation
      (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration)
      (reverseDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1
          (energy (Fin.last 2)))
        generator duration)
      (fun γ => ENNReal.ofReal (Real.exp (-1 * work energy γ)))
      (ENNReal.ofReal
        (Real.exp (-1 *
          deltaFreeEnergy (Measure.count : Measure (Fin 3)) 1 energy))) :=
  crooks_of_gibbsDetailedBalance 1 one_ne_zero energy generator duration
    generator_isGibbsDetailedBalance

/-- **Jarzynski equality for the two-window three-state protocol**, in the
form `E[exp (-W)] = 1` because the protocol is cyclic in free energy. -/
theorem jarzynski_eq_one (duration : Fin 2 → NNReal) :
    ∫ γ, Real.exp (-1 * work energy γ)
        ∂forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
          generator duration = 1 := by
  rw [jarzynski_of_gibbsDetailedBalance 1 one_ne_zero energy generator
    duration generator_isGibbsDetailedBalance]
  rw [deltaFreeEnergy_eq_zero]
  norm_num

/-- **Second law for the two-window three-state protocol**: the mean work is
nonnegative because the free-energy difference vanishes. -/
theorem second_law (duration : Fin 2 → NNReal) :
    0 ≤ ∫ γ, work energy γ
        ∂forwardDrivenLaw
          (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
          generator duration := by
  have h := second_law_of_gibbsDetailedBalance 1 one_pos energy generator
    duration generator_isGibbsDetailedBalance
  rw [deltaFreeEnergy_eq_zero] at h
  exact h

/-! ### Positive-probability work atoms for positive windows -/

private def endpointEvent (y : Fin 3) : Set (Fin 3 × FullPath (Fin 3)) :=
  {p | p.1 = y}

private theorem measurableSet_endpointEvent (y : Fin 3) :
    MeasurableSet (endpointEvent y) :=
  (measurable_fst.eq_const y).setOf

private theorem forwardWindowKernel_endpointEvent
    (G : FiniteJumpGenerator (Fin 3)) (T : NNReal) (x y : Fin 3) :
    G.forwardWindowKernel T x (endpointEvent y) =
      G.transitionMass T x y := by
  rw [G.forwardWindowKernel_apply,
    Measure.map_apply (by fun_prop) (measurableSet_endpointEvent y)]
  change G.pathLawFrom T x {γ | FullPath.terminalState γ = y} = _
  rw [← G.pathLawFrom_terminalState_singleton T x y,
    Measure.map_apply FullPath.measurable_terminalState
      (measurableSet_singleton y)]
  rfl

private def oneWindowEvent (x₀ x₁ : Fin 3) :
    Set (Path (Fin 3) 1) :=
  {γ | γ.2.1.1 = x₀ ∧ γ.1 = x₁}

private theorem measurableSet_oneWindowEvent (x₀ x₁ : Fin 3) :
    MeasurableSet (oneWindowEvent x₀ x₁) := by
  exact
    ((measurable_fst.comp (measurable_fst.comp measurable_snd)).eq_const x₀).setOf.inter
      (measurable_fst.eq_const x₁).setOf

private theorem forwardDrivenLaw_oneWindowEvent
    (initial : Measure (Fin 3)) (G : FiniteJumpGenerator (Fin 3))
    (T : NNReal) (x₀ x₁ : Fin 3) [SFinite initial] :
    forwardDrivenLaw initial (fun _ : Fin 1 => G) (fun _ => T)
        (oneWindowEvent x₀ x₁) =
      initial {x₀} * G.transitionMass T x₀ x₁ := by
  classical
  haveI : SFinite
      (Marked.reversePathMeasure initial
        (fun _ : Fin 0 => G.forwardWindowKernel T)) := by
    unfold Marked.reversePathMeasure
    infer_instance
  have hbase :
      Marked.reversePathMeasure initial
          (fun _ : Fin 0 => G.forwardWindowKernel T)
          {p : Path (Fin 3) 0 | p.1 = x₀} = initial {x₀} := by
    unfold Marked.reversePathMeasure
    rw [show {p : Path (Fin 3) 0 | p.1 = x₀} =
        ({x₀} ×ˢ (Set.univ : Set (Marked.MarkedContinuation
          (Fin 3) (FullPath (Fin 3)) 0))) by ext; simp]
    rw [Measure.compProd_apply_prod (measurableSet_singleton x₀)
      MeasurableSet.univ]
    simp
  rw [forwardDrivenLaw]
  simp only [Marked.reversedForwardPathMeasure]
  rw [Measure.map_apply (Marked.prependEquiv 0).measurable
    (measurableSet_oneWindowEvent x₀ x₁)]
  have hpre : (Marked.prependEquiv (Ω := Fin 3)
      (Λ := FullPath (Fin 3)) 0) ⁻¹' oneWindowEvent x₀ x₁ =
      ({p : Path (Fin 3) 0 | p.1 = x₀} ×ˢ endpointEvent x₁) := by
    ext p
    simp [oneWindowEvent, endpointEvent, Marked.prependEquiv]
  rw [hpre, Measure.compProd_apply_prod
    ((measurable_fst.eq_const x₀).setOf)
    (measurableSet_endpointEvent x₁)]
  have hkernel : ∀ p : Path (Fin 3) 0,
      p.1 = x₀ →
      Marked.endpointKernel (G.forwardWindowKernel T) 0 p
          (endpointEvent x₁) = G.transitionMass T x₀ x₁ := by
    intro p hp
    simp only [Marked.endpointKernel, Kernel.comap_apply]
    rw [hp, forwardWindowKernel_endpointEvent]
  rw [setLIntegral_congr_fun ((measurable_fst.eq_const x₀).setOf) hkernel,
    setLIntegral_const, hbase]
  ring

private def twoWindowEvent (x₀ x₁ x₂ : Fin 3) :
    Set (Path (Fin 3) 2) :=
  (Marked.prependEquiv (Ω := Fin 3) (Λ := FullPath (Fin 3)) 1) ''
    (oneWindowEvent x₀ x₁ ×ˢ endpointEvent x₂)

private theorem measurableSet_twoWindowEvent (x₀ x₁ x₂ : Fin 3) :
    MeasurableSet (twoWindowEvent x₀ x₁ x₂) := by
  exact (Marked.prependEquiv (Ω := Fin 3) (Λ := FullPath (Fin 3)) 1)
    |>.measurableEmbedding.measurableSet_image.mpr
      ((measurableSet_oneWindowEvent x₀ x₁).prod
        (measurableSet_endpointEvent x₂))

private theorem reversedForwardPathMeasure_twoWindowEvent_step
    (initial : Measure (Fin 3))
    (K : Fin 2 → ProbabilityTheory.Kernel (Fin 3)
      (Fin 3 × FullPath (Fin 3)))
    [SFinite
      (Marked.reversedForwardPathMeasure initial (fun i : Fin 1 => K i.castSucc))]
    [IsSFiniteKernel (Marked.endpointKernel (K (Fin.last 1)) 1)]
    (x₀ x₁ x₂ : Fin 3) (c : ℝ≥0∞)
    (hkernel : ∀ p ∈ oneWindowEvent x₀ x₁,
      Marked.endpointKernel (K (Fin.last 1)) 1 p (endpointEvent x₂) = c) :
    Marked.reversedForwardPathMeasure initial K
        (twoWindowEvent x₀ x₁ x₂) =
      Marked.reversedForwardPathMeasure initial
          (fun i : Fin 1 => K i.castSucc) (oneWindowEvent x₀ x₁) * c := by
  calc
    Marked.reversedForwardPathMeasure initial K
        (twoWindowEvent x₀ x₁ x₂) =
        c * Marked.reversedForwardPathMeasure initial
          (fun i : Fin 1 => K i.castSucc) (oneWindowEvent x₀ x₁) := by
      exact Marked.reversedForwardPathMeasure_succ_apply_image_prod
        initial K
        (measurableSet_oneWindowEvent x₀ x₁)
        (measurableSet_endpointEvent x₂) c hkernel
    _ = _ := mul_comm _ _

private theorem reversedForwardPathMeasure_twoWindowEvent
    (initial : Measure (Fin 3)) (duration : Fin 2 → NNReal)
    (x₀ x₁ x₂ : Fin 3) [IsProbabilityMeasure initial] :
    Marked.reversedForwardPathMeasure initial
        (fun i => (generator i).forwardWindowKernel (duration i))
        (twoWindowEvent x₀ x₁ x₂) =
    initial {x₀} *
        genFlat.transitionMass (duration 0) x₀ x₁ *
        genTilted.transitionMass (duration 1) x₁ x₂ := by
  have hkernel : ∀ p : Path (Fin 3) 1,
      p ∈ oneWindowEvent x₀ x₁ →
      Marked.endpointKernel
          (genTilted.forwardWindowKernel (duration 1)) 1 p
          (endpointEvent x₂) =
        genTilted.transitionMass (duration 1) x₁ x₂ := by
    intro p hp
    simp only [Marked.endpointKernel, Kernel.comap_apply]
    rw [show p.1 = x₁ from hp.2, forwardWindowKernel_endpointEvent]
  rw [reversedForwardPathMeasure_twoWindowEvent_step initial
    (fun i => (generator i).forwardWindowKernel (duration i)) x₀ x₁ x₂
    (genTilted.transitionMass (duration 1) x₁ x₂) hkernel]
  have hone :
      Marked.reversedForwardPathMeasure initial
          (fun _ : Fin 1 => genFlat.forwardWindowKernel (duration 0))
          (oneWindowEvent x₀ x₁) =
        initial {x₀} * genFlat.transitionMass (duration 0) x₀ x₁ := by
    simpa [forwardDrivenLaw] using
      (forwardDrivenLaw_oneWindowEvent initial genFlat (duration 0) x₀ x₁)
  have hprefix :
      (fun i : Fin 1 =>
        (generator i.castSucc).forwardWindowKernel (duration i.castSucc)) =
        (fun _ : Fin 1 => genFlat.forwardWindowKernel (duration 0)) := by
    funext i
    fin_cases i
    rfl
  rw [hprefix, hone]

private theorem holdingIntegral_pos
    (G : FiniteJumpGenerator (Fin 3)) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Fin 3) :
    0 < G.holdingIntegral T states := by
  unfold FiniteJumpGenerator.holdingIntegral
  let f : (Fin n → I) → ℝ≥0∞ := fun u =>
    Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
      ENNReal.ofReal
        (Real.exp
          (-((G.escapeRate (states (Fin.last n)) : ℝ) *
            (T : ℝ) * Simplex.residual u)))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  rw [setLIntegral_pos_iff hf]
  have hsupp : Function.support f = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    dsimp [f, Simplex.cubeExpWeight]
    exact (ENNReal.mul_pos
      (by
        apply Finset.prod_ne_zero_iff.2
        intro i hi
        exact ENNReal.ofReal_ne_zero_iff.2 (Real.exp_pos _))
      (ENNReal.ofReal_ne_zero_iff.2 (Real.exp_pos _))).ne'
  rw [hsupp, Set.univ_inter]
  exact Simplex.volume_freeSimplexSet_pos n

private theorem transitionMass_self_pos
    (G : FiniteJumpGenerator (Fin 3)) (T : NNReal) (x : Fin 3) :
    0 < G.transitionMass T x x := by
  let states : Fin 1 → Fin 3 := fun _ => x
  have hsequence : 0 < G.sequenceMass T states := by
    unfold FiniteJumpGenerator.sequenceMass
    simp only [pow_zero, one_mul]
    have hjump : G.jumpProduct states = 1 := by
      simp [FiniteJumpGenerator.jumpProduct]
    rw [hjump, one_mul]
    exact holdingIntegral_pos G T states
  have hsector : 0 < G.sectorTerminalMassFrom T x x 0 := by
    unfold FiniteJumpGenerator.sectorTerminalMassFrom
    have hterm : 0 <
        FiniteJumpGenerator.fixedInitialWeight x (states 0) *
          (FiniteJumpGenerator.fixedInitialWeight x
            (states (Fin.last 0)) * G.sequenceMass T states) := by
      simpa [states] using hsequence
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun s : Fin 1 → Fin 3 =>
          FiniteJumpGenerator.fixedInitialWeight x (s 0) *
            (FiniteJumpGenerator.fixedInitialWeight x (s (Fin.last 0)) *
              G.sequenceMass T s))
        (fun _ _ => zero_le) (Finset.mem_univ states))
  unfold FiniteJumpGenerator.transitionMass
  exact lt_of_lt_of_le hsector (ENNReal.le_tsum 0)

private theorem transitionMass_pos_of_jumpRate_pos
    (G : FiniteJumpGenerator (Fin 3)) (T : NNReal) (hT : 0 < T)
    (x y : Fin 3) (hrate : 0 < G.jumpRate x y) :
    0 < G.transitionMass T x y := by
  let states : Fin 2 → Fin 3 := ![x, y]
  have hsequence : 0 < G.sequenceMass T states := by
    unfold FiniteJumpGenerator.sequenceMass
    have hT' : 0 < (T : ℝ≥0∞) := by exact_mod_cast hT
    have hjump : 0 < G.jumpProduct states := by
      simpa [states, FiniteJumpGenerator.jumpProduct] using
        (show 0 < (G.jumpRate x y : ℝ≥0∞) by exact_mod_cast hrate)
    rw [pow_one]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hT'.ne' hjump.ne').ne'
      (holdingIntegral_pos G T states).ne'
  have hsector : 0 < G.sectorTerminalMassFrom T x y 1 := by
    unfold FiniteJumpGenerator.sectorTerminalMassFrom
    have hterm : 0 <
        FiniteJumpGenerator.fixedInitialWeight x (states 0) *
          (FiniteJumpGenerator.fixedInitialWeight y
            (states (Fin.last 1)) * G.sequenceMass T states) := by
      simpa [states] using hsequence
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun s : Fin 2 → Fin 3 =>
          FiniteJumpGenerator.fixedInitialWeight x (s 0) *
            (FiniteJumpGenerator.fixedInitialWeight y (s (Fin.last 1)) *
              G.sequenceMass T s))
        (fun _ _ => zero_le) (Finset.mem_univ states))
  unfold FiniteJumpGenerator.transitionMass
  exact lt_of_lt_of_le hsector (ENNReal.le_tsum 1)

private theorem gibbs_initial_atom_pos (x : Fin 3) :
    0 < Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0) {x} := by
  rw [FiniteJumpGenerator.gibbsMeasure_count_eq_sum_smul_dirac]
  rw [Measure.sum_apply _ (measurableSet_singleton x)]
  have hweight : 0 < FiniteJumpGenerator.finiteGibbsWeight 1 (energy 0) x := by
    unfold FiniteJumpGenerator.finiteGibbsWeight
    apply ENNReal.ofReal_pos.2
    exact div_pos (Real.exp_pos _)
      (FiniteJumpGenerator.finitePartitionFunction_pos 1 (energy 0))
  simp only [Measure.smul_apply, Measure.dirac_apply' _
    (measurableSet_singleton x), smul_eq_mul]
  calc
    0 < FiniteJumpGenerator.finiteGibbsWeight 1 (energy 0) x := hweight
    _ = FiniteJumpGenerator.finiteGibbsWeight 1 (energy 0) x *
        (Set.indicator ({x} : Set (Fin 3))
          (fun _ => (1 : ℝ≥0∞)) x) := by simp
    _ ≤ ∑' i : Fin 3,
        FiniteJumpGenerator.finiteGibbsWeight 1 (energy 0) i *
          (Set.indicator ({x} : Set (Fin 3))
            (fun _ => (1 : ℝ≥0∞)) i) := ENNReal.le_tsum x

private theorem integrable_initial_boltzmann :
    Integrable (fun x : Fin 3 => Real.exp (-(1 : ℝ) * energy 0 x))
      (Measure.count : Measure (Fin 3)) := by
  apply Integrable.of_bound
    (Measurable.of_discrete : Measurable
      (fun x : Fin 3 => Real.exp (-(1 : ℝ) * energy 0 x))).aestronglyMeasurable
    (∑ x : Fin 3, ‖Real.exp (-(1 : ℝ) * energy 0 x)‖)
  filter_upwards [] with x
  exact Finset.single_le_sum
    (f := fun y : Fin 3 => ‖Real.exp (-(1 : ℝ) * energy 0 y)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ x)

/-- For positive window widths, the realized forward work has a positive atom
at zero. The witness event remains at state `0` in both windows. -/
theorem work_zero_atom_pos (duration : Fin 2 → NNReal)
    (_hduration : ∀ i, 0 < duration i) :
    0 < (forwardDrivenLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration) {γ | work energy γ = 0} := by
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0)) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure (Fin 3)) 1 (energy 0)
      integrable_initial_boltzmann
  have hevent : 0 < forwardDrivenLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration
      (twoWindowEvent 0 0 0) := by
    change 0 < Marked.reversedForwardPathMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      (fun i => (generator i).forwardWindowKernel (duration i))
      (twoWindowEvent 0 0 0)
    rw [reversedForwardPathMeasure_twoWindowEvent]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (gibbs_initial_atom_pos 0).ne'
        (transitionMass_self_pos genFlat (duration 0) 0).ne').ne'
      (transitionMass_self_pos genTilted (duration 1) 0).ne'
  refine lt_of_lt_of_le hevent (measure_mono ?_)
  intro γ hγ
  rcases hγ with ⟨p, hp, rfl⟩
  change work energy
    (p.2.1, ((p.1.1, p.2.2), p.1.2)) = 0
  rw [work_two_eq]
  rw [show p.1.1 = 0 from hp.1.2,
    show p.2.1 = 0 from hp.2]
  simp [energy]

/-- For positive window widths, the realized forward work has a positive atom
at `log 2`. The witness event stays at state `1` in the first window and makes
the positive-rate jump `1 → 0` in the tilted second window. -/
theorem work_log_two_atom_pos (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    0 < (forwardDrivenLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration) {γ | work energy γ = Real.log 2} := by
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0)) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure (Fin 3)) 1 (energy 0)
      integrable_initial_boltzmann
  have hjump : 0 < genTilted.jumpRate 1 0 := by norm_num [genTilted]
  have hevent : 0 < forwardDrivenLaw
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      generator duration
      (twoWindowEvent 1 1 0) := by
    change 0 < Marked.reversedForwardPathMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      (fun i => (generator i).forwardWindowKernel (duration i))
      (twoWindowEvent 1 1 0)
    rw [reversedForwardPathMeasure_twoWindowEvent]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (gibbs_initial_atom_pos 1).ne'
        (transitionMass_self_pos genFlat (duration 0) 1).ne').ne'
      (transitionMass_pos_of_jumpRate_pos genTilted (duration 1)
        (hduration 1) 1 0 hjump).ne'
  refine lt_of_lt_of_le hevent (measure_mono ?_)
  intro γ hγ
  rcases hγ with ⟨p, hp, rfl⟩
  change work energy
    (p.2.1, ((p.1.1, p.2.2), p.1.2)) = Real.log 2
  rw [work_two_eq]
  rw [show p.1.1 = 1 from hp.1.2,
    show p.2.1 = 0 from hp.2]
  simp [energy]

/-! ### The work observable is nonconstant on boundary-consistent paths -/

/-- The zero-jump window path resting at a prescribed state. -/
def restMark (x : Fin 3) : FullPath (Fin 3) :=
  ⟨0, (fun _ => x, fun _ => 0)⟩

/-- The one-jump window path hopping from `x` to `y` halfway through a unit
window: it holds `x` for half a unit, jumps, and holds `y` for the remaining
half. -/
noncomputable def hopMark (x y : Fin 3) : FullPath (Fin 3) :=
  ⟨1, (![x, y], fun _ => 2⁻¹)⟩

/-- The rest mark is a valid real-time trajectory chart for every window
length. -/
theorem restMark_isValid (T : NNReal) (x : Fin 3) :
    FullPath.IsValid T (restMark x) := by
  refine ⟨fun i => i.elim0, ?_⟩
  have h : (Fin.last 0) = (0 : Fin 1) := rfl
  rw [h, JumpPath.jumpTimes_zero]
  exact T.coe_nonneg

/-- Each hop mark is a valid real-time trajectory chart for a unit window: its
single pre-jump holding time is positive and its jump happens by time `1`. -/
theorem hopMark_isValid (x y : Fin 3) :
    FullPath.IsValid 1 (hopMark x y) := by
  refine ⟨fun i => by norm_num, ?_⟩
  have h : Finset.Iio (Fin.last 1) = {(0 : Fin 2)} := by decide
  unfold JumpPath.jumpTimes
  rw [h, Finset.sum_singleton]
  norm_num

/-- On this protocol the endpoint work only sees the raised landscape: on any
two-window carrier it is the middle-state energy difference of the two stored
window endpoints, regardless of the window marks. -/
theorem work_carrier_eq
    (x₀ x₁ x₂ : Fin 3) (w₀ w₁ : FullPath (Fin 3)) :
    work energy (x₂, ((x₁, w₁), ((x₀, w₀), PUnit.unit))) =
      energy 1 x₁ - energy 1 x₂ := by
  rw [work_two_eq]
  show energy 1 x₁ - energy 0 x₁ + (energy 2 x₂ - energy 1 x₂) =
    energy 1 x₁ - energy 1 x₂
  have h0 : energy 0 x₁ = 0 := by fin_cases x₁ <;> simp [energy]
  have h2 : energy 2 x₂ = 0 := by fin_cases x₂ <;> simp [energy]
  rw [h0, h2]
  ring

/-- The boundary-consistent carrier point that rests at `0` through both
windows. -/
def restPath : ConnectedPath (Fin 3) 2 :=
  ⟨(0, ((0, restMark 0), ((0, restMark 0), PUnit.unit))),
    rfl, rfl, rfl, rfl, trivial⟩

/-- A boundary-consistent carrier point that hops `0 → 1` in the first window
and back `1 → 0` in the second, each window mark being a valid unit-window
trajectory chart. -/
noncomputable def hopPath : ConnectedPath (Fin 3) 2 :=
  ⟨(0, ((1, hopMark 1 0), ((0, hopMark 0 1), PUnit.unit))),
    rfl, rfl, rfl, rfl, trivial⟩

/-- Hopping through the raised middle state costs `log 2`. -/
theorem work_hopPath : work energy hopPath.1 = Real.log 2 := by
  have h : work energy hopPath.1 = energy 1 1 - energy 1 0 :=
    work_carrier_eq 0 1 0 (hopMark 0 1) (hopMark 1 0)
  rw [h]
  simp [energy]

/-- Resting through both windows costs nothing. -/
theorem work_restPath : work energy restPath.1 = 0 := by
  have h : work energy restPath.1 = energy 1 0 - energy 1 0 :=
    work_carrier_eq 0 0 0 (restMark 0) (restMark 0)
  rw [h]
  ring

/-- **The endpoint work observable separates two boundary-consistent carrier
points**: hopping through the raised middle state costs `log 2` while resting
costs nothing.  This is a nonconstancy statement about the work observable on
structurally connected paths; it does not by itself assert nondegeneracy of
the pushforward work distribution (for zero window durations the constructed
laws never leave the initial state, so the realized work vanishes almost
surely). -/
theorem work_not_constant :
    work energy hopPath.1 ≠ work energy restPath.1 := by
  rw [work_hopPath, work_restPath]
  exact (Real.log_pos (by norm_num)).ne'

/-! ### The same endpoints, not a function of the endpoints -/

/-- For positive window durations the resting event `twoWindowEvent 0 0 0`
has positive measure, and on it the initial endpoint, the final endpoint and
the realized work are pinned to `0`, `0` and `0`. -/
theorem work_zero_same_endpoints_event_pos (duration : Fin 2 → NNReal)
    (_hduration : ∀ i, 0 < duration i) :
    0 < (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration) (twoWindowEvent 0 0 0) ∧
      ∀ γ ∈ twoWindowEvent 0 0 0,
        Driven.startpointAt γ 0 = 0 ∧
          Driven.endpointAt γ (Fin.last 1) = 0 ∧
          work energy γ = 0 := by
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0)) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure (Fin 3)) 1 (energy 0)
      integrable_initial_boltzmann
  constructor
  · change 0 < Marked.reversedForwardPathMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      (fun i => (generator i).forwardWindowKernel (duration i))
      (twoWindowEvent 0 0 0)
    rw [reversedForwardPathMeasure_twoWindowEvent]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (gibbs_initial_atom_pos 0).ne'
        (transitionMass_self_pos genFlat (duration 0) 0).ne').ne'
      (transitionMass_self_pos genTilted (duration 1) 0).ne'
  · intro γ hγ
    rcases hγ with ⟨p, hp, rfl⟩
    constructor
    · change Driven.startpointAt
          ((p.2.1, ((p.1.1, p.2.2), p.1.2)) : Marked.MarkedPath (Fin 3) (FullPath (Fin 3)) 2)
          (0 : Fin 2) = 0
      rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl]
      rw [Driven.startpointAt_castSucc]
      rw [show (0 : Fin 1) = Fin.last 0 from rfl]
      rw [Driven.startpointAt_last]
      simp [hp.1.1]
    · constructor
      · change Driven.endpointAt
          ((p.2.1, ((p.1.1, p.2.2), p.1.2)) : Marked.MarkedPath (Fin 3) (FullPath (Fin 3)) 2)
          (Fin.last 1) = 0
        rw [Driven.endpointAt_last]
        exact hp.2
      · change work energy (p.2.1, ((p.1.1, p.2.2), p.1.2)) = 0
        rw [work_two_eq]
        rw [show p.1.1 = 0 from hp.1.2]
        rw [show p.2.1 = 0 from hp.2]
        simp [energy]

/-- For positive window durations the hopping event `twoWindowEvent 0 1 0`
has positive measure, and on it the initial and final endpoints are pinned to
`0` while the realized work is `log 2`. -/
theorem work_log_two_same_endpoints_event_pos (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    0 < (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration) (twoWindowEvent 0 1 0) ∧
      ∀ γ ∈ twoWindowEvent 0 1 0,
        Driven.startpointAt γ 0 = 0 ∧
          Driven.endpointAt γ (Fin.last 1) = 0 ∧
          work energy γ = Real.log 2 := by
  letI : IsProbabilityMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0)) :=
    Gibbs.isProbabilityMeasure_measure
      (Measure.count : Measure (Fin 3)) 1 (energy 0)
      integrable_initial_boltzmann
  constructor
  · change 0 < Marked.reversedForwardPathMeasure
      (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
      (fun i => (generator i).forwardWindowKernel (duration i))
      (twoWindowEvent 0 1 0)
    rw [reversedForwardPathMeasure_twoWindowEvent]
    have hjump₀ : 0 < genFlat.jumpRate 0 1 := by norm_num [genFlat]
    have hjump₁ : 0 < genTilted.jumpRate 1 0 := by norm_num [genTilted]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (gibbs_initial_atom_pos 0).ne'
        (transitionMass_pos_of_jumpRate_pos genFlat (duration 0)
          (hduration 0) 0 1 hjump₀).ne').ne'
      (transitionMass_pos_of_jumpRate_pos genTilted (duration 1)
        (hduration 1) 1 0 hjump₁).ne'
  · intro γ hγ
    rcases hγ with ⟨p, hp, rfl⟩
    constructor
    · change Driven.startpointAt
          ((p.2.1, ((p.1.1, p.2.2), p.1.2)) : Marked.MarkedPath (Fin 3) (FullPath (Fin 3)) 2)
          (0 : Fin 2) = 0
      rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl]
      rw [Driven.startpointAt_castSucc]
      rw [show (0 : Fin 1) = Fin.last 0 from rfl]
      rw [Driven.startpointAt_last]
      simp [hp.1.1]
    · constructor
      · change Driven.endpointAt
          ((p.2.1, ((p.1.1, p.2.2), p.1.2)) : Marked.MarkedPath (Fin 3) (FullPath (Fin 3)) 2)
          (Fin.last 1) = 0
        rw [Driven.endpointAt_last]
        exact hp.2
      · change work energy (p.2.1, ((p.1.1, p.2.2), p.1.2)) = Real.log 2
        rw [work_two_eq]
        rw [show p.1.1 = 1 from hp.1.2]
        rw [show p.2.1 = 0 from hp.2]
        simp [energy]

/-! ### The endpoint pair does not determine the realized work -/

/-- An almost-everywhere equality of `work energy` with a function of the
endpoint pair, restricted to a positive event on which the endpoints and the
work are pinned, forces the value of the function at the pinned endpoints. -/
private lemma ae_endpoint_pair_value {x₁ : Fin 3} {v : ℝ}
    (f : Fin 3 → Fin 3 → ℝ) (duration : Fin 2 → NNReal)
    (hf : (work energy) =ᵐ[forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration] fun γ => f (Driven.startpointAt γ 0)
        (Driven.endpointAt γ (Fin.last 1)))
    (hpos : 0 < (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration) (twoWindowEvent 0 x₁ 0))
    (hep : ∀ γ ∈ twoWindowEvent 0 x₁ 0, Driven.startpointAt γ 0 = 0 ∧
        Driven.endpointAt γ (Fin.last 1) = 0 ∧ work energy γ = v) :
    f 0 0 = v := by
  classical
  have hN : (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration) {γ : Path (Fin 3) 2 | work energy γ ≠
      f (Driven.startpointAt γ 0) (Driven.endpointAt γ (Fin.last 1))} = 0 := by
    rw [← ae_iff]
    exact hf
  have hgood : (twoWindowEvent 0 x₁ 0 \ {γ : Path (Fin 3) 2 | work energy γ ≠
      f (Driven.startpointAt γ 0) (Driven.endpointAt γ (Fin.last 1))}).Nonempty := by
    exact MeasureTheory.nonempty_of_measure_ne_zero
      (μ := (forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration))
      (by
        rw [show (forwardDrivenLaw
              (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
              generator duration) (twoWindowEvent 0 x₁ 0 \ {γ : Path (Fin 3) 2 | work energy γ ≠
                f (Driven.startpointAt γ 0) (Driven.endpointAt γ (Fin.last 1))}) =
            (forwardDrivenLaw
              (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
              generator duration) (twoWindowEvent 0 x₁ 0) by
          apply measure_sdiff_null'
          exact measure_mono_null Set.inter_subset_right hN]
        exact ne_of_gt hpos)
  rcases hgood with ⟨γ, hγA, hγN⟩
  have hval : work energy γ = f (Driven.startpointAt γ 0)
      (Driven.endpointAt γ (Fin.last 1)) := by
    by_contra h
    exact hγN (by simpa using h)
  have hs : Driven.startpointAt γ 0 = 0 := (hep γ hγA).1
  have ht : Driven.endpointAt γ (Fin.last 1) = 0 := (hep γ hγA).2.1
  have hwork : work energy γ = v := (hep γ hγA).2.2
  rw [hs, ht] at hval
  rw [hwork] at hval
  exact hval.symm

/-- **The realized work is not almost surely a function of the endpoint pair
alone**: two positive-probability events pin the same endpoint pair `(0, 0)`
but realize the different work values `0` and `log 2`. -/
theorem work_not_ae_initialFinalFunction (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    ¬ ∃ f : Fin 3 → Fin 3 → ℝ,
      (work energy) =ᵐ[forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration] fun γ => f (Driven.startpointAt γ 0)
        (Driven.endpointAt γ (Fin.last 1)) := by
  rintro ⟨f, hf⟩
  have h₀ : f 0 0 = 0 :=
    ae_endpoint_pair_value (x₁ := 0) (v := 0) f duration hf
      (work_zero_same_endpoints_event_pos duration hduration).1
      (work_zero_same_endpoints_event_pos duration hduration).2
  have h₂ : f 0 0 = Real.log 2 :=
    ae_endpoint_pair_value (x₁ := 1) (v := Real.log 2) f duration hf
      (work_log_two_same_endpoints_event_pos duration hduration).1
      (work_log_two_same_endpoints_event_pos duration hduration).2
  have hc : (0 : ℝ) = Real.log 2 := h₀.symm.trans h₂
  exact (Real.log_pos (by norm_num)).ne' hc.symm

/-- The same obstruction holds even for functions of the final state alone. -/
theorem work_not_ae_finalStateFunction (duration : Fin 2 → NNReal)
    (hduration : ∀ i, 0 < duration i) :
    ¬ ∃ f : Fin 3 → ℝ,
      (work energy) =ᵐ[forwardDrivenLaw
        (Gibbs.measure (Measure.count : Measure (Fin 3)) 1 (energy 0))
        generator duration] fun γ => f (Driven.endpointAt γ (Fin.last 1)) := by
  rintro ⟨f, hf⟩
  apply work_not_ae_initialFinalFunction duration hduration
  refine ⟨fun _ y => f y, ?_⟩
  simpa using hf

end ThreeStateTwoWindow
end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
