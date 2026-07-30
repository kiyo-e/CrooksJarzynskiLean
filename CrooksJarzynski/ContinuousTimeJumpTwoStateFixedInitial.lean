/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpTwoStateGenerator

/-!
# Fixed-initial path laws and the two-state Markov semigroup

This module upgrades the generator comparison for the symmetric two-state chain
from a Poisson-flip calculation to an identity for an actual normalized path
law started from a prescribed state. The path law is constructed sector by
sector from the fixed-horizon simplex chart, is concentrated on paths whose
initial coordinate is the prescribed state, and has Poisson jump-count
marginal. Pushing its real terminal coordinate forward gives the corresponding
row of `exp (TQ)`.

The explicit transition probabilities are also shown to satisfy the
Chapman--Kolmogorov identity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace TwoState

/-- The initial state recorded by a complete finite-jump path. -/
def FullPath.initialState : FullPath State → State
  | ⟨_, γ⟩ => γ.1 0

/-- The terminal state recorded by a complete finite-jump path. -/
def FullPath.terminalState : FullPath State → State
  | ⟨n, γ⟩ => γ.1 (Fin.last n)

@[fun_prop]
theorem FullPath.measurable_initialState :
    Measurable FullPath.initialState := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun γ : JumpPath State n => γ.1 0) ⁻¹' s)
  exact ((measurable_pi_apply 0).comp measurable_fst) hs

@[fun_prop]
theorem FullPath.measurable_terminalState :
    Measurable FullPath.terminalState := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet
    ((fun γ : JumpPath State n => γ.1 (Fin.last n)) ⁻¹' s)
  exact ((measurable_pi_apply (Fin.last n)).comp measurable_fst) hs

/-- Assemble the deterministic alternating state sequence started at `x` with
free simplex holding-time coordinates. -/
def assembleAlternatingPath {n : ℕ} (T : NNReal) (x : State)
    (u : Fin n → I) : JumpPath State n :=
  (alternatingStates n x, Simplex.holdingTimesOfFree T u)

@[fun_prop]
theorem measurable_assembleAlternatingPath {n : ℕ} (T : NNReal) (x : State) :
    Measurable (assembleAlternatingPath (n := n) T x) := by
  unfold assembleAlternatingPath
  exact Measurable.prodMk measurable_const
    (Simplex.measurable_holdingTimesOfFree T)

/-- The normalized geometric law on one fixed-jump-count sector, with the
initial state fixed to `x`. -/
noncomputable def fixedInitialPathProbability (T : NNReal) (x : State) (n : ℕ) :
    Measure (JumpPath State n) :=
  (Simplex.freeSimplexProbability n).map
    (assembleAlternatingPath (n := n) T x)

noncomputable instance instIsProbabilityMeasureFixedInitialPathProbability
    (T : NNReal) (x : State) (n : ℕ) :
    IsProbabilityMeasure (fixedInitialPathProbability T x n) := by
  unfold fixedInitialPathProbability
  exact Measure.isProbabilityMeasure_map
    (measurable_assembleAlternatingPath T x).aemeasurable

/-- The fixed-initial geometric sector law is concentrated on the physical
horizon. -/
theorem fixedInitialPathProbability_ae_horizon
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialPathProbability T x n,
      γ ∈ JumpPath.horizonSet (Ω := State) (n := n) T := by
  have hf := measurable_assembleAlternatingPath (n := n) T x
  change ∀ᵐ γ ∂fixedInitialPathProbability T x n,
    JumpPath.totalHoldingTime γ = T
  unfold fixedInitialPathProbability
  rw [ae_map_iff hf.aemeasurable (by
    simpa [JumpPath.horizonSet] using
      (JumpPath.measurableSet_horizonSet (Ω := State) (n := n) T))]
  have hmem : ∀ᵐ u ∂Simplex.freeSimplexProbability n,
      u ∈ Simplex.freeSimplexSet n := by
    unfold Simplex.freeSimplexProbability
    exact ProbabilityTheory.ae_cond_mem
      (Simplex.measurableSet_freeSimplexSet n)
  exact hmem.mono fun u hu => by
    simpa [assembleAlternatingPath, JumpPath.totalHoldingTime] using
      (Simplex.sum_holdingTimesOfFree T u hu)

/-- The fixed-initial geometric sector law records the prescribed initial
state almost surely. -/
theorem fixedInitialPathProbability_ae_initialState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialPathProbability T x n, γ.1 0 = x := by
  have hf := measurable_assembleAlternatingPath (n := n) T x
  have hmeas : Measurable (fun γ : JumpPath State n => γ.1 0) :=
    (measurable_pi_apply 0).comp measurable_fst
  unfold fixedInitialPathProbability
  rw [ae_map_iff hf.aemeasurable (hmeas.eq_const x).setOf]
  exact ae_of_all _ fun _ => rfl

/-- The fixed-initial geometric sector law is concentrated on alternating state
sequences. -/
theorem fixedInitialPathProbability_ae_alternates
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialPathProbability T x n, Alternates γ.1 := by
  have hf := measurable_assembleAlternatingPath (n := n) T x
  unfold fixedInitialPathProbability
  rw [ae_map_iff hf.aemeasurable (measurableSet_pathAlternatesSet n)]
  exact ae_of_all _ fun _ => alternatingStates_alternates n x

/-- The terminal coordinate in the `n`-jump fixed-initial geometric sector is
the `n`-fold flip of the prescribed initial state. -/
theorem fixedInitialPathProbability_ae_terminalState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialPathProbability T x n,
      γ.1 (Fin.last n) = iterateFlip n x := by
  have hf := measurable_assembleAlternatingPath (n := n) T x
  have hmeas : Measurable
      (fun γ : JumpPath State n => γ.1 (Fin.last n)) :=
    (measurable_pi_apply (Fin.last n)).comp measurable_fst
  unfold fixedInitialPathProbability
  rw [ae_map_iff hf.aemeasurable
    (hmeas.eq_const (iterateFlip n x)).setOf]
  exact ae_of_all _ fun _ => by
    simp [assembleAlternatingPath, alternatingStates]

/-- Scale the fixed-initial geometric probability by the physical simplex
volume `T^n / n!`. -/
noncomputable def fixedInitialSectorReference
    (T : NNReal) (x : State) (n : ℕ) : Measure (JumpPath State n) :=
  simplexMass T n • fixedInitialPathProbability T x n

/-- The fixed-initial sector reference has the same geometric mass as the
uniform-initial reference. -/
theorem fixedInitialSectorReference_univ
    (T : NNReal) (x : State) (n : ℕ) :
    fixedInitialSectorReference T x n Set.univ = simplexMass T n := by
  simp [fixedInitialSectorReference]

/-- The fixed-initial sector reference is concentrated on the physical
horizon. -/
theorem fixedInitialSectorReference_ae_horizon
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialSectorReference T x n,
      γ ∈ JumpPath.horizonSet (Ω := State) (n := n) T := by
  unfold fixedInitialSectorReference
  exact Measure.ae_smul_measure
    (fixedInitialPathProbability_ae_horizon T x n) _

/-- The fixed-initial sector reference records its prescribed initial state
almost surely. -/
theorem fixedInitialSectorReference_ae_initialState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialSectorReference T x n, γ.1 0 = x := by
  unfold fixedInitialSectorReference
  exact Measure.ae_smul_measure
    (fixedInitialPathProbability_ae_initialState T x n) _

/-- The fixed-initial sector reference is concentrated on alternating state
sequences. -/
theorem fixedInitialSectorReference_ae_alternates
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialSectorReference T x n, Alternates γ.1 := by
  unfold fixedInitialSectorReference
  exact Measure.ae_smul_measure
    (fixedInitialPathProbability_ae_alternates T x n) _

/-- The fixed-initial sector reference has the deterministic terminal state
prescribed by the jump count. -/
theorem fixedInitialSectorReference_ae_terminalState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂fixedInitialSectorReference T x n,
      γ.1 (Fin.last n) = iterateFlip n x := by
  unfold fixedInitialSectorReference
  exact Measure.ae_smul_measure
    (fixedInitialPathProbability_ae_terminalState T x n) _

/-- The symmetric-chain rate density is the constant survival factor on the
fixed-initial sector reference. -/
theorem fixedInitialRateDensity_ae_eq_survivalWeight
    (T : NNReal) (x : State) (n : ℕ) :
    JumpPath.rateDensity endpointWeight escapeRate jumpRate =ᵐ[
      fixedInitialSectorReference T x n] fun _ => survivalWeight T := by
  filter_upwards [fixedInitialSectorReference_ae_alternates T x n,
    fixedInitialSectorReference_ae_horizon T x n] with γ halternates hhorizon
  exact rateDensity_eq_survivalWeight γ halternates hhorizon

/-- The actual symmetric CTMC law in one jump-count sector, started from `x`. -/
noncomputable def sectorLawFrom (T : NNReal) (x : State) (n : ℕ) :
    Measure (JumpPath State n) :=
  pathMeasure (fixedInitialSectorReference T x n)
    (JumpPath.rateDensity endpointWeight escapeRate jumpRate)

/-- A fixed-initial sector law is its geometric reference scaled by the survival
factor. -/
theorem sectorLawFrom_eq_smul_reference
    (T : NNReal) (x : State) (n : ℕ) :
    sectorLawFrom T x n =
      survivalWeight T • fixedInitialSectorReference T x n := by
  unfold sectorLawFrom pathMeasure
  calc
    (fixedInitialSectorReference T x n).withDensity
        (JumpPath.rateDensity endpointWeight escapeRate jumpRate) =
      (fixedInitialSectorReference T x n).withDensity
        (fun _ => survivalWeight T) :=
      MeasureTheory.withDensity_congr_ae
        (fixedInitialRateDensity_ae_eq_survivalWeight T x n)
    _ = survivalWeight T • fixedInitialSectorReference T x n := by
      exact MeasureTheory.withDensity_const
        (μ := fixedInitialSectorReference T x n) (survivalWeight T)

/-- The mass of the fixed-initial `n`-jump sector is the Poisson probability. -/
theorem sectorLawFrom_univ_eq_poisson
    (T : NNReal) (x : State) (n : ℕ) :
    sectorLawFrom T x n Set.univ = poissonMeasure T {n} := by
  rw [sectorLawFrom_eq_smul_reference, Measure.smul_apply,
    fixedInitialSectorReference_univ,
    ProbabilityTheory.poissonMeasure_singleton]
  rw [simplexMass_eq_ofReal]
  unfold survivalWeight
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

/-- The fixed-initial sector law records its initial state almost surely. -/
theorem sectorLawFrom_ae_initialState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂sectorLawFrom T x n, γ.1 0 = x := by
  unfold sectorLawFrom pathMeasure
  apply ae_iff.mpr
  exact (MeasureTheory.withDensity_absolutelyContinuous
    (fixedInitialSectorReference T x n)
    (JumpPath.rateDensity endpointWeight escapeRate jumpRate))
      (ae_iff.mp (fixedInitialSectorReference_ae_initialState T x n))

/-- The fixed-initial sector law has the terminal state dictated by its jump
count almost surely. -/
theorem sectorLawFrom_ae_terminalState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂sectorLawFrom T x n,
      γ.1 (Fin.last n) = iterateFlip n x := by
  unfold sectorLawFrom pathMeasure
  apply ae_iff.mpr
  exact (MeasureTheory.withDensity_absolutelyContinuous
    (fixedInitialSectorReference T x n)
    (JumpPath.rateDensity endpointWeight escapeRate jumpRate))
      (ae_iff.mp (fixedInitialSectorReference_ae_terminalState T x n))

/-- The normalized full finite-jump path law of the symmetric chain started
from the prescribed state `x`. -/
noncomputable def pathLawFrom (T : NNReal) (x : State) :
    Measure (FullPath State) :=
  FullPath.measure (sectorLawFrom T x)

/-- The fixed-initial sector masses sum to one. -/
theorem tsum_sectorLawFrom_univ (T : NNReal) (x : State) :
    ∑' n, sectorLawFrom T x n Set.univ = 1 := by
  calc
    (∑' n, sectorLawFrom T x n Set.univ) =
        ∑' n, poissonMeasure T {n} := by
      apply tsum_congr
      exact sectorLawFrom_univ_eq_poisson T x
    _ = 1 := by
      simpa only [sectorLaw_univ_eq_poisson] using tsum_sectorLaw_univ T

noncomputable instance instIsProbabilityMeasurePathLawFrom
    (T : NNReal) (x : State) : IsProbabilityMeasure (pathLawFrom T x) := by
  unfold pathLawFrom
  exact FullPath.isProbabilityMeasure_measure (sectorLawFrom T x)
    (tsum_sectorLawFrom_univ T x)

/-- The jump-count marginal of the fixed-initial path law is Poisson. -/
theorem map_pathLawFrom_jumpCount (T : NNReal) (x : State) :
    (pathLawFrom T x).map FullPath.jumpCount = poissonMeasure T := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply FullPath.measurable_jumpCount
    (MeasurableSet.singleton n)]
  unfold pathLawFrom FullPath.measure
  rw [Measure.sum_apply _ (MeasurableSet.preimage
    (MeasurableSet.singleton n) FullPath.measurable_jumpCount)]
  have hlift : ∀ i : ℕ,
      FullPath.liftMeasure i (sectorLawFrom T x i)
          (FullPath.jumpCount ⁻¹' ({n} : Set ℕ)) =
        if i = n then sectorLawFrom T x i Set.univ else 0 := by
    intro i
    unfold FullPath.liftMeasure
    rw [Measure.map_apply (FullPath.measurable_mk i)
      (MeasurableSet.preimage (MeasurableSet.singleton n)
        FullPath.measurable_jumpCount)]
    have hpre :
        Sigma.mk i ⁻¹' FullPath.jumpCount ⁻¹' ({n} : Set ℕ) =
          if i = n then Set.univ else ∅ := by
      ext γ
      simp [FullPath.jumpCount]
    rw [hpre]
    by_cases hin : i = n
    · simp [hin]
    · simp [hin]
  simp_rw [hlift]
  rw [tsum_ite_eq n, sectorLawFrom_univ_eq_poisson]

private theorem liftMeasure_ae_initialState
    (T : NNReal) (x : State) (n : ℕ) :
    ∀ᵐ γ ∂FullPath.liftMeasure n (sectorLawFrom T x n),
      FullPath.initialState γ = x := by
  change ∀ᵐ γ ∂Measure.map (Sigma.mk n) (sectorLawFrom T x n),
    FullPath.initialState γ = x
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable
    (FullPath.measurable_initialState.eq_const x).setOf]
  exact (sectorLawFrom_ae_initialState T x n).mono fun γ hγ => by
    simpa [FullPath.initialState] using hγ

/-- The full fixed-initial path law records `x` in its own initial coordinate
almost surely. -/
theorem pathLawFrom_ae_initialState (T : NNReal) (x : State) :
    ∀ᵐ γ ∂pathLawFrom T x, FullPath.initialState γ = x := by
  have heq : MeasurableSet
      {γ : FullPath State | FullPath.initialState γ = x} :=
    FullPath.measurable_initialState (measurableSet_singleton x)
  have hbad : MeasurableSet
      {γ : FullPath State | ¬ FullPath.initialState γ = x} := by
    change MeasurableSet
      ({γ : FullPath State | FullPath.initialState γ = x}ᶜ)
    exact heq.compl
  apply ae_iff.mpr
  unfold pathLawFrom FullPath.measure
  rw [Measure.sum_apply _ hbad, ENNReal.tsum_eq_zero]
  intro n
  exact ae_iff.mp (liftMeasure_ae_initialState T x n)

private theorem measurable_expectedTerminal (x : State) :
    Measurable (fun γ : FullPath State =>
      iterateFlip (FullPath.jumpCount γ) x) :=
  ((Measurable.of_discrete :
      Measurable (fun n : ℕ => iterateFlip n x)).comp
    FullPath.measurable_jumpCount)

private theorem liftMeasure_ae_terminalState
    (T : NNReal) (x : State) (n : ℕ) :
    FullPath.terminalState =ᵐ[FullPath.liftMeasure n (sectorLawFrom T x n)]
      fun γ => iterateFlip (FullPath.jumpCount γ) x := by
  have heq : MeasurableSet {γ : FullPath State |
      FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x} :=
    (FullPath.measurable_terminalState.eq (measurable_expectedTerminal x)).setOf
  change ∀ᵐ γ ∂Measure.map (Sigma.mk n) (sectorLawFrom T x n),
    FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable heq]
  exact (sectorLawFrom_ae_terminalState T x n).mono fun γ hγ => by
    simpa [FullPath.terminalState, FullPath.jumpCount] using hγ

/-- Under the fixed-initial path law, the real terminal coordinate is the
initial state flipped once for every recorded jump. -/
theorem pathLawFrom_ae_terminalState (T : NNReal) (x : State) :
    FullPath.terminalState =ᵐ[pathLawFrom T x]
      fun γ => iterateFlip (FullPath.jumpCount γ) x := by
  have heq : MeasurableSet {γ : FullPath State |
      FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x} :=
    (FullPath.measurable_terminalState.eq (measurable_expectedTerminal x)).setOf
  have hbad : MeasurableSet {γ : FullPath State |
      ¬ FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x} := by
    change MeasurableSet ({γ : FullPath State |
      FullPath.terminalState γ = iterateFlip (FullPath.jumpCount γ) x}ᶜ)
    exact heq.compl
  apply ae_iff.mpr
  unfold pathLawFrom FullPath.measure
  rw [Measure.sum_apply _ hbad, ENNReal.tsum_eq_zero]
  intro n
  exact ae_iff.mp (liftMeasure_ae_terminalState T x n)

/-- The terminal-state pushforward of the actual fixed-initial path law is the
Poisson-flip law. -/
theorem map_pathLawFrom_terminalState (T : NNReal) (x : State) :
    (pathLawFrom T x).map FullPath.terminalState =
      conditionalTerminalLaw T x := by
  rw [Measure.map_congr (pathLawFrom_ae_terminalState T x)]
  unfold conditionalTerminalLaw
  rw [← map_pathLawFrom_jumpCount T x]
  simpa [Function.comp_def] using
    (Measure.map_map
      (μ := pathLawFrom T x)
      (g := fun n : ℕ => iterateFlip n x)
      (f := FullPath.jumpCount)
      Measurable.of_discrete FullPath.measurable_jumpCount).symm

/-- The actual terminal-state marginal of the normalized path law started from
`x` is the corresponding entry of `exp (TQ)`. -/
theorem pathLawFrom_terminalState_eq_exp_generator
    (T : NNReal) (x y : State) :
    ((pathLawFrom T x).map FullPath.terminalState).real {y} =
      NormedSpace.exp
        ((T : ℝ) •
          (show Matrix State State ℝ from fun x y => generator x y)) x y := by
  rw [map_pathLawFrom_terminalState,
    conditionalTerminalLaw_eq_exp_generator]

/-- At time zero, the explicit transition probabilities reduce to the identity
matrix. -/
theorem transitionProbability_zero (x y : State) :
    transitionProbability 0 x y = if x = y then 1 else 0 := by
  cases x <;> cases y <;> simp [transitionProbability]

/-- The explicit transition probabilities satisfy Chapman--Kolmogorov. -/
theorem transitionProbability_chapman_kolmogorov
    (S T : NNReal) (x y : State) :
    (∑ z : State,
      transitionProbability (S : ℝ) x z *
        transitionProbability (T : ℝ) z y) =
      transitionProbability ((S + T : NNReal) : ℝ) x y := by
  have hmul :
      Real.exp (-(S : ℝ) * 2) * Real.exp (-(T : ℝ) * 2) =
        Real.exp (-(S : ℝ) * 2 - (T : ℝ) * 2) := by
    rw [← Real.exp_add]
  rw [show (Finset.univ : Finset State) = {.zero, .one} by decide,
    Finset.sum_pair (by decide)]
  cases x <;> cases y <;>
    simp [transitionProbability] <;> nlinarith [hmul]

end TwoState
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
