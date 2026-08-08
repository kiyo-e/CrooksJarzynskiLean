/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenEndpointLaw
import CrooksJarzynski.ContinuousTimeJumpDriven
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorBridge
import CrooksJarzynski.MeasureProtocolFiniteBridge
import CrooksJarzynski.MeasureProtocolMarkedEndpoints
import CrooksJarzynski.TimeReversal

/-!
# Endpoint cylinders are matrix-exponential products

A singleton (point) cylinder of the driven forward law — a complete
prescription of the state sequence over all `M` windows — has mass equal to
the initial atom times the product of the generator matrix exponentials
`exp ((duration i) • (generator i).generator)`.

The carrier of the driven law is **reverse chronological**: the front
coordinate of `Trajectory.ofFn (fun i => states i.rev)` is the *final* state
`states M`.  The event pins the erased path to this singleton trajectory, so
the factors inside the product run along the chronological chain
`states 0 → states 1 → … → states M`, each factor being the transition
probability from the column `exp (tQ) x ·`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace Markov

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The reversed forward path law is σ-finite (`SFinite`) whenever the initial
law and all kernels are. -/
noncomputable instance instSFiniteReversedForwardPathMeasure
    {n : ℕ} (initial : Measure Ω) [SFinite initial]
    (K : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [∀ i, IsSFiniteKernel (K i)] :
    SFinite (reversedForwardPathMeasure initial K) := by
  induction n with
  | zero =>
      simp only [reversedForwardPathMeasure, reversePathMeasure, reverseContinuationKernel]
      infer_instance
  | succ n ih =>
      haveI : SFinite (reversedForwardPathMeasure initial (fun i => K i.castSucc)) :=
        ih (fun i => K i.castSucc)
      haveI : IsSFiniteKernel (endpointKernel (K (Fin.last n)) n) := by
        unfold endpointKernel
        infer_instance
      haveI : SFinite (reversedForwardPathMeasure initial
          (fun i => K i.castSucc) ⊗ₘ endpointKernel (K (Fin.last n)) n) := by
        infer_instance
      simpa only [reversedForwardPathMeasure] using
        (inferInstance : SFinite
          ((reversedForwardPathMeasure initial (fun i => K i.castSucc) ⊗ₘ
            endpointKernel (K (Fin.last n)) n).map (prependEquiv n)))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The first component of `ofFn f` is `f 0`. -/
theorem ofFn_fst {n : ℕ} (f : Fin (n + 1) → Ω) :
    (Trajectory.ofFn f).1 = f 0 := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- The mass of the singleton trajectory built from the reverse of a
chronological chain `x 0 → x 1 → … → x n` factorizes over the single steps. -/
theorem reversedForwardPathMeasure_ofFn_rev {n : ℕ} (initial : Measure Ω)
    [SFinite initial] (K : Fin n → ProbabilityTheory.Kernel Ω Ω)
    [∀ i, IsMarkovKernel (K i)] (x : Fin (n + 1) → Ω) :
    reversedForwardPathMeasure initial K
        {γ : Trajectory Ω n | γ = Trajectory.ofFn (fun i : Fin (n + 1) => x i.rev)} =
      initial {x 0} * ∏ i : Fin n, (K i) (x i.castSucc) {x i.succ} := by
  classical
  induction n with
  | zero =>
      simp only [reversedForwardPathMeasure, reversePathMeasure, reverseContinuationKernel]
      have hf : Trajectory.ofFn (fun i : Fin 1 => x i.rev) =
          (x 0, (PUnit.unit : Continuation Ω 0)) := by
        rfl
      rw [show {γ : Trajectory Ω 0 | γ = Trajectory.ofFn (fun i : Fin 1 => x i.rev)} =
          {γ : Trajectory Ω 0 | γ = (x 0, (PUnit.unit : Continuation Ω 0))} by
        ext γ
        simp [hf]]
      let st : Set (Trajectory Ω 0) :=
        {γ : Trajectory Ω 0 | γ = (x 0, (PUnit.unit : Continuation Ω 0))}
      let K0 : ProbabilityTheory.Kernel Ω (Continuation Ω 0) :=
        ProbabilityTheory.Kernel.deterministic
          (fun _ : Ω => (PUnit.unit : Continuation Ω 0)) measurable_const
      change (initial ⊗ₘ K0) st = initial {x 0} * ∏ i : Fin 0, (K i) (x i.castSucc) {x i.succ}
      rw [show ((initial ⊗ₘ K0) st = ∫⁻ a : Ω, K0 a (Prod.mk a ⁻¹' st) ∂initial) by
        exact Measure.compProd_apply (s := st) (by simp [st] : MeasurableSet st)]
      have hc : ∀ a : Ω, K0 a (Prod.mk a ⁻¹' st) =
          if a = x 0 then (1 : ℝ≥0∞) else 0 := by
        intro a
        have hdet : K0 a (Prod.mk a ⁻¹' st) =
            (Prod.mk a ⁻¹' st).indicator (fun _ => (1 : ℝ≥0∞))
              (PUnit.unit : Continuation Ω 0) := by
          dsimp [K0]
          exact Kernel.deterministic_apply' (by fun_prop : Measurable
              (fun _ : Ω => (PUnit.unit : Continuation Ω 0)))
            a (by
              exact (MeasurableSet.preimage (by simp [st] : MeasurableSet st)
                (measurable_prodMk_left :
                  Measurable (Prod.mk a : Continuation Ω 0 → Ω × Continuation Ω 0))))
        rw [hdet]
        rw [Set.indicator_apply]
        by_cases ha : a = x 0
        · simp [ha, st]; rfl
        · have hn : (a, (PUnit.unit : Continuation Ω 0)) ≠
              (x 0, (PUnit.unit : Continuation Ω 0)) := by
            intro h
            exact ha (by simpa using congrArg Prod.fst h)
          simp [st, ha]
          exact hn
      rw [show (fun a : Ω => K0 a (Prod.mk a ⁻¹' st)) =
          (fun a : Ω => if a = x 0 then (1 : ℝ≥0∞) else 0) by
        funext a
        exact hc a]
      rw [show (fun a : Ω => if a = x 0 then (1 : ℝ≥0∞) else 0) =
          Set.indicator ({x 0} : Set Ω) (fun _ => (1 : ℝ≥0∞)) by
        funext y
        by_cases hy : y = x 0 <;> simp [hy]]
      rw [lintegral_indicator (measurableSet_singleton (x 0))]
      rw [setLIntegral_const ({x 0} : Set Ω) (1 : ℝ≥0∞)]
      simp
  | succ n ih =>
      let y : Fin (n + 1) → Ω := fun j => x j.castSucc
      simp only [reversedForwardPathMeasure]
      -- (0) comprehension ↦ singleton
      rw [show {γ : Trajectory Ω (n + 1) | γ = Trajectory.ofFn (fun i : Fin (n + 2) => x i.rev)} =
          ({Trajectory.ofFn (fun i : Fin (n + 2) => x i.rev)} :
            Set (Trajectory Ω (n + 1))) by
        ext γ
        simp]
      -- (1) move the prepend map to a preimage
      rw [Measure.map_apply (prependEquiv n).measurable
        (measurableSet_singleton
          (Trajectory.ofFn (fun i : Fin (n + 2) => x i.rev)))]
      -- (2) preimage of the point ↦ point under the inverse
      have hset : (prependEquiv n) ⁻¹' ({Trajectory.ofFn (fun i : Fin (n + 2) => x i.rev)} :
            Set (Trajectory Ω (n + 1))) =
          {p : Trajectory Ω n × Ω | p = (prependEquiv n).symm
            (Trajectory.ofFn (fun i : Fin (n + 2) => x i.rev))} := by
        ext p : 2
        simp
        exact Equiv.apply_eq_iff_eq_symm_apply (prependEquiv n).toEquiv
      rw [hset]
      -- (3) the symmetric value is a pair (continuation prefix, front state)
      have hsymm : (prependEquiv n).symm
          (Trajectory.ofFn (fun i : Fin (n + 2) => x i.rev)) =
          (Trajectory.ofFn (fun i : Fin (n + 1) => x (i.succ : Fin (n + 2)).rev),
            x (0 : Fin (n + 2)).rev) := by
        simp [prependEquiv, Trajectory.ofFn]
        rfl
      rw [hsymm]
      -- (4) re-index the continuation with the symmetric chain
      have hren : (fun i : Fin (n + 1) => x (i.succ : Fin (n + 2)).rev) =
          fun i : Fin (n + 1) => y i.rev := by
        funext i
        simp [y]
      rw [hren]
      -- (5) the half pair mass splits
      have hpt : {p : Trajectory Ω n × Ω | p = (Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev),
            x (0 : Fin (n + 2)).rev)} =
          ({(Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev),
            x (0 : Fin (n + 2)).rev)} : Set (Trajectory Ω n × Ω)) := by
        ext p : 2
        simp
      rw [hpt]
      rw [MathlibBridge.compProd_singleton
        (reversedForwardPathMeasure initial (fun j : Fin n => K j.castSucc))
        (endpointKernel (K (Fin.last n)) n)
        (Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev))
        (x (0 : Fin (n + 2)).rev)]
      -- (6) the endpoint kernel reads the front state of the continuation
      have hk : endpointKernel (K (Fin.last n)) n
          (Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev))
          {x (0 : Fin (n + 2)).rev} =
          (K (Fin.last n)) (x (Fin.last n).castSucc) {x (Fin.last n).succ} := by
        rw [endpointKernel]
        rw [Kernel.comap_apply' (K (Fin.last n))
          (by fun_prop : Measurable fun γ : Trajectory Ω n => γ.1)
          (Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev))
          {x (0 : Fin (n + 2)).rev}]
        congr
        · show (Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev)).1 =
            x (Fin.last n).castSucc
          rw [ofFn_fst (fun i : Fin (n + 1) => y i.rev)]
          simp [y]
      rw [hk]
      -- (6b) put the singleton back in the comprehension form for the IH
      rw [show ({Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev)} :
            Set (Trajectory Ω n)) =
          {γ : Trajectory Ω n | γ = Trajectory.ofFn (fun i : Fin (n + 1) => y i.rev)} by
        ext γ
        simp]
      -- (7) apply the induction hypothesis
      rw [ih (fun j : Fin n => K j.castSucc) y]
      -- (8) recombine the product
      rw [Fin.prod_univ_castSucc]
      simp [y, Fin.castSucc_succ, mul_left_comm, mul_comm]

end Markov
end MeasureProtocol
end CrooksJarzynski

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Driven

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- **The driven cylindrical law factorizes over the window chain**: the
`real` probability that the endpoints of all `M + 1` vertices are the
prescribed states equals the initial atom times the product of the
exponential transition weights
`exp ((duration i) • (generator i).generator)`.  The event pins the erased
path to the reverse-chronological singleton `ofFn (states.rev)`; the factors
run along the chronological chain `states 0 → … → states M`. -/
theorem forwardDrivenLaw_endpointCylinder_eq_exp_product
    {M : ℕ} (initial : Measure Ω) [SFinite initial] [IsProbabilityMeasure initial]
    (generator : Fin M → FiniteJumpGenerator Ω)
    (duration : Fin M → NNReal) (states : Fin (M + 1) → Ω) :
    (forwardDrivenLaw initial generator duration).real
        {γ : Path Ω M | ∀ i : Fin (M + 1),
          Trajectory.stateAt (Marked.eraseMarks γ) i = states i.rev} =
      initial.real {states 0} *
        ∏ i : Fin M,
          NormedSpace.exp ((duration i : ℝ) • (generator i).generator)
            (states i.castSucc) (states i.succ) := by
  classical
  have hpre : {γ : Path Ω M | ∀ i : Fin (M + 1),
        Trajectory.stateAt (Marked.eraseMarks γ) i = states i.rev} =
      Marked.eraseMarks ⁻¹'
        ({Trajectory.ofFn (fun i : Fin (M + 1) => states i.rev)} :
          Set (Trajectory Ω M)) := by
    ext p
    constructor
    · intro hp
      apply Trajectory.ext
      intro i
      simpa [Trajectory.stateAt_ofFn] using hp i
    · intro hp i
      have hγ : Trajectory.stateAt (Marked.eraseMarks p) =
          fun j : Fin (M + 1) => states j.rev := by
        simpa [Trajectory.stateAt_ofFn] using (congrArg Trajectory.stateAt hp)
      simp [hγ]
  have hmap : (forwardDrivenLaw initial generator duration).real
        {γ : Path Ω M | ∀ i : Fin (M + 1),
          Trajectory.stateAt (Marked.eraseMarks γ) i = states i.rev} =
      ((forwardDrivenLaw initial generator duration).map Marked.eraseMarks).real
        ({Trajectory.ofFn (fun i : Fin (M + 1) => states i.rev)} :
          Set (Trajectory Ω M)) := by
    rw [hpre]
    simp only [Measure.real_def]
    rw [Measure.map_apply (by fun_prop : Measurable (Marked.eraseMarks :
          Path Ω M → Trajectory Ω M))
      (measurableSet_singleton
        (Trajectory.ofFn (fun i : Fin (M + 1) => states i.rev)))]
  rw [hmap]
  rw [map_forwardDrivenLaw_endpoints initial generator duration]
  simp only [Measure.real_def]
  rw [show ({Trajectory.ofFn (fun i : Fin (M + 1) => states i.rev)} :
        Set (Trajectory Ω M)) =
      {γ : Trajectory Ω M | γ = Trajectory.ofFn (fun i : Fin (M + 1) => states i.rev)} by
    ext γ
    simp]
  rw [Markov.reversedForwardPathMeasure_ofFn_rev (initial := initial)
    (K := fun i => (generator i).transitionKernel (duration i)) (x := states)]
  rw [ENNReal.toReal_mul]
  have hkernel : ∀ i : Fin M,
      ((generator i).pathLawFrom (duration i) (states i.castSucc)).map FullPath.terminalState
          {states i.succ} =
        (generator i).transitionKernel (duration i) (states i.castSucc) {states i.succ} := by
    intro i
    rw [← FiniteJumpGenerator.transitionKernel_apply]
  rw [show (∏ i : Fin M, (((generator i).transitionKernel (duration i))
        (states i.castSucc)) {states i.succ}) = 
      ∏ i ∈ (Finset.univ : Finset (Fin M)), (((generator i).transitionKernel (duration i))
        (states i.castSucc)) {states i.succ} by
    simp]
  rw [ENNReal.toReal_prod (Finset.univ : Finset (Fin M))]
  have hfact : ∀ x : Fin M, (((generator x).transitionKernel (duration x)) (states x.castSucc)
        ({states x.succ} : Set Ω)).toReal =
        NormedSpace.exp ((duration x : ℝ) • (generator x).generator)
          (states x.castSucc) (states x.succ) := by
    intro x
    rw [← Measure.real_def]
    exact FiniteJumpGenerator.transitionKernel_real_singleton_eq_exp_generator
      (generator x) (duration x) (states x.castSucc) (states x.succ)
  rw [show (∏ x : Fin M, (((generator x).transitionKernel (duration x)) (states x.castSucc)
        ({states x.succ} : Set Ω)).toReal) =
      ∏ x : Fin M, NormedSpace.exp ((duration x : ℝ) • (generator x).generator)
        (states x.castSucc) (states x.succ) by
    congr
    funext x
    exact hfact x]
end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski