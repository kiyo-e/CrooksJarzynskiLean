/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MeasureProtocolPhysical
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Metropolis--Hastings kernels on a general state space

This module constructs a Metropolis--Hastings kernel from a Markov proposal
that is symmetric with respect to the reference measure. It proves detailed
balance for the corresponding Gibbs measure, then instantiates the construction
on `ℝ` with Lebesgue reference measure, Gaussian random-walk proposals, and
quadratic energies.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski
namespace MeasureProtocol

universe u

namespace MetropolisHastings

variable {X : Type u} [MeasurableSpace X]

/-- The textbook Metropolis acceptance probability for an energy `E`. -/
noncomputable def acceptance (β : ℝ) (E : X → ℝ) (x y : X) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Real.exp (-β * (E y - E x))))

/-- The Metropolis acceptance probability is jointly measurable. -/
theorem measurable_acceptance (β : ℝ) {E : X → ℝ} (hE : Measurable E) :
    Measurable (Function.uncurry (acceptance β E)) := by
  unfold acceptance
  fun_prop

omit [MeasurableSpace X] in
/-- The Metropolis acceptance probability is at most one. -/
theorem acceptance_le_one (β : ℝ) (E : X → ℝ) (x y : X) :
    acceptance β E x y ≤ 1 := by
  rw [acceptance, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-- The accepted-move subkernel. -/
noncomputable def acceptedKernel
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q] (β : ℝ) (E : X → ℝ) :
    ProbabilityTheory.Kernel X X :=
  Q.withDensity (acceptance β E)

/-- The probability of rejecting a proposal at the current state. -/
noncomputable def rejectionMass
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q] (β : ℝ) (E : X → ℝ) (x : X) :
    ℝ≥0∞ :=
  1 - acceptedKernel Q β E x Set.univ

/-- The rejected-move subkernel, concentrated at the current state. -/
noncomputable def rejectionKernel
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q] (β : ℝ) (E : X → ℝ) :
    ProbabilityTheory.Kernel X X :=
  (Kernel.deterministic id measurable_id).withDensity
    (fun x _ => rejectionMass Q β E x)

/-- The Metropolis--Hastings transition kernel. -/
noncomputable def mhKernel
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q] (β : ℝ) (E : X → ℝ) :
    ProbabilityTheory.Kernel X X :=
  acceptedKernel Q β E + rejectionKernel Q β E

theorem acceptedKernel_univ_le_one
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q] (β : ℝ)
    {E : X → ℝ} (hE : Measurable E) (x : X) :
    acceptedKernel Q β E x Set.univ ≤ 1 := by
  rw [acceptedKernel, Kernel.withDensity_apply' Q
    (measurable_acceptance β hE) x Set.univ]
  calc
    ∫⁻ y in Set.univ, acceptance β E x y ∂Q x ≤
        ∫⁻ _ in Set.univ, 1 ∂Q x :=
      lintegral_mono fun y => acceptance_le_one β E x y
    _ = 1 := by simp

theorem isMarkovKernel_mhKernel
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q] (β : ℝ)
    (E : X → ℝ) (hE : Measurable E) :
    IsMarkovKernel (mhKernel Q β E) := by
  letI : IsFiniteKernel (acceptedKernel Q β E) :=
    Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top
      (acceptance_le_one β E)
  have hrMeas : Measurable (rejectionMass Q β E) := by
    unfold rejectionMass
    exact Measurable.const_sub
      ((acceptedKernel Q β E).measurable_coe MeasurableSet.univ) 1
  letI : IsFiniteKernel (rejectionKernel Q β E) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (Kernel.deterministic id measurable_id) ENNReal.one_ne_top fun x y => by
        exact tsub_le_self
  refine ⟨fun x => ⟨?_⟩⟩
  rw [mhKernel, Kernel.add_apply, Measure.add_apply]
  rw [rejectionKernel, Kernel.withDensity_apply'
    (Kernel.deterministic id measurable_id) (by
      exact hrMeas.comp measurable_fst) x Set.univ]
  rw [setLIntegral_const]
  simp only [Kernel.deterministic_apply, measure_univ, mul_one, rejectionMass]
  exact add_tsub_cancel_of_le (acceptedKernel_univ_le_one Q β hE x)

/-- The density of the Gibbs measure with respect to its reference measure. -/
noncomputable def gibbsDensity
    (base : Measure X) (β : ℝ) (E : X → ℝ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-β * E x) / ∫ z, Real.exp (-β * E z) ∂base)

theorem measurable_gibbsDensity
    (base : Measure X) (β : ℝ) {E : X → ℝ} (hE : Measurable E) :
    Measurable (gibbsDensity base β E) := by
  unfold gibbsDensity
  fun_prop

omit [MeasurableSpace X] in
/-- Multiplying a Boltzmann weight by the Metropolis acceptance probability
gives the smaller of the two endpoint Boltzmann weights. -/
theorem boltzmann_mul_acceptance
    (β : ℝ) (E : X → ℝ) (x y : X) :
    ENNReal.ofReal (Real.exp (-β * E x)) * acceptance β E x y =
      min (ENNReal.ofReal (Real.exp (-β * E x)))
        (ENNReal.ofReal (Real.exp (-β * E y))) := by
  rw [acceptance, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_min]
  congr 1
  have hexp :
      Real.exp (-β * E y) =
        Real.exp (-β * E x) *
          Real.exp (-β * (E y - E x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rcases le_total (Real.exp (-β * (E y - E x))) 1 with h | h
  · rw [min_eq_right h]
    have hxy : Real.exp (-β * E y) ≤ Real.exp (-β * E x) := by
      rw [hexp]
      nlinarith [Real.exp_pos (-β * E x)]
    rw [min_eq_right hxy, hexp]
  · rw [min_eq_left h]
    have hxy : Real.exp (-β * E x) ≤ Real.exp (-β * E y) := by
      rw [hexp]
      nlinarith [Real.exp_pos (-β * E x)]
    rw [min_eq_left hxy, mul_one]

noncomputable def acceptedWeight
    (base : Measure X) (β : ℝ) (E : X → ℝ) (p : X × X) : ℝ≥0∞ :=
  gibbsDensity base β E p.1 * acceptance β E p.1 p.2

theorem measurable_acceptedWeight
    (base : Measure X) (β : ℝ) {E : X → ℝ} (hE : Measurable E) :
    Measurable (acceptedWeight base β E) := by
  unfold acceptedWeight
  exact
    ((measurable_gibbsDensity base β hE).comp measurable_fst).mul
      (measurable_acceptance β hE)

theorem acceptedWeight_swap
    (base : Measure X) [NeZero base] (β : ℝ)
    {E : X → ℝ}
    (_hEInt : Integrable (fun x => Real.exp (-β * E x)) base) :
    acceptedWeight base β E ∘ Prod.swap =
      acceptedWeight base β E := by
  have hZinv : (0 : ℝ) ≤ (∫ z, Real.exp (-β * E z) ∂base)⁻¹ :=
    inv_nonneg.mpr (integral_nonneg fun z => (Real.exp_pos _).le)
  have key : ∀ x y : X,
      gibbsDensity base β E x * acceptance β E x y =
        ENNReal.ofReal ((∫ z, Real.exp (-β * E z) ∂base)⁻¹) *
          min (ENNReal.ofReal (Real.exp (-β * E x)))
            (ENNReal.ofReal (Real.exp (-β * E y))) := by
    intro x y
    unfold gibbsDensity
    rw [div_eq_mul_inv, mul_comm (Real.exp (-β * E x)),
      ENNReal.ofReal_mul hZinv, mul_assoc, boltzmann_mul_acceptance]
  funext p
  simp only [Function.comp_apply]
  unfold acceptedWeight
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [key, key, min_comm]

/-- The accepted-move path measure is invariant under swapping its endpoints. -/
theorem accepted_detailedBalance
    (base : Measure X) [SFinite base] [NeZero base]
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q]
    (β : ℝ) (E : X → ℝ) (hE : Measurable E)
    (hEInt : Integrable (fun x => Real.exp (-β * E x)) base)
    (hsym : base ⊗ₘ Q = (base ⊗ₘ Q).map Prod.swap) :
    Gibbs.measure base β E ⊗ₘ acceptedKernel Q β E =
      (Gibbs.measure base β E ⊗ₘ acceptedKernel Q β E).map Prod.swap := by
  letI : IsFiniteKernel (Q.withDensity (acceptance β E)) :=
    Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top
      (acceptance_le_one β E)
  have haccept := measurable_acceptance β hE
  have hgibbs := measurable_gibbsDensity base β hE
  have hweight := measurable_acceptedWeight base β hE
  haveI : SFinite (Gibbs.measure base β E) := by
    unfold Gibbs.measure Measure.tilted
    infer_instance
  have hgfst : Measurable (fun p : X × X => gibbsDensity base β E p.1) :=
    hgibbs.comp measurable_fst
  have hacc2 : Measurable (fun p : X × X => acceptance β E p.1 p.2) :=
    haccept
  have hmeasure :
      Gibbs.measure base β E ⊗ₘ acceptedKernel Q β E =
        (base ⊗ₘ Q).withDensity (acceptedWeight base β E) := by
    rw [acceptedKernel, Measure.compProd_withDensity haccept]
    unfold Gibbs.measure Measure.tilted
    change
      (base.withDensity (gibbsDensity base β E) ⊗ₘ Q).withDensity
          (fun p => acceptance β E p.1 p.2) =
        (base ⊗ₘ Q).withDensity (acceptedWeight base β E)
    rw [← Markov.compProd_withDensity_fst base Q
      (gibbsDensity base β E) hgibbs]
    rw [← withDensity_mul (base ⊗ₘ Q) hgfst hacc2]
    rfl
  rw [hmeasure]
  calc
    (base ⊗ₘ Q).withDensity (acceptedWeight base β E) =
        ((base ⊗ₘ Q).map Prod.swap).withDensity
          (acceptedWeight base β E) := by rw [← hsym]
    _ = ((base ⊗ₘ Q).withDensity
          (acceptedWeight base β E ∘ Prod.swap)).map Prod.swap :=
      map_withDensity (base ⊗ₘ Q) Prod.swap
        (acceptedWeight base β E) measurable_swap hweight
    _ = ((base ⊗ₘ Q).withDensity
          (acceptedWeight base β E)).map Prod.swap := by
      rw [acceptedWeight_swap base β hEInt]

/-- The rejected-move path measure is invariant under swapping its equal
endpoints. -/
theorem rejection_detailedBalance
    (base : Measure X) [SFinite base] [NeZero base]
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q]
    (β : ℝ) (E : X → ℝ) (_hE : Measurable E)
    (_hEInt : Integrable (fun x => Real.exp (-β * E x)) base) :
    Gibbs.measure base β E ⊗ₘ rejectionKernel Q β E =
      (Gibbs.measure base β E ⊗ₘ rejectionKernel Q β E).map Prod.swap := by
  letI : IsFiniteKernel (acceptedKernel Q β E) :=
    Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top
      (acceptance_le_one β E)
  have hr : Measurable (rejectionMass Q β E) := by
    unfold rejectionMass
    exact Measurable.const_sub
      ((acceptedKernel Q β E).measurable_coe MeasurableSet.univ) 1
  letI : IsFiniteKernel (rejectionKernel Q β E) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (Kernel.deterministic id measurable_id) ENNReal.one_ne_top fun x y => by
        exact tsub_le_self
  letI : IsFiniteKernel
      ((Kernel.deterministic (id : X → X) measurable_id).withDensity
        (fun x _ => rejectionMass Q β E x)) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (Kernel.deterministic id measurable_id) ENNReal.one_ne_top fun x y => by
        exact tsub_le_self
  haveI : SFinite (Gibbs.measure base β E) := by
    unfold Gibbs.measure Measure.tilted
    infer_instance
  let π := Gibbs.measure base β E
  haveI : SFinite π := inferInstanceAs (SFinite (Gibbs.measure base β E))
  let ν := π.withDensity (rejectionMass Q β E)
  have hmeasure :
      π ⊗ₘ rejectionKernel Q β E =
        ν.map (fun x => (x, x)) := by
    rw [rejectionKernel, Measure.compProd_withDensity]
    swap
    · exact hr.comp measurable_fst
    rw [Measure.compProd_deterministic]
    exact map_withDensity π (fun x => (x, x))
      (fun p => rejectionMass Q β E p.1)
      (measurable_id.prod measurable_id) (hr.comp measurable_fst)
  rw [show Gibbs.measure base β E = π by rfl, hmeasure]
  rw [Measure.map_map measurable_swap
    (measurable_id.prod measurable_id)]
  change ν.map (fun x => (x, x)) = ν.map (fun x => (x, x))
  rfl

/-- A Metropolis--Hastings kernel is reversible for the Gibbs measure whenever
its proposal is symmetric with respect to the Gibbs reference measure. -/
theorem detailedBalance
    (base : Measure X) [SFinite base] [NeZero base]
    (Q : ProbabilityTheory.Kernel X X) [IsMarkovKernel Q]
    (β : ℝ) (E : X → ℝ) (hE : Measurable E)
    (hEInt : Integrable (fun x => Real.exp (-β * E x)) base)
    (hsym : base ⊗ₘ Q = (base ⊗ₘ Q).map Prod.swap) :
    Gibbs.measure base β E ⊗ₘ mhKernel Q β E =
      (Gibbs.measure base β E ⊗ₘ mhKernel Q β E).map Prod.swap := by
  letI : IsMarkovKernel (mhKernel Q β E) :=
    isMarkovKernel_mhKernel Q β E hE
  letI : IsFiniteKernel (acceptedKernel Q β E) :=
    Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top
      (acceptance_le_one β E)
  letI : IsFiniteKernel (rejectionKernel Q β E) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (Kernel.deterministic id measurable_id) ENNReal.one_ne_top fun x y => by
        exact tsub_le_self
  haveI : SFinite (Gibbs.measure base β E) := by
    unfold Gibbs.measure Measure.tilted
    infer_instance
  rw [mhKernel, Measure.compProd_add_right,
    Measure.map_add _ _ measurable_swap,
    ← accepted_detailedBalance base Q β E hE hEInt hsym,
    ← rejection_detailedBalance base Q β E hE hEInt]

end MetropolisHastings

namespace MetropolisExample

/-- Lebesgue measure is the Gibbs reference measure in the real example. -/
noncomputable def base : Measure ℝ :=
  volume

noncomputable instance instNeZeroBase : NeZero base := by
  unfold base
  infer_instance

noncomputable instance instSFiniteBase : SFinite base := by
  unfold base
  infer_instance

/-- A symmetric unit-variance Gaussian random-walk proposal. -/
noncomputable def proposal : ProbabilityTheory.Kernel ℝ ℝ :=
  (Kernel.const ℝ volume).withDensity
    (fun x y => ProbabilityTheory.gaussianPDF x 1 y)

/-- The proposal from `x` is the Gaussian law with mean `x`. -/
theorem proposal_apply (x : ℝ) :
    proposal x = ProbabilityTheory.gaussianReal x 1 := by
  rw [proposal, Kernel.withDensity_apply]
  · exact
      (ProbabilityTheory.gaussianReal_of_var_ne_zero x
        (by norm_num : (1 : NNReal) ≠ 0)).symm
  · fun_prop

noncomputable instance instIsMarkovKernelProposal :
    IsMarkovKernel proposal := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [proposal_apply]
  exact measure_univ

theorem gaussianPDF_symm (x y : ℝ) :
    ProbabilityTheory.gaussianPDF x 1 y =
      ProbabilityTheory.gaussianPDF y 1 x := by
  unfold ProbabilityTheory.gaussianPDF
    ProbabilityTheory.gaussianPDFReal
  have h : (y - x) ^ 2 = (x - y) ^ 2 := by ring
  rw [h]

/-- Lebesgue measure composed with the Gaussian random-walk proposal is
invariant under exchanging the current and proposed states. -/
theorem proposal_symmetry :
    base ⊗ₘ proposal = (base ⊗ₘ proposal).map Prod.swap := by
  have hpdf :
      Measurable
        (Function.uncurry
          (fun x y => ProbabilityTheory.gaussianPDF x 1 y)) := by
    fun_prop
  let density : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ProbabilityTheory.gaussianPDF p.1 1 p.2
  have hdensity : Measurable density := hpdf
  have hdensitySwap : density ∘ Prod.swap = density := by
    funext p
    exact gaussianPDF_symm p.2 p.1
  letI : IsMarkovKernel
      ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
        (fun x y => ProbabilityTheory.gaussianPDF x 1 y)) :=
    inferInstanceAs (IsMarkovKernel proposal)
  unfold base proposal
  rw [Measure.compProd_withDensity hpdf, Measure.compProd_const]
  calc
    (volume.prod volume).withDensity density =
        ((volume.prod volume).map Prod.swap).withDensity density := by
      rw [Measure.prod_swap]
    _ = ((volume.prod volume).withDensity
          (density ∘ Prod.swap)).map Prod.swap :=
      map_withDensity (volume.prod volume) Prod.swap density
        measurable_swap hdensity
    _ = ((volume.prod volume).withDensity density).map Prod.swap := by
      rw [hdensitySwap]

/-- A positive, time-dependent quadratic energy schedule. -/
def energy {n : ℕ} (c : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ → ℝ :=
  fun i x => c i * x ^ 2

/-- Every quadratic energy slice is measurable. -/
theorem measurable_energy
    {n : ℕ} (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Measurable (energy c i) := by
  unfold energy
  fun_prop

/-- Positive inverse temperature and curvature make every Boltzmann factor
Lebesgue-integrable. -/
theorem integrable_boltzmann_energy
    {n : ℕ} (β : ℝ) (hβ : 0 < β)
    (c : Fin (n + 1) → ℝ) (hc : ∀ i, 0 < c i)
    (i : Fin (n + 1)) :
    Integrable (fun x : ℝ => Real.exp (-β * energy c i x)) base := by
  unfold base energy
  have h : ∀ x : ℝ, -β * (c i * x ^ 2) = -(β * c i) * x ^ 2 :=
    fun x => by ring
  simpa only [h] using integrable_exp_neg_mul_sq (mul_pos hβ (hc i))

/-- The Metropolis kernel targeting one quadratic Gibbs equilibrium. -/
noncomputable def kernel
    {n : ℕ} (β : ℝ) (c : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ProbabilityTheory.Kernel ℝ ℝ :=
  MetropolisHastings.mhKernel proposal β (energy c i)

noncomputable instance instIsMarkovKernelKernel
    {n : ℕ} (β : ℝ) (c : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    IsMarkovKernel (kernel β c i) := by
  unfold kernel
  exact MetropolisHastings.isMarkovKernel_mhKernel proposal β
    (energy c i) (measurable_energy c i)

/-- Each post-quench quadratic Gibbs equilibrium satisfies local detailed
balance with its Metropolis transition. -/
theorem localBalance
    {n : ℕ} (β : ℝ) (hβ : 0 < β)
    (c : Fin (n + 1) → ℝ) (hc : ∀ i, 0 < c i)
    (i : Fin n) :
    Gibbs.measure base β (energy c i.succ) ⊗ₘ kernel β c i.succ =
      (Gibbs.measure base β (energy c i.succ) ⊗ₘ
        kernel β c i.succ).map Prod.swap := by
  exact MetropolisHastings.detailedBalance base proposal β
    (energy c i.succ) (measurable_energy c i.succ)
    (integrable_boltzmann_energy β hβ c hc i.succ) proposal_symmetry

/-- The physical multi-step Crooks relation for Gaussian random-walk
Metropolis transitions and quadratic energies. -/
theorem multiStep_crooks
    {n : ℕ} (β : ℝ) (hβ : 0 < β)
    (c : Fin (n + 1) → ℝ) (hc : ∀ i, 0 < c i) :
    CrooksRelation
      (Markov.chronologicalForwardPathMeasure
        (Gibbs.measure base β (energy c 0))
        (fun i : Fin n => kernel β c i.succ))
      (Markov.timeReversedReversePathMeasure
        (Gibbs.measure base β (energy c (Fin.last n)))
        (fun i : Fin n => kernel β c i.succ))
      (fun γ => ENNReal.ofReal
        (Real.exp (-β * Gibbs.pathWork (energy c) γ)))
      (ENNReal.ofReal
        (Real.exp (-β * Gibbs.deltaFreeEnergy base β (energy c)))) := by
  simpa using
    (Gibbs.multiStep_crooks_physical base β hβ.ne'
      (energy c)
      (fun i : Fin n => kernel β c i.succ)
      (fun i : Fin n => kernel β c i.succ)
      (measurable_energy c)
      (integrable_boltzmann_energy β hβ c hc)
      (localBalance β hβ c hc))

/-- The corresponding real-valued Jarzynski equality. -/
theorem multiStep_jarzynski
    {n : ℕ} (β : ℝ) (hβ : 0 < β)
    (c : Fin (n + 1) → ℝ) (hc : ∀ i, 0 < c i) :
    ∫ γ, Real.exp (-β * Gibbs.pathWork (energy c) γ)
        ∂Markov.chronologicalForwardPathMeasure
          (Gibbs.measure base β (energy c 0))
          (fun i : Fin n => kernel β c i.succ) =
      Real.exp (-β * Gibbs.deltaFreeEnergy base β (energy c)) := by
  simpa using
    (Gibbs.multiStep_jarzynski_integral base β hβ.ne'
      (energy c)
      (fun i : Fin n => kernel β c i.succ)
      (fun i : Fin n => kernel β c i.succ)
      (measurable_energy c)
      (integrable_boltzmann_energy β hβ c hc)
      (localBalance β hβ c hc))

end MetropolisExample

end MeasureProtocol
end CrooksJarzynski
