/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.ContinuousTimeJumpDrivenDensity

/-!
# Mixtures of fixed-initial jump sectors

A weighted sum over the fixed-initial sector laws is the sector law whose
initial endpoint density is that weight. This is the normalization bridge from
`pathLawFrom` mixtures to the equilibrium-weighted density laws used by the
Gibbs reversal theorem.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace FiniteJumpGenerator

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Summing the fixed-initial rate densities against a state weight recovers
that state weight as the initial endpoint density. -/
theorem tsum_weight_mul_fixedInitial_rateDensity
    (G : FiniteJumpGenerator Ω) (weight : Ω → ℝ≥0∞)
    {n : ℕ} (γ : JumpPath Ω n) :
    (∑' x : Ω,
      weight x *
        JumpPath.rateDensity (fixedInitialWeight x)
          G.pathEscapeRate G.pathJumpRate γ) =
      JumpPath.rateDensity weight
        G.pathEscapeRate G.pathJumpRate γ := by
  classical
  unfold JumpPath.rateDensity JumpPath.density fixedInitialWeight
  simp [mul_assoc]

/-- The weighted sum of fixed-initial sector measures is the common-reference
sector measure with the corresponding initial endpoint density. -/
theorem sum_smul_sectorLawFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ)
    (weight : Ω → ℝ≥0∞) :
    Measure.sum (fun x : Ω => weight x • G.sectorLawFrom T x n) =
      pathMeasure (G.rawCountingReference T n)
        (JumpPath.rateDensity weight
          G.pathEscapeRate G.pathJumpRate) := by
  unfold sectorLawFrom pathMeasure
  let densityFrom : Ω → JumpPath Ω n → ℝ≥0∞ :=
    fun x => JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate
  have hdensityFrom : ∀ x, Measurable (densityFrom x) := by
    intro x
    exact G.measurable_rateDensity (fixedInitialWeight x) n
  have hweighted : ∀ x,
      Measurable (weight x • densityFrom x) := by
    intro x
    change Measurable (fun γ => weight x * densityFrom x γ)
    exact measurable_const.mul (hdensityFrom x)
  calc
    Measure.sum (fun x : Ω =>
        weight x •
          (G.rawCountingReference T n).withDensity (densityFrom x)) =
      Measure.sum (fun x : Ω =>
        (G.rawCountingReference T n).withDensity
          (weight x • densityFrom x)) := by
        congr 1
        funext x
        exact (withDensity_smul (μ := G.rawCountingReference T n)
          (weight x) (hdensityFrom x)).symm
    _ = (G.rawCountingReference T n).withDensity
          (∑' x : Ω, weight x • densityFrom x) := by
        exact (withDensity_tsum hweighted).symm
    _ = (G.rawCountingReference T n).withDensity
          (JumpPath.rateDensity weight
            G.pathEscapeRate G.pathJumpRate) := by
        apply withDensity_congr_ae
        refine ae_of_all _ fun γ => ?_
        simpa [densityFrom, Pi.smul_apply, smul_eq_mul] using
          G.tsum_weight_mul_fixedInitial_rateDensity weight γ

/-- The weighted sum of the normalized fixed-initial full path laws is the
all-jump-count law obtained from the same initial endpoint density. -/
theorem sum_smul_pathLawFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal)
    (weight : Ω → ℝ≥0∞) :
    Measure.sum (fun x : Ω => weight x • G.pathLawFrom T x) =
      FullPath.measure (fun n =>
        pathMeasure (G.rawCountingReference T n)
          (JumpPath.rateDensity weight
            G.pathEscapeRate G.pathJumpRate)) := by
  ext s hs
  unfold pathLawFrom FullPath.measure
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.sum_apply _ hs]
  calc
    (∑' x : Ω, weight x *
        ∑' n : ℕ, FullPath.liftMeasure n (G.sectorLawFrom T x n) s) =
      ∑' x : Ω, ∑' n : ℕ,
        weight x * FullPath.liftMeasure n (G.sectorLawFrom T x n) s := by
          apply tsum_congr
          intro x
          exact (ENNReal.tsum_mul_left
            (α := ℕ) (a := weight x)
            (f := fun n =>
              FullPath.liftMeasure n (G.sectorLawFrom T x n) s)).symm
    _ = ∑' n : ℕ, ∑' x : Ω,
        weight x * FullPath.liftMeasure n (G.sectorLawFrom T x n) s :=
      ENNReal.tsum_comm
    _ = ∑' n : ℕ,
        FullPath.liftMeasure n
          (pathMeasure (G.rawCountingReference T n)
            (JumpPath.rateDensity weight
              G.pathEscapeRate G.pathJumpRate)) s := by
      apply tsum_congr
      intro n
      rw [← G.sum_smul_sectorLawFrom T n weight]
      simp_rw [FullPath.liftMeasure,
        Measure.map_apply (FullPath.measurable_mk n) hs]
      rw [Measure.sum_apply _ ((FullPath.measurable_mk n) hs)]
      simp only [Measure.smul_apply, smul_eq_mul]

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
