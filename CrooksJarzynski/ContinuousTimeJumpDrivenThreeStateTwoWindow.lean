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
one resting.  (This is a statement about the work observable on the carrier,
not about nondegeneracy of the pushforward work distribution — for zero window
durations the constructed laws never leave the initial state.)  The example
also pins the `Fin.castSucc` orientation of the window-indexed balance
hypothesis on a case where the two windows differ.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

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

/-! ### The work observable is nonconstant on boundary-consistent paths -/

/-- The zero-jump window path resting at a prescribed state. -/
def restMark (x : Fin 3) : FullPath (Fin 3) :=
  ⟨0, (fun _ => x, fun _ => 0)⟩

/-- The one-jump window path hopping from `x` to `y`. -/
def hopMark (x y : Fin 3) : FullPath (Fin 3) :=
  ⟨1, (![x, y], fun _ => 0)⟩

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
and back `1 → 0` in the second. -/
def hopPath : ConnectedPath (Fin 3) 2 :=
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

end ThreeStateTwoWindow
end Driven
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
