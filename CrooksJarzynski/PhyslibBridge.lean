/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.MathlibBridge
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

/-!
# Bridge to Physlib finite canonical ensembles

This module identifies the finite equilibrium layer used by the
Crooks–Jarzynski development with Physlib's finite `CanonicalEnsemble` API.
The bridge proves equality of partition functions, Gibbs probabilities, and
Helmholtz free energies after converting inverse temperature to Physlib's
`Temperature` type.

Physlib's current `CanonicalEnsemble` carrier is defined in `Type`, so this
adapter specializes the universe-polymorphic core library to that universe.
-/

open MeasureTheory
open scoped BigOperators Temperature

namespace CrooksJarzynski

noncomputable section

namespace PhyslibBridge

variable {Ω : Type} [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Regard a finite energy landscape as a discrete Physlib canonical ensemble. -/
def toCanonicalEnsemble (E : Energy Ω) : CanonicalEnsemble Ω where
  energy := E
  dof := 0
  μ := Measure.count
  energy_measurable := measurable_of_finite _

instance (E : Energy Ω) :
    CanonicalEnsemble.IsFinite (toCanonicalEnsemble E) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

/-- Physlib's temperature corresponding to a nonnegative inverse temperature. -/
def temperatureOfBeta (β : ℝ) (hβ : 0 ≤ β) : Temperature :=
  Temperature.ofβ ⟨β, hβ⟩

@[simp]
theorem temperatureOfBeta_beta (β : ℝ) (hβ : 0 ≤ β) :
    ((temperatureOfBeta β hβ).β : ℝ) = β := by
  unfold temperatureOfBeta
  rw [Temperature.β_ofβ]
  rfl

/-- Physlib and the finite algebraic layer use the same partition function. -/
theorem partitionFunction_eq
    [Nonempty Ω] (β : ℝ) (hβ : 0 ≤ β) (E : Energy Ω) :
    (toCanonicalEnsemble E).partitionFunction (temperatureOfBeta β hβ) =
      CrooksJarzynski.partitionFunction β E := by
  rw [CanonicalEnsemble.partitionFunction_of_fintype]
  unfold CrooksJarzynski.partitionFunction CrooksJarzynski.boltzmannWeight
  simp only [toCanonicalEnsemble, temperatureOfBeta_beta]

/-- Physlib's point probability is the Gibbs probability used by this library. -/
theorem probability_eq_gibbsProbability
    [Nonempty Ω] (β : ℝ) (hβ : 0 ≤ β) (E : Energy Ω) (x : Ω) :
    (toCanonicalEnsemble E).probability (temperatureOfBeta β hβ) x =
      gibbsProbability β E x := by
  unfold CanonicalEnsemble.probability gibbsProbability
  rw [CanonicalEnsemble.mathematicalPartitionFunction_of_fintype]
  unfold CrooksJarzynski.partitionFunction CrooksJarzynski.boltzmannWeight
  simp only [toCanonicalEnsemble, temperatureOfBeta_beta]

/-- Physlib's Helmholtz free energy agrees with `-log Z / β` at positive β. -/
theorem helmholtzFreeEnergy_eq_freeEnergy
    [Nonempty Ω] (β : ℝ) (hβ : 0 < β) (E : Energy Ω) :
    (toCanonicalEnsemble E).helmholtzFreeEnergy
        (temperatureOfBeta β hβ.le) =
      CrooksJarzynski.freeEnergy β E := by
  rw [CanonicalEnsemble.helmholtzFreeEnergy_def,
    partitionFunction_eq β hβ.le E]
  unfold CrooksJarzynski.freeEnergy temperatureOfBeta
  change
    -Constants.kB * (1 / (Constants.kB * β)) *
        Real.log (CrooksJarzynski.partitionFunction β E) =
      -Real.log (CrooksJarzynski.partitionFunction β E) / β
  field_simp [Constants.kB_ne_zero, hβ.ne']

end PhyslibBridge

namespace Protocol

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable {n : ℕ}

/-- The Physlib canonical ensemble at protocol time `t`. -/
def physlibEnsembleAt (P : Protocol Ω n) (t : ℕ) : CanonicalEnsemble Ω :=
  PhyslibBridge.toCanonicalEnsemble (P.energy t)

/-- The single Physlib temperature associated with a protocol's inverse temperature. -/
def physlibTemperature (P : Protocol Ω n) : Temperature :=
  PhyslibBridge.temperatureOfBeta P.β P.β_pos.le

@[simp]
theorem physlibTemperature_beta (P : Protocol Ω n) :
    ((P.physlibTemperature).β : ℝ) = P.β := by
  exact PhyslibBridge.temperatureOfBeta_beta P.β P.β_pos.le

/-- Every protocol energy slice has the same partition function in Physlib. -/
theorem physlib_partitionFunction_at (P : Protocol Ω n) (t : ℕ) :
    (P.physlibEnsembleAt t).partitionFunction P.physlibTemperature =
      CrooksJarzynski.partitionFunction P.β (P.energy t) := by
  exact PhyslibBridge.partitionFunction_eq P.β P.β_pos.le (P.energy t)

/-- The protocol free-energy change is exactly the difference of Physlib Helmholtz energies. -/
theorem deltaFreeEnergy_eq_physlib (P : Protocol Ω n) :
    P.deltaFreeEnergy =
      (P.physlibEnsembleAt n).helmholtzFreeEnergy P.physlibTemperature -
        (P.physlibEnsembleAt 0).helmholtzFreeEnergy P.physlibTemperature := by
  unfold deltaFreeEnergy finalEnergy initialEnergy physlibEnsembleAt physlibTemperature
  rw [PhyslibBridge.helmholtzFreeEnergy_eq_freeEnergy P.β P.β_pos (P.energy n),
    PhyslibBridge.helmholtzFreeEnergy_eq_freeEnergy P.β P.β_pos (P.energy 0)]

end Protocol

end

end CrooksJarzynski
