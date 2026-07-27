import CrooksJarzynski.Protocol

/-!
# Concrete finite-state examples
-/

namespace CrooksJarzynski

universe u

/-- A deterministic distribution concentrated at one state. -/
def FiniteDistribution.dirac {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (x₀ : Ω) : FiniteDistribution Ω where
  prob := fun x => if x = x₀ then 1 else 0
  nonneg := by
    intro x
    split <;> positivity
  sum_prob := by simp

/-- The identity Markov kernel. -/
def identityKernel {Ω : Type u} [Fintype Ω] [DecidableEq Ω] : Kernel Ω :=
  fun x => FiniteDistribution.dirac x

@[simp]
theorem identityKernel_apply_self {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (x : Ω) : identityKernel x x = 1 := by
  simp [identityKernel, FiniteDistribution.dirac]

/-- A one-step quench with no state change. It is a useful sanity check: work
is the pointwise energy change, and Crooks and Jarzynski follow from the general
theory. -/
noncomputable def deterministicQuenchProtocol
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (β : ℝ) (hβ : 0 < β) (E₀ E₁ : Energy Ω) : Protocol Ω 1 where
  β := β
  β_pos := hβ
  energy := fun t => if t = 0 then E₀ else E₁
  forwardKernel := fun _ => identityKernel
  reverseKernel := fun _ => identityKernel
  localBalance := by
    intro t x y
    fin_cases t
    simp only [zero_add, identityKernel, FiniteDistribution.dirac]
    by_cases hxy : x = y
    · subst y
      simp
    · simp [hxy, Ne.symm hxy]

/-- A concrete two-state energy landscape with levels `0` and `ε`. -/
def twoStateEnergy (ε : ℝ) : Energy (Fin 2)
  | 0 => 0
  | 1 => ε

/-- Partition function of the two-state landscape. -/
theorem twoState_partitionFunction (β ε : ℝ) :
    partitionFunction β (twoStateEnergy ε) = 1 + Real.exp (-β * ε) := by
  unfold partitionFunction boltzmannWeight
  simp [Fin.sum_univ_two, twoStateEnergy]

end CrooksJarzynski
