# Crooks–Jarzynski in Lean 4

A machine-checked development of stochastic thermodynamics in Lean 4. The
library contains:

- a complete finite-state, discrete-time Crooks–Jarzynski theory;
- a measure-theoretic discrete-time theory on arbitrary measurable state
  spaces;
- a finite-jump continuous-time path-space theory with fixed-horizon Crooks and
  Jarzynski statements for segmentwise jump rates;
- a fixed-horizon simplex reference with derived volume `1 / n!`;
- a normalized, non-explosive two-state continuous-time Markov chain whose
  fixed-initial terminal laws form a Markov kernel with entries `exp (TQ)`;
- a normalized asymmetric reversible two-state chain followed by an explicit
  energy quench, with real work, free-energy difference, physical Crooks and
  Jarzynski relations, work-distribution Crooks, the second law, and an entropy
  production fluctuation theorem; and
- a path-uniform refinement limit for the two standard discrete work
  conventions.

The development contains no `sorry` placeholders and introduces no custom
axioms.

## Main results

The library proves:

- Crooks' relation as a measure identity on an arbitrary measurable trajectory
  space and its nonnegative-integral and real-integral Jarzynski consequences;
- a density-free Crooks relation for every measurable pushforward observable;
- an average-work second law `ΔF ≤ ⟨W⟩` derived from any normalized physical
  measure-level Crooks relation by Jensen's inequality;
- one-step and finite-horizon multi-step Crooks theorems on arbitrary measurable
  state spaces from equilibrium reweighting and measure-level local detailed
  balance;
- measurable chronological paths, explicit path reversal, and an
  Ionescu–Tulcea trajectory measure whose finite-dimensional marginals agree
  with the recursive finite-horizon path laws;
- Gibbs specializations with the physical factors `exp (-β W)` and
  `exp (-β ΔF)`, a density-free work-distribution theorem, and the average-work
  second law;
- non-atomic Gaussian examples and a Metropolis–Hastings specialization on
  `ℝ` with Gaussian random-walk proposals and quadratic energies;
- fixed-jump-count continuous-time paths represented by state sequences and
  holding-time sequences, with measurable involutive reversal;
- a dependent-sum path space containing every finite jump count, together with
  the countable sum of the sector measures;
- a measurable fixed-time horizon condition that is invariant under reversal;
- a simplex parametrization with derived volume `1 / n!` that builds the
  horizon condition into the holding-time law and yields a nonzero
  reversal-invariant reference;
- factorized continuous-time path densities built from endpoint weights,
  survival factors, and jump-rate factors;
- a path-density Crooks identity derived from endpoint reweighting, cancellation
  of aligned waiting-time factors, and local jump balance;
- fixed-sector, all-sector, and fixed-horizon Crooks and Jarzynski theorems for
  segmentwise constant escape and jump rates;
- a symmetric unit-rate two-state CTMC whose `n`-jump sector has Poisson mass,
  whose complete finite-jump path law is normalized and non-explosive, and
  which satisfies full-path Crooks and Jarzynski theorems;
- normalized fixed-initial versions of that path law whose actual terminal-state
  pushforwards form a Mathlib Markov kernel, equal the rows of `exp (TQ)`, and
  satisfy Chapman--Kolmogorov;
- an asymmetric two-state generator with rates `q(0,1)=2` and `q(1,0)=1`, whose
  Gibbs distribution is explicitly normalized, reversible, and stationary;
- a normalized final-quench experiment with partition functions `Z₀=3` and
  `Z₁=6`, free-energy difference `ΔF=-log 2`, and a genuinely nonconstant real
  work observable;
- physical full-path Crooks and Jarzynski relations for this quench, a
  density-free Crooks relation for its work laws, the average-work second law,
  and the integral fluctuation theorem for entropy production;
- the original finite-state pathwise Crooks ratio, Jarzynski equality, integral
  fluctuation theorem, explicit reverse protocol, and work-distribution Crooks
  theorem; and
- an exact summation-by-parts comparison and a path-uniform `O(1/N)` refinement
  bound for the quench-then-transition and transition-then-quench work
  conventions.

## Abstract measure formulation

For an arbitrary measurable trajectory space `Γ`, Crooks' relation is expressed
without division as

```lean
forward.withDensity workWeight = freeEnergyWeight • reverse
```

by `CrooksJarzynski.MeasureProtocol.CrooksRelation`. If `reverse` is a
probability measure, evaluating this identity on the whole path space gives

```lean
∫⁻ γ, workWeight γ ∂forward = freeEnergyWeight
```

through `MeasureProtocol.jarzynski_lintegral`. The physical real-valued form

```text
∫ exp (-β W) dP_F = exp (-β ΔF)
```

is provided by `MeasureProtocol.jarzynski_integral`. For normalized forward and
reverse laws, positive `β`, and integrable real work,
`MeasureProtocol.second_law_of_crooks` derives

```text
ΔF ≤ ∫ W dP_F
```

directly from the same measure identity.

This formulation avoids ratios on zero-probability trajectories and lets the
same measure algebra serve discrete-time kernels, continuous-time jump-path
densities, and future path-measure constructions.

## Discrete time on arbitrary measurable state spaces

For one Markov step, `MeasureProtocol.Markov.oneStep_crooks` assumes the
equilibrium reweighting identity

```lean
initial.withDensity workWeight = freeEnergyWeight • final
```

and local detailed balance as an equality of measures on `Ω × Ω`:

```lean
final ⊗ₘ forward = (final ⊗ₘ reverse).map Prod.swap
```

The theorem derives the corresponding Crooks relation for the forward one-step
path measure. `MeasureProtocol.Markov.multiStep_crooks` iterates these
hypotheses over an arbitrary finite protocol, and
`multiStep_crooks_chronological` transports the result to chronological paths
with explicit measurable reversal.

`MeasureProtocol.Gibbs` constructs equilibrium measures by exponential tilting
of a base measure and proves the physical total-work and endpoint-free-energy
forms. `MeasureProtocol.GaussianExample` exercises a genuinely non-atomic state
space, while `MeasureProtocol.MetropolisHastings` and
`MeasureProtocol.MetropolisExample` construct state-dependent transition
kernels and prove their measure-level detailed balance.

For a time-inhomogeneous family of Mathlib kernels,
`MeasureProtocol.Markov.trajectoryMeasure` constructs the law on `ℕ → Ω`.
`finiteMarginal_eq_chronologicalForwardPathMeasure` identifies every finite
dimensional marginal with the finite-horizon path measure used by the Crooks
theorem.

## Continuous-time jump paths

For exactly `n` jumps, the path type is

```lean
JumpPath Ω n =
  (Fin (n + 1) → Ω) × (Fin (n + 1) → NNReal)
```

The first component stores the occupied states, and the second component stores
the holding intervals, including the terminal no-jump interval. Reversal acts
on both finite sequences and is proved measurable and involutive.

All finite jump counts are assembled into

```lean
FullPath Ω = Σ n : ℕ, JumpPath Ω n
```

and `ContinuousTimeJump.FullPath.measure` sums the lifted sector measures.
`FullPath.crooks_of_sector_relations` proves that sectorwise Crooks relations
with a common free-energy factor sum to a Crooks relation on the complete
finite-jump path space.

The elapsed-time observable is the sum of all holding intervals. The set

```text
{γ | totalHoldingTime γ = T}
```

is measurable and invariant under reversal. Crooks relations can therefore be
restricted to a common physical horizon and then summed over all jump counts.

### Nonzero fixed-horizon simplex reference

Restricting an ambient product Lebesgue measure to the equality slice
`∑ᵢ τᵢ = T` would normally produce the zero measure. The module
`ContinuousTimeJumpSimplex` instead starts from `n` free unit-interval
coordinates satisfying

```text
∑ᵢ<n uᵢ ≤ 1,
```

conditions the finite product Lebesgue measure on this positive-volume simplex,
and defines

```text
τᵢ = T uᵢ              for i < n,
τₙ = T - ∑ᵢ<n τᵢ.
```

Consequently, the total holding time is exactly `T` by construction. Averaging
the resulting path probability with its time reversal produces a probability
measure that is reversal invariant. Scaling it by any positive finite mass
gives a genuinely nonzero fixed-horizon reference. The principal declarations
are:

```lean
MeasureProtocol.ContinuousTimeJump.Simplex.volume_freeSimplexSet
MeasureProtocol.ContinuousTimeJump.Simplex.volume_freeSimplexSet_pos
MeasureProtocol.ContinuousTimeJump.Simplex.sum_holdingTimesOfFree
MeasureProtocol.ContinuousTimeJump.Simplex.rawPathProbability_ae_horizon
MeasureProtocol.ContinuousTimeJump.Simplex.map_reference_reverse
MeasureProtocol.ContinuousTimeJump.Simplex.reference_ne_zero
MeasureProtocol.ContinuousTimeJump.Simplex.reference_ae_horizon
```

### Rate-level density identity

For segmentwise constant escape rates `λᵢ(x)` and jump rates `kᵢ(x,y)`, the
forward density has the factorized form

```text
initialWeight(x₀)
  · ∏ᵢ [exp (-λᵢ(xᵢ) τᵢ) · kᵢ(xᵢ,xᵢ₊₁)]
  · exp (-λₙ(xₙ) τₙ).
```

The local-balance theorem assumes:

```text
initialWeight(x₀) · boundaryWork(x₀,xₙ)
  = freeEnergyWeight · finalWeight(xₙ),

forwardEscapeᵢ(x) = alignedReverseEscapeᵢ(x),

forwardJumpᵢ(x,y) · jumpWorkᵢ(x,y)
  = alignedReverseJumpᵢ(y,x).
```

The equality of aligned escape rates cancels every waiting-time survival
factor. The endpoint and jump identities then multiply into the full pathwise
Radon–Nikodym identity. The principal declarations are:

```lean
MeasureProtocol.ContinuousTimeJump.JumpPath.crooks_of_rate_local_balance
MeasureProtocol.ContinuousTimeJump.JumpPath.jarzynski_of_rate_local_balance
MeasureProtocol.ContinuousTimeJump.FullPath.crooks_of_rate_local_balance
MeasureProtocol.ContinuousTimeJump.FullPath.jarzynski_of_rate_local_balance
MeasureProtocol.ContinuousTimeJump.FullPath.crooks_restrict_horizon_of_rate_local_balance
MeasureProtocol.ContinuousTimeJump.FullPath.jarzynski_restrict_horizon_of_rate_local_balance
```

### Normalized symmetric two-state CTMC

`ContinuousTimeJumpTwoStateNormalization` instantiates the construction for the
symmetric chain on two states with generator

```text
Q(x,y) = 1    when y is the other state,
Q(x,x) = -1.
```

The state flips at every jump, the escape rate is one, and the work observable
is identically one. The fixed-horizon `n`-jump reference has simplex mass
`T^n / n!`, derived from the proved unit-simplex volume `1 / n!`.
Multiplication by the survival factor `exp (-T)` gives exactly the Poisson
jump-count mass

```text
exp (-T) T^n / n!.
```

These masses sum to one, so the measure on
`Σ n, JumpPath State n` is a probability measure. In this concrete model, this
is the non-explosion result: every finite horizon is exhausted by finite-jump
sectors. The forward and reverse laws coincide at equilibrium.

The connection to the generator is made at the level of actual normalized path
laws. For each fixed initial state `x`, `pathLawFrom T x` records `x` in its
initial coordinate almost surely, has Poisson jump count, and its terminal-state
pushforward is the corresponding row of `exp (TQ)`. These terminal laws are
packaged as a Mathlib Markov kernel and satisfy Chapman--Kolmogorov:

```lean
MeasureProtocol.ContinuousTimeJump.TwoState.tsum_sectorLawFrom_univ
MeasureProtocol.ContinuousTimeJump.TwoState.map_pathLawFrom_jumpCount
MeasureProtocol.ContinuousTimeJump.TwoState.map_pathLawFrom_terminalState
MeasureProtocol.ContinuousTimeJump.TwoState.pathLawFrom_terminalState_eq_exp_generator
MeasureProtocol.ContinuousTimeJump.TwoState.transitionKernel_real_singleton_eq_exp_generator
MeasureProtocol.ContinuousTimeJump.TwoState.transitionKernel_chapman_kolmogorov
```

### Asymmetric reversible chain and final quench

The asymmetric example uses the conservative two-state generator

```text
q(0,1) = 2,    q(1,0) = 1,
q(0,0) = -2,   q(1,1) = -1.
```

Its equilibrium probabilities are `(1/3, 2/3)`. The development proves their
normalization, detailed balance, and stationarity. The initial and final energy
landscapes at `β=1` are

```text
E₀(0) = 0,        E₀(1) = -log 2,
E₁(0) = -log 3,   E₁(1) = -log 3.
```

Thus `Z₀=3`, `Z₁=6`, and `ΔF=-log 2`, so `exp (-β ΔF)=2`. The initial Gibbs
density relative to the uniform state reference is `(2/3,4/3)`, and the final
density is one.

Normalization is proved directly from the continuous-time path construction.
For each initial state, integrating out the last free simplex coordinate makes
consecutive arrival integrals differ by one sector integral. The partial sums
telescope, and the `(2T)^n/n!` bound makes the remainder vanish. An affine
involution of the free simplex proves that the raw reference is reversal
invariant. Therefore, both the forward law and the dynamically constructed
reverse law are probability measures; the reverse law is not defined as a
formal tilt of the forward law.

The factorized endpoint and jump work weights telescope pointwise to a terminal
potential. This potential is exactly the Boltzmann factor of the real-valued
final-quench work

```text
W(γ) = E₁(x_T) - E₀(x_T).
```

The work values `-log 3` and `log (2/3)` both have positive probability under
the normalized forward law; equivalently, the exponential weights `3` and
`3/2` both have positive probability. The observable is therefore not almost
everywhere constant on the physical support.

The resulting statements include:

```lean
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physicalGenerator_row_sum
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physical_detailedBalance
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.equilibriumProbability_stationary
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.initial_partitionFunction
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.final_partitionFunction
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physicalDeltaFreeEnergy_eq
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.fullWorkWeight_not_ae_const
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.fullWorkWeight_eq_exp_thermodynamicWork
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_crooks_physical
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_physical
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_physical_eq_two
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_work_distribution_crooks
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_second_law
MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_entropyProduction_integral_fluctuation
```

## Discrete work conventions and refinement

The finite-state protocol formalizes both quench-then-transition and
transition-then-quench work. Their exact trajectory-wise difference is reduced
by discrete summation by parts to temporal increments evaluated at the same
state. Under uniform bounds

```text
|qᵢ(x)| ≤ M h,
|qᵢ(x) - qᵢ₊₁(x)| ≤ L h²,
```

`WorkConvention.discrepancy_uniform_grid_abs_le` proves

```text
|D_N| ≤ 2 M h + (N - 1) L h²
      ≤ (2 M T + L T²) / N.
```

The resulting convergence is uniform over paths. This refinement result is
separate from the continuous-time jump-process construction; it compares two
discrete externally driven work conventions and is not an Itô–Stratonovich
conversion theorem.

## Scope

The discrete-time development permits arbitrary measurable state spaces and an
arbitrary finite horizon. Forward and reverse kernels and their local-balance
identity are supplied; reverse-kernel existence by disintegration is not
formalized.

The generic continuous-time development covers finite-jump trajectories, the
countable sum over all finite jump counts, a measurable fixed horizon, and
path-density Crooks and Jarzynski theorems for segmentwise constant escape and
jump rates. The library constructs a nonzero reversal-invariant simplex
reference on the fixed horizon with derived volume `1 / n!`.

For the symmetric unit-rate two-state CTMC, the library constructs normalized
full and fixed-initial path laws, proves their Poisson jump-count law and
non-explosion, identifies the actual fixed-initial terminal-state marginal with
`exp (TQ)`, and packages those terminal laws as a Markov kernel satisfying
Chapman--Kolmogorov.

For the asymmetric two-state model, the library connects the normalized path
construction to a conservative reversible generator and an explicit energy
quench. It derives Gibbs equilibrium, partition functions, free-energy
difference, real work, physical Crooks and Jarzynski relations,
work-distribution Crooks, the average-work second law, and the entropy-production
integral fluctuation theorem.

A generator-to-path-law construction and a general non-explosion theorem for an
arbitrary CTMC remain outside this PR. General calendar-time-dependent
integrated hazards and Langevin/SDE path laws are not formalized.

## Build

```bash
lake exe cache get
lake build
```

The project is pinned to Lean and Mathlib `v4.32.0`. GitHub Actions also checks
for proof placeholders and custom axioms and prints the kernel axioms of the
headline theorems.

## Theorem map

See [`FORMALIZATION.md`](FORMALIZATION.md) for a paper-level-to-Lean declaration
map covering the abstract, discrete-time, Gibbs, concrete-example, and
continuous-time jump-process layers.

## References

The formalized results build on the fluctuation-theorem literature, including:

- C. Jarzynski, *Nonequilibrium equality for free energy differences*, Phys.
  Rev. Lett. **78**, 2690 (1997).
- G. E. Crooks, *Nonequilibrium measurements of free energy differences for
  microscopically reversible Markovian systems*, J. Stat. Phys. **90**, 1481
  (1998).
- G. E. Crooks, *Entropy production fluctuation theorem and the nonequilibrium
  work relation for free energy differences*, Phys. Rev. E **60**, 2721 (1999).
- G. E. Crooks, *Path-ensemble averages in systems driven far from
  equilibrium*, Phys. Rev. E **61**, 2361 (2000).
- L. Peliti and S. Pigolotti, *Stochastic Thermodynamics: An Introduction*,
  Princeton University Press (2021).

## License

Released under the Apache License 2.0. See [`LICENSE`](LICENSE) and
[`CITATION.cff`](CITATION.cff).
