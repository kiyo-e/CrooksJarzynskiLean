# Crooks–Jarzynski in Lean 4

A machine-checked development of stochastic thermodynamics in Lean 4. The
library contains:

- a complete finite-state, discrete-time Crooks–Jarzynski theory;
- a measure-theoretic discrete-time theory on arbitrary measurable state
  spaces;
- a finite-jump continuous-time path-space theory with fixed-horizon Crooks and
  Jarzynski statements for segmentwise jump rates; and
- a path-uniform refinement limit for the two standard discrete work
  conventions.

The development contains no `sorry` placeholders and introduces no custom
axioms.

## Main results

The library proves:

- Crooks' relation as a measure identity on an arbitrary measurable trajectory
  space and its nonnegative-integral and real-integral Jarzynski consequences;
- one-step and finite-horizon multi-step Crooks theorems on arbitrary measurable
  state spaces from equilibrium reweighting and measure-level local detailed
  balance;
- measurable chronological paths, explicit path reversal, and an
  Ionescu–Tulcea trajectory measure whose finite-dimensional marginals agree
  with the recursive finite-horizon path laws;
- Gibbs specializations with the physical factors `exp (-β W)` and
  `exp (-β ΔF)`, a density-free work-distribution theorem, and the average-work
  second law `ΔF ≤ ⟨W⟩`;
- non-atomic Gaussian examples and a Metropolis–Hastings specialization on
  `ℝ` with Gaussian random-walk proposals and quadratic energies;
- fixed-jump-count continuous-time paths represented by state sequences and
  holding-time sequences, with measurable involutive reversal;
- a dependent-sum path space containing every finite jump count, together with
  the countable sum of the sector measures;
- a measurable fixed-time horizon condition that is invariant under reversal;
- factorized continuous-time path densities built from endpoint weights,
  survival factors, and jump-rate factors;
- a path-density Crooks identity derived from endpoint reweighting, cancellation
  of aligned waiting-time factors, and local jump balance;
- fixed-sector, all-sector, and fixed-horizon Crooks and Jarzynski theorems for
  segmentwise constant escape and jump rates;
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

through `MeasureProtocol.jarzynski_lintegral`. The real-valued physical form is
provided by `MeasureProtocol.jarzynski_integral`.

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
the holding intervals, including the terminal no-jump interval. Reversal acts on
both finite sequences and is proved measurable and involutive.

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
discrete externally driven work conventions and is not an
Itô–Stratonovich conversion theorem.

## Scope

The discrete-time development permits arbitrary measurable state spaces and an
arbitrary finite horizon. Forward and reverse kernels and their local-balance
identity are supplied; reverse-kernel existence by disintegration is not
formalized.

The continuous-time development covers finite-jump trajectories, the countable
sum over all finite jump counts, and a measurable fixed-horizon restriction. It
provides path-density Crooks and Jarzynski theorems for segmentwise constant
escape and jump rates. The sector reference measures, normalization across all
jump counts, and non-explosion are explicit hypotheses rather than being
constructed from an infinitesimal generator. General calendar-time-dependent
integrated hazards and Langevin/SDE path laws are not yet formalized.

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
