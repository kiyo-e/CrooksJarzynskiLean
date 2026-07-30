# Formalization map

This file maps the paper-level statements of the development to their Lean
declarations. All modules are exported by `CrooksJarzynski.lean`.

## Abstract measure theory

| Informal statement | Lean declaration |
| --- | --- |
| Crooks relation as a measure identity | `MeasureProtocol.CrooksRelation` |
| Crooks implies the nonnegative-integral Jarzynski equality | `MeasureProtocol.jarzynski_lintegral` |
| Real-integral Jarzynski equality | `MeasureProtocol.jarzynski_integral` |
| Crooks relation for a pushed-forward observable | `MeasureProtocol.CrooksRelation.map` |
| Density-free work-distribution relation | `MeasureProtocol.work_distribution_crooks` |

## Markov paths on arbitrary measurable state spaces

| Informal statement | Lean declaration |
| --- | --- |
| One-step Crooks theorem | `MeasureProtocol.Markov.oneStep_crooks` |
| Finite-horizon multi-step Crooks theorem | `MeasureProtocol.Markov.multiStep_crooks` |
| Multi-step Jarzynski equality | `MeasureProtocol.Markov.multiStep_jarzynski` |
| Chronological-path and path-reversal form | `MeasureProtocol.Markov.multiStep_crooks_chronological` |
| Ionescu–Tulcea path law | `MeasureProtocol.Markov.trajectoryMeasure` |
| Finite-prefix evolution law | `MeasureProtocol.Markov.trajectoryMeasure_step` |
| Finite-dimensional marginal identification | `MeasureProtocol.Markov.finiteMarginal_eq_chronologicalForwardPathMeasure` |

The multi-step theorem assumes a supplied forward kernel, reverse kernel,
equilibrium probability measure, equilibrium reweighting identity, and
measure-level local detailed-balance identity at each time. It does not assume
finite or countable state spaces or transition densities.

## Gibbs and physical forms

| Informal statement | Lean declaration |
| --- | --- |
| Gibbs reweighting by a quench | `MeasureProtocol.Gibbs.reweight_freeEnergy` |
| Physical `exp (-β W)` Crooks relation | `MeasureProtocol.Gibbs.multiStep_crooks_physical` |
| Physical real-integral Jarzynski equality | `MeasureProtocol.Gibbs.multiStep_jarzynski_integral` |
| Work-law Crooks relation with explicit `P_R(-W)` | `MeasureProtocol.Gibbs.multiStep_work_distribution_crooks` |
| Average-work second law `ΔF ≤ ⟨W⟩` | `MeasureProtocol.Gibbs.multiStep_second_law` |

The Gibbs construction uses Mathlib's exponentially tilted measures. Its
integrability and nonzero-measure hypotheses are explicit theorem inputs.

## Continuous-time finite-jump paths

| Informal statement | Lean declaration |
| --- | --- |
| Crooks from a common path-space density identity | `MeasureProtocol.ContinuousTimeJump.crooks_of_reversal_density` |
| Measurable involutive reversal of state/holding-time paths | `MeasureProtocol.ContinuousTimeJump.JumpPath.measurable_reverse` |
| Countable sum of all finite jump-count sectors | `MeasureProtocol.ContinuousTimeJump.FullPath.measure` |
| Sectorwise Crooks relations summed over all jump counts | `MeasureProtocol.ContinuousTimeJump.FullPath.crooks_of_sector_relations` |
| Measurable fixed-time horizon and reversal invariance | `MeasureProtocol.ContinuousTimeJump.JumpPath.map_horizonMeasure_reverse` |
| Full Crooks relation after horizon restriction | `MeasureProtocol.ContinuousTimeJump.FullPath.crooks_restrict_horizon_of_sector_relations` |
| Path-density identity from endpoint, holding, and jump factors | `MeasureProtocol.ContinuousTimeJump.JumpPath.density_mul_factorizedWorkWeight` |
| Segmentwise-rate Crooks theorem from local balance | `MeasureProtocol.ContinuousTimeJump.JumpPath.crooks_of_rate_local_balance` |
| Segmentwise-rate full-path Crooks theorem | `MeasureProtocol.ContinuousTimeJump.FullPath.crooks_of_rate_local_balance` |
| Fixed-horizon segmentwise-rate full-path Crooks theorem | `MeasureProtocol.ContinuousTimeJump.FullPath.crooks_restrict_horizon_of_rate_local_balance` |
| Fixed-horizon segmentwise-rate full-path Jarzynski equality | `MeasureProtocol.ContinuousTimeJump.FullPath.jarzynski_restrict_horizon_of_rate_local_balance` |
| Real-integral Jarzynski equality from a Crooks relation | `MeasureProtocol.jarzynski_toReal_integral` |
| Real-integral full-path Jarzynski for segmentwise rates | `MeasureProtocol.ContinuousTimeJump.FullPath.jarzynski_toReal_of_rate_local_balance` |

The generic continuous-time layer uses a common reversal-invariant reference
measure in each fixed-jump-count sector. Exponential survival factors are
instantiated for segmentwise constant escape rates. Equality of the forward and
aligned reverse escape rates cancels waiting-time factors, while endpoint
reweighting and local jump balance give the remaining path-density ratio.

## Fixed-horizon simplex construction

| Informal statement | Lean declaration |
| --- | --- |
| The free-coordinate simplex has product volume exactly `1 / n!` | `MeasureProtocol.ContinuousTimeJump.Simplex.volume_freeSimplexSet` |
| The free-coordinate simplex has positive product volume | `MeasureProtocol.ContinuousTimeJump.Simplex.volume_freeSimplexSet_pos` |
| The residual final holding interval makes the total duration exactly `T` | `MeasureProtocol.ContinuousTimeJump.Simplex.sum_holdingTimesOfFree` |
| The constructed path probability is supported on the horizon | `MeasureProtocol.ContinuousTimeJump.Simplex.rawPathProbability_ae_horizon` |
| Symmetrization gives reversal invariance | `MeasureProtocol.ContinuousTimeJump.Simplex.map_pathProbability_reverse` |
| A scaled simplex reference is reversal invariant | `MeasureProtocol.ContinuousTimeJump.Simplex.map_reference_reverse` |
| Positive scaling gives a nonzero reference | `MeasureProtocol.ContinuousTimeJump.Simplex.reference_ne_zero` |
| The scaled reference remains supported on the horizon | `MeasureProtocol.ContinuousTimeJump.Simplex.reference_ae_horizon` |

The horizon condition is built into the parametrization rather than imposed by
restricting an ambient Lebesgue measure to the zero-measure slice
`∑ᵢ τᵢ = T`. The first `n` holding times are free simplex coordinates and the
last holding time is the residual `T - ∑ᵢ<n τᵢ`.

## Concrete specializations

| Informal statement | Lean declaration |
| --- | --- |
| Non-atomic Gaussian-state Crooks theorem | `MeasureProtocol.GaussianExample.multiStep_crooks` |
| Non-atomic Gaussian-state Jarzynski equality | `MeasureProtocol.GaussianExample.multiStep_jarzynski` |
| Metropolis–Hastings detailed balance for a Gibbs measure | `MeasureProtocol.MetropolisHastings.detailedBalance` |
| Metropolis random-walk Crooks theorem on `ℝ` | `MeasureProtocol.MetropolisExample.multiStep_crooks` |
| Metropolis random-walk Jarzynski equality on `ℝ` | `MeasureProtocol.MetropolisExample.multiStep_jarzynski` |
| Two-state CTMC sector mass is the Poisson jump-count mass | `MeasureProtocol.ContinuousTimeJump.TwoState.sectorLaw_univ_eq_poisson` |
| The two-state sector masses sum to one | `MeasureProtocol.ContinuousTimeJump.TwoState.tsum_sectorLaw_univ` |
| The complete two-state finite-jump path law is a probability measure | `MeasureProtocol.ContinuousTimeJump.TwoState.instIsProbabilityMeasurePathLaw` |
| Forward and reverse two-state path laws coincide at equilibrium | `MeasureProtocol.ContinuousTimeJump.TwoState.reversePathLaw_eq_pathLaw` |
| Crooks relation for the normalized two-state CTMC | `MeasureProtocol.ContinuousTimeJump.TwoState.pathLaw_crooks` |
| Jarzynski equality for the normalized two-state CTMC | `MeasureProtocol.ContinuousTimeJump.TwoState.pathLaw_jarzynski` |
| The concrete generator has unit escape rate | `MeasureProtocol.ContinuousTimeJump.TwoState.generator_escape_eq_one` |
| Every row of the concrete generator sums to zero | `MeasureProtocol.ContinuousTimeJump.TwoState.generator_row_sum` |
| The jump-count marginal of the two-state path law is Poisson | `MeasureProtocol.ContinuousTimeJump.TwoState.map_pathLaw_jumpCount` |
| The Poisson-flip kernel of the jump count equals the entries of `exp (TQ)` | `MeasureProtocol.ContinuousTimeJump.TwoState.conditionalTerminalLaw_eq_exp_generator` |
| Asymmetric-chain sector masses sum to one for every initial state | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_sectorMass` |
| The raw simplex reference is reversal invariant | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.map_rawSectorReference_reverse` |
| The normalized asymmetric forward path law is a probability measure | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_forwardSectorLaw_univ` |
| The normalized asymmetric reverse path law is a probability measure | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_reverseSectorLaw_univ` |
| Nonequilibrium full-path Crooks relation with free-energy factor two | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_crooks` |
| Nonequilibrium full-path Jarzynski equality | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_lintegral` |
| Nonequilibrium real-integral Jarzynski equality | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_toReal` |
| The work observable is not a.e. constant under the forward law | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.fullWorkWeight_not_ae_const` |
| Original finite protocol satisfies measure Crooks | `Protocol.measure_crooks` |
| Original finite protocol satisfies real-integral Jarzynski | `Protocol.measure_jarzynski_integral` |
| General forward path singleton mass equals legacy `forwardWeight` | `Protocol.measure_forwardWeight_singleton` |
| General reverse path singleton mass equals legacy `reverseWeight` | `Protocol.measure_reverseWeight_singleton` |

For the symmetric unit-rate two-state chain, the `n`-jump simplex volume
`T^n / n!` is derived from the proved unit-simplex volume `1 / n!`, and the
survival factor is `exp (-T)`. Hence each sector has Poisson mass
`exp (-T) T^n / n!`; the sector sum is one. Because the sample space is the
disjoint union of finite-jump sectors, this supplies a concrete non-explosion
result together with normalized Crooks and Jarzynski theorems. The path
construction is identified with the conservative generator by matching the
Poisson-flip kernel of its jump count with the matrix exponential `exp (TQ)`;
the conditional terminal-state marginal given the path's own initial state is
not yet formalized.

The asymmetric example drives the chain with escape rates two and one, a Gibbs
initial density, a uniform final density, and a nonconstant work observable
whose free-energy factor is two. A telescoping evaluation of the weighted
simplex integrals proves that the sector masses of every initial state sum to
one, and the reversal invariance of the raw simplex reference upgrades both the
forward law and the dynamically constructed reverse law to probability
measures. The resulting full-path Crooks and Jarzynski equalities are therefore
normalized and genuinely nonequilibrium.

## Explicit scope boundaries

- The discrete-time theorem permits arbitrary measurable state spaces and has a
  finite horizon.
- The generic continuous-time theorem covers finite-jump paths, their countable
  sector sum, segmentwise constant rates, and a measurable fixed horizon.
- A nonzero reversal-invariant fixed-horizon simplex reference is constructed,
  rather than assumed.
- A normalized, non-explosive path law is constructed for the symmetric
  unit-rate two-state CTMC, and the Poisson-flip kernel of its jump count is
  identified with the matrix exponential of its conservative generator;
  conditioning the path law on its own initial state is not formalized.
- A normalized, non-explosive, genuinely nonequilibrium path law is
  constructed for the asymmetric two-state chain, with full-path Crooks and
  real-integral Jarzynski equalities.
- A generator-to-path-law construction and a non-explosion theorem for an
  arbitrary CTMC are not formalized in this PR.
- General calendar-time-dependent integrated escape rates and Langevin/SDE path
  laws are not formalized.
- Reverse discrete-time kernels and local balance are supplied; reverse-kernel
  existence by disintegration is not formalized.

`CrooksJarzynski/AxiomAudit.lean` lists the declarations whose kernel axioms are
checked in CI.
