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

The continuous-time layer uses a common reversal-invariant reference measure in
each fixed-jump-count sector. Exponential survival factors are instantiated for
segmentwise constant escape rates. Equality of the forward and aligned reverse
escape rates cancels waiting-time factors, while endpoint reweighting and local
jump balance give the remaining path-density ratio. Sector normalization and
the total probability mass across all jump counts are explicit hypotheses.

## Concrete specializations

| Informal statement | Lean declaration |
| --- | --- |
| Non-atomic Gaussian-state Crooks theorem | `MeasureProtocol.GaussianExample.multiStep_crooks` |
| Non-atomic Gaussian-state Jarzynski equality | `MeasureProtocol.GaussianExample.multiStep_jarzynski` |
| Metropolis–Hastings detailed balance for a Gibbs measure | `MeasureProtocol.MetropolisHastings.detailedBalance` |
| Metropolis random-walk Crooks theorem on `ℝ` | `MeasureProtocol.MetropolisExample.multiStep_crooks` |
| Metropolis random-walk Jarzynski equality on `ℝ` | `MeasureProtocol.MetropolisExample.multiStep_jarzynski` |
| Original finite protocol satisfies measure Crooks | `Protocol.measure_crooks` |
| Original finite protocol satisfies real-integral Jarzynski | `Protocol.measure_jarzynski_integral` |
| General forward path singleton mass equals legacy `forwardWeight` | `Protocol.measure_forwardWeight_singleton` |
| General reverse path singleton mass equals legacy `reverseWeight` | `Protocol.measure_reverseWeight_singleton` |

## Explicit scope boundaries

- The discrete-time theorem permits arbitrary measurable state spaces and has a
  finite horizon.
- The continuous-time theorem covers finite-jump paths and their countable
  sector sum, with segmentwise constant rates and a measurable fixed-horizon
  restriction.
- Continuous-time sector reference measures, normalization across jump counts,
  and non-explosion are supplied as hypotheses rather than constructed from a
  generator.
- General calendar-time-dependent integrated escape rates and Langevin/SDE
  path laws are not yet formalized.
- Reverse discrete-time kernels and local balance are supplied; reverse-kernel
  existence by disintegration is not formalized.

`CrooksJarzynski/AxiomAudit.lean` lists the declarations whose kernel axioms are
checked in CI.
