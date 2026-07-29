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

The Gibbs construction uses Mathlib's exponentially tilted measures. Its
integrability and nonzero-measure hypotheses are explicit theorem inputs.

## Concrete specializations

| Informal statement | Lean declaration |
| --- | --- |
| Non-atomic Gaussian-state Crooks theorem | `MeasureProtocol.GaussianExample.multiStep_crooks` |
| Non-atomic Gaussian-state Jarzynski equality | `MeasureProtocol.GaussianExample.multiStep_jarzynski` |
| Original finite protocol satisfies measure Crooks | `Protocol.measure_crooks` |
| Original finite protocol satisfies real-integral Jarzynski | `Protocol.measure_jarzynski_integral` |
| General forward path singleton mass equals legacy `forwardWeight` | `Protocol.measure_forwardWeight_singleton` |
| General reverse path singleton mass equals legacy `reverseWeight` | `Protocol.measure_reverseWeight_singleton` |

## Explicit scope boundaries

- Time is discrete and the main theorem has a finite horizon.
- Reverse kernels and local balance are supplied; reverse-kernel existence by
  disintegration is not formalized.
- No continuous-time Crooks theorem is claimed.

`CrooksJarzynski/AxiomAudit.lean` lists the declarations whose kernel axioms are
checked in CI.
