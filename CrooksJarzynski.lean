/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Probability
import CrooksJarzynski.Equilibrium
import CrooksJarzynski.Protocol
import CrooksJarzynski.TimeReversal
import CrooksJarzynski.WorkConventionLimit
import CrooksJarzynski.MeasureProtocol
import CrooksJarzynski.MeasureProtocolFiniteCrooks
import CrooksJarzynski.MeasureProtocolGibbs
import CrooksJarzynski.MeasureProtocolPaths
import CrooksJarzynski.MeasureProtocolMarginals
import CrooksJarzynski.MeasureProtocolPhysical
import CrooksJarzynski.MeasureProtocolGaussianExample
import CrooksJarzynski.MeasureProtocolMetropolisExample
import CrooksJarzynski.ContinuousTimeJumpRateFull
import CrooksJarzynski.MathlibBridge
import CrooksJarzynski.MeasureProtocolFiniteBridge
import CrooksJarzynski.PhyslibBridge
import CrooksJarzynski.Examples

/-!
# Crooks–Jarzynski theory

This root module exports the finite-state, discrete-time development together
with a measure-theoretic development on arbitrary measurable state spaces. The
measure-theoretic layer includes one-step and finite-horizon Crooks relations,
the corresponding Lebesgue and real-integral Jarzynski equalities, a Gibbs
specialization constructed from Mathlib's exponentially tilted measures,
measurable chronological path reversal, physical total-work and endpoint
free-energy forms, a non-atomic Gaussian example on `ℝ`, an
explicit Lebesgue-based Metropolis--Hastings example on `ℝ`, an
Ionescu–Tulcea trajectory-measure adapter for time-inhomogeneous Mathlib Markov
kernels, an identification of all of its finite-dimensional marginals with the
finite-horizon path measures, and a bridge proving that the original finite
protocol satisfies the new measure-level hypotheses and that the new path
measures recover its legacy singleton weights.

The continuous-time jump layer represents an `n`-jump path by its state and
holding-time sequences, proves measurable involutive reversal, and constructs
path laws from densities against reversal-invariant references. It sums all
finite jump-count sectors into one dependent-sum path law, restricts sectors to
a measurable fixed-time horizon, instantiates exponential survival and jump
factors for segmentwise constant rates, derives the path-density identity from
endpoint reweighting, waiting-time cancellation, and local jump balance, and
proves fixed-sector, full-path, fixed-horizon Crooks and Jarzynski statements.

The finite-state results include explicit time reversal, both standard
discrete-time work conventions, a path-uniform `O(1/N)` continuous-time limit
for their discrepancy, work-distribution fluctuation relations, bridges to
Mathlib's measure-theoretic Markov-kernel API, and Physlib's finite
canonical-ensemble API. The main results include `Protocol.crooks`,
`Protocol.jarzynski`, `Protocol.measure_crooks`,
`Protocol.measure_jarzynski_integral`,
`Protocol.measure_forwardWeight_singleton`,
`Protocol.measure_reverseWeight_singleton`,
`MeasureProtocol.Markov.multiStep_crooks`,
`MeasureProtocol.Markov.multiStep_crooks_chronological`,
`MeasureProtocol.Gibbs.multiStep_crooks_physical`,
`MeasureProtocol.Gibbs.multiStep_jarzynski_integral`,
`MeasureProtocol.Gibbs.multiStep_second_law`,
`MeasureProtocol.Gibbs.multiStep_work_distribution_crooks`,
`MeasureProtocol.GaussianExample.multiStep_crooks`,
`MeasureProtocol.GaussianExample.multiStep_jarzynski`,
`MeasureProtocol.MetropolisExample.multiStep_crooks`,
`MeasureProtocol.MetropolisExample.multiStep_jarzynski`,
`MeasureProtocol.Markov.trajectoryMeasure`,
`MeasureProtocol.Markov.finiteMarginal_eq_chronologicalForwardPathMeasure`,
`MeasureProtocol.ContinuousTimeJump.crooks_of_reversal_density`,
`MeasureProtocol.ContinuousTimeJump.JumpPath.crooks_of_rate_local_balance`,
`MeasureProtocol.ContinuousTimeJump.FullPath.crooks_of_sector_relations`,
`MeasureProtocol.ContinuousTimeJump.FullPath.crooks_of_rate_local_balance`,
`MeasureProtocol.ContinuousTimeJump.FullPath.crooks_restrict_horizon_of_rate_local_balance`,
`Protocol.work_distribution_crooks`,
`WorkConvention.discrepancy_uniform_tendsto_zero`, and `Protocol.second_law`.
-/
