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
import CrooksJarzynski.MeasureProtocolSecondLaw
import CrooksJarzynski.MeasureProtocolGaussianExample
import CrooksJarzynski.MeasureProtocolMetropolisExample
import CrooksJarzynski.ContinuousTimeJumpRateFull
import CrooksJarzynski.ContinuousTimeJumpTwoStateNormalization
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetric
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricNormalization
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricJarzynski
import CrooksJarzynski.ContinuousTimeJumpTwoStateGenerator
import CrooksJarzynski.ContinuousTimeJumpTwoStateFixedInitial
import CrooksJarzynski.ContinuousTimeJumpTwoStateThermodynamics
import CrooksJarzynski.ContinuousTimeJumpTwoStatePhysicalWork
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
finite jump-count sectors into one dependent-sum path law, constructs a
nonzero fixed-horizon simplex reference instead of restricting an ambient
Lebesgue law to a null slice, instantiates exponential survival and jump
factors, derives the path-density identity from endpoint reweighting,
waiting-time cancellation, and local jump balance, and proves fixed-sector,
full-path and fixed-horizon Crooks and Jarzynski statements.  A normalized
unit-rate two-state CTMC example identifies every jump-count sector with its
Poisson probability and proves non-explosion by constructing a probability law
on the disjoint union of all finite-jump sectors.  Its fixed-initial-state
time-`T` marginal is identified with the matrix exponential of the conservative
generator, and a separate asymmetric-rate example has nonconstant work and a
non-unit free-energy factor.  The asymmetric example is normalized directly
from its state-dependent holding-time simplex integrals and satisfies full-path
Crooks and Jarzynski equalities without uniformization.

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
`MeasureProtocol.ContinuousTimeJump.Simplex.map_reference_reverse`,
`MeasureProtocol.ContinuousTimeJump.Simplex.volume_freeSimplexSet`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.sector_crooks`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_crooks`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_lintegral`,
`MeasureProtocol.ContinuousTimeJump.TwoState.pathLawFrom_terminalState_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.TwoState.transitionProbability_chapman_kolmogorov`,
`MeasureProtocol.ContinuousTimeJump.TwoState.pathLaw_crooks`,
`MeasureProtocol.ContinuousTimeJump.TwoState.pathLaw_jarzynski`,
`MeasureProtocol.ContinuousTimeJump.TwoState.sectorLaw_univ_eq_poisson`,
`Protocol.work_distribution_crooks`,
`WorkConvention.discrepancy_uniform_tendsto_zero`, and `Protocol.second_law`.
-/
