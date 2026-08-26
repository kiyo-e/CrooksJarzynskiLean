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
import CrooksJarzynski.MeasureProtocolMarked
import CrooksJarzynski.MeasureProtocolMarkedCrooks
import CrooksJarzynski.MeasureProtocolMarkedMultiStep
import CrooksJarzynski.MeasureProtocolMarkedPhysical
import CrooksJarzynski.MeasureProtocolMarkedEndpoints
import CrooksJarzynski.MeasureProtocolMarginals
import CrooksJarzynski.MeasureProtocolPhysical
import CrooksJarzynski.MeasureProtocolSecondLaw
import CrooksJarzynski.MeasureProtocolGaussianExample
import CrooksJarzynski.MeasureProtocolMetropolisExample
import CrooksJarzynski.ContinuousTimeJumpRateFull
import CrooksJarzynski.ContinuousTimeJumpSimplexReversal
import CrooksJarzynski.ContinuousTimeJumpFiniteGenerator
import CrooksJarzynski.ContinuousTimeJumpTwoStateNormalization
import CrooksJarzynski.ContinuousTimeJumpTwoStateFiniteGenerator
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetric
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricNormalization
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricJarzynski
import CrooksJarzynski.ContinuousTimeJumpTwoStateGenerator
import CrooksJarzynski.ContinuousTimeJumpTwoStateFixedInitial
import CrooksJarzynski.ContinuousTimeJumpTwoStateThermodynamics
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricFixedInitial
import CrooksJarzynski.ContinuousTimeJumpTwoStateAsymmetricParity
import CrooksJarzynski.ContinuousTimeJumpTwoStatePhysicalWork
import CrooksJarzynski.ContinuousTimeJumpTwoStateSemigroup
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorPathLaw
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorFullPath
import CrooksJarzynski.ContinuousTimeJumpTrajectory
import CrooksJarzynski.ContinuousTimeJumpConcat
import CrooksJarzynski.ContinuousTimeJumpConcatLaw
import CrooksJarzynski.ContinuousTimeJumpConcatPathLaw
import CrooksJarzynski.ContinuousTimeJumpConcatPathLawBridge
import CrooksJarzynski.ContinuousTimeJumpFiniteDimensional
import CrooksJarzynski.ContinuousTimeJumpFullPathReversal
import CrooksJarzynski.ContinuousTimeJumpDriven
import CrooksJarzynski.ContinuousTimeJumpDrivenBalance
import CrooksJarzynski.ContinuousTimeJumpDrivenDensity
import CrooksJarzynski.ContinuousTimeJumpDrivenMixture
import CrooksJarzynski.ContinuousTimeJumpDrivenStationary
import CrooksJarzynski.ContinuousTimeJumpDrivenBoundary
import CrooksJarzynski.ContinuousTimeJumpDrivenConnectedPath
import CrooksJarzynski.ContinuousTimeJumpDrivenConcat
import CrooksJarzynski.ContinuousTimeJumpDrivenGlobalLaw
import CrooksJarzynski.ContinuousTimeJumpDrivenWorkSum
import CrooksJarzynski.ContinuousTimeJumpDrivenWindowBalance
import CrooksJarzynski.ContinuousTimeJumpDrivenPhysical
import CrooksJarzynski.ContinuousTimeJumpDrivenWorkDistribution
import CrooksJarzynski.ContinuousTimeJumpDrivenEndpointLaw
import CrooksJarzynski.ContinuousTimeJumpDrivenEndpointExp
import CrooksJarzynski.ContinuousTimeJumpDrivenThreeStateTwoWindow
import CrooksJarzynski.ContinuousTimeJumpDrivenTwoState
import CrooksJarzynski.ContinuousTimeJumpDrivenTwoStateComparison
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorRenewal
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorExp
import CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorBridge
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
free-energy forms, a second law derived directly from an arbitrary physical
measure-level Crooks relation, a non-atomic Gaussian example on `ℝ`, an
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
full-path, and fixed-horizon Crooks and Jarzynski statements. A general
`FiniteJumpGenerator` packages nonnegative finite-state jump rates, derives a
conservative real generator, and supplies a fixed-horizon counting reference;
a three-state Y-shaped chain demonstrates genuine branching. Its fixed-initial
sector laws are proved non-explosive and assembled into a probability measure
on the disjoint union of all jump-count sectors, whose actual terminal
coordinate pushes forward to the transition mass. On the real side the
exponential of the generator is shown to satisfy the entrywise first-jump
renewal equation and to be its unique bounded continuous solution.

The two halves are matched in a residual fraction of a fixed horizon, so no
rescaling of the simplex chart is ever needed. Peeling the first holding
coordinate turns an `(n+1)`-jump sector into the `n`-jump sector of the shifted
state sequence on the remaining fraction; folding the branching sum over the
state reached by that jump, and then summing over the jump count, produces a
genuine renewal equation for the transition mass. Its solution is bounded by
the normalization already proved at full horizon, and continuity comes out of
the renewal equation itself rather than being assumed. Since scaling every jump
rate scales the generator, the fraction form is the real-time form of a
rescaled chain, which feeds the uniqueness hook directly and identifies the
terminal marginal of the general fixed-initial path law with the rows of
`exp (TQ)`. The terminal marginals are packaged as a Mathlib Markov kernel and
shown to satisfy Chapman--Kolmogorov and the semigroup law under kernel
composition, and the identification is specialized to the branching three-state
Y chain, which no parity argument reaches, and to the normalized two-state
chain.

A finite-window driven protocol binds one complete normalized fixed-initial
jump path at every switching endpoint. The reverse experiment traverses the
windows in reverse order and stores reversed complete paths. Boundary matching
is available both almost surely for the constructed laws and structurally in
`Driven.ConnectedPath`. The recursive work is identified with its ordinary
finite sum over window endpoints, is uniformly bounded on finite state spaces,
and is therefore automatically integrable. Division-free instantaneous Gibbs
detailed balance is lifted to the complete-path `WindowBalance`, yielding
Crooks, Jarzynski, and the average-work second law without an external
work-integrability hypothesis. The asymmetric reversible two-state final
quench is also recovered as an explicit one-window specialization. Its generic
and legacy fixed-initial constructions have identical terminal-state
pushforward measures because both are the same row of `exp (TQ)`.

A normalized unit-rate two-state CTMC identifies every jump-count sector with
its Poisson probability and proves non-explosion by constructing a probability
law on the disjoint union of all finite-jump sectors. Its normalized
fixed-initial path laws record their prescribed initial state, and the
pushforward of their actual terminal coordinate is packaged as a Mathlib Markov
kernel. The kernel entries are the rows of `exp (TQ)` for the conservative
generator and satisfy Chapman--Kolmogorov. Its concrete matrix is also proved
to be the generator derived from the general `FiniteJumpGenerator` structure.

A separate asymmetric reversible two-state chain is followed by a final energy
quench. Its state-dependent holding-time simplex integrals normalize both the
forward law and the dynamically constructed reverse law without
uniformization. The conservative generator, reversible Gibbs distribution,
detailed balance, stationarity, energy landscapes, partition functions,
free-energy difference, and real-valued quench work are explicit. The
factorized path weight telescopes pointwise to `exp (-β W)`, yielding normalized
physical Crooks and Jarzynski relations, a density-free work-distribution
relation, the average-work second law, and an integral fluctuation theorem for
entropy production. Restricting the measure-level Crooks relation to
terminal-state events determines the exact two-atom work distribution, the
exact mean work, a strict second law, and the conventional atomwise Crooks
ratio with the sign-reversed reverse work observable. The simplex-reversal
change of variables underlying all path-reversal arguments is exposed as a
reusable API on the free simplex chart. Normalized fixed-initial path laws are
also constructed for the asymmetric chain. A renewal expansion evaluates
their parity-filtered sector-mass sums, proving that their actual terminal
marginals are the rows of the explicit asymmetric transition matrix and hence
of `exp (TQ)`. The explicit matrix has eigenvalues `0` and `-3` and satisfies
Chapman--Kolmogorov.

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
`MeasureProtocol.second_law_of_crooks`,
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
`MeasureProtocol.ContinuousTimeJump.Simplex.lintegral_freeSimplex_reverseFree`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.generator_row_sum`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.map_countingReference_reverse`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionMassAt_renewal`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.eq_exp_smul_apply_of_renewal_fraction`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_terminalState_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel_chapman_kolmogorov`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel_add`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.ThreeStateBranching.pathLawFrom_terminalState_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.TwoState.finiteGenerator_pathLawFrom_terminalState_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.ThreeStateBranching.has_two_distinct_successors`,
`MeasureProtocol.ContinuousTimeJump.TwoState.finiteGenerator_generator_eq`,
`MeasureProtocol.ContinuousTimeJump.Driven.work_eq_sum`,
`MeasureProtocol.ContinuousTimeJump.Driven.integrable_work`,
`MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.windowBalance_of_gibbsDetailedBalance`,
`MeasureProtocol.ContinuousTimeJump.Driven.crooks_of_gibbsDetailedBalance`,
`MeasureProtocol.ContinuousTimeJump.Driven.jarzynski_of_gibbsDetailedBalance`,
`MeasureProtocol.ContinuousTimeJump.Driven.second_law_of_gibbsDetailedBalance`,
`MeasureProtocol.ContinuousTimeJump.Driven.reverseWork_eq_neg`,
`MeasureProtocol.ContinuousTimeJump.Driven.work_distribution_crooks_of_gibbsDetailedBalance`,
`MeasureProtocol.ContinuousTimeJump.Driven.crooks_work_atom_of_gibbsDetailedBalance`,
`MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.crooks`,
`MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.jarzynski_eq_one`,
`MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_not_constant`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.driven_oneWindow_crooks_physical`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.driven_oneWindow_jarzynski_physical`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.driven_oneWindow_second_law`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.map_physicalFiniteGenerator_pathLawFrom_terminalState_eq_legacy`,
`MeasureProtocol.ContinuousTimeJump.TwoState.pathLawFrom_terminalState_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.TwoState.transitionKernel_real_singleton_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.TwoState.transitionKernel_chapman_kolmogorov`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_sectorMass_parity`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.asymmetricPathLawFrom_terminalState_eq_exp_generator`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physical_detailedBalance`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_crooks_physical`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_physical_eq_two`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_work_distribution_crooks`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_second_law`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.forward_work_atom_low`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_average_work`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_second_law_strict`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.crooks_work_atom`,
`MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_entropyProduction_integral_fluctuation`,
`MeasureProtocol.ContinuousTimeJump.TwoState.pathLaw_crooks`,
`MeasureProtocol.ContinuousTimeJump.TwoState.pathLaw_jarzynski`,
`MeasureProtocol.ContinuousTimeJump.TwoState.sectorLaw_univ_eq_poisson`,
`Protocol.work_distribution_crooks`,
`WorkConvention.discrepancy_uniform_tendsto_zero`, and `Protocol.second_law`.
-/
