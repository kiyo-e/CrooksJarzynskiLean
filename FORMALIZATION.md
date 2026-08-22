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
| Average-work second law from a physical measure-level Crooks relation | `MeasureProtocol.second_law_of_crooks` |

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
| Simplex reversal preserves every free-simplex Lebesgue integral | `MeasureProtocol.ContinuousTimeJump.Simplex.lintegral_freeSimplex_reverseFree` |
| Reversing the free coordinates reverses the completed holding times | `MeasureProtocol.ContinuousTimeJump.Simplex.holdingTimesOfFree_reverseFree` |

The horizon condition is built into the parametrization rather than imposed by
restricting an ambient Lebesgue measure to the zero-measure slice
`∑ᵢ τᵢ = T`. The first `n` holding times are free simplex coordinates and the
last holding time is the residual `T - ∑ᵢ<n τᵢ`.

All volume statements refer to this free-coordinate convention: the `n`
free holding-time coordinates carry the `n`-dimensional Lebesgue product
measure, under which the free simplex has volume exactly `1 / n!`. This is a
chart convention, not the intrinsic geometry of the embedded slice
`∑ᵢ τᵢ = T` in `ℝ^{n+1}`, whose `n`-dimensional Hausdorff measure carries an
additional constant factor `√(n+1)`. The factor is common to the forward and
reverse references, so it cancels from every normalized path law and every
Crooks ratio; no statement in this development depends on the intrinsic
normalization.

Time reversal of a fixed-horizon holding-time vector acts on the free
coordinates as an affine involution: a shear exchanging the first coordinate
with the residual coordinate, followed by a coordinate permutation. The
change-of-variables lemmas above expose this as a reusable public API in
`ContinuousTimeJumpSimplexReversal.lean`.

## Stepwise driven finite-state protocols

| Informal statement | Lean declaration |
| --- | --- |
| Complete-path reversal on the all-jump-count path space | `MeasureProtocol.ContinuousTimeJump.FullPath.reverse` |
| Pointwise concatenation of finite-jump charts, with the seam holding intervals merged | `MeasureProtocol.ContinuousTimeJump.JumpPath.concat` |
| Real-time left/right gluing laws for concatenated charts | `MeasureProtocol.ContinuousTimeJump.JumpPath.trajectory_concat_left`, `MeasureProtocol.ContinuousTimeJump.JumpPath.trajectory_concat_right` |
| Validity of concatenated charts over the summed horizon | `MeasureProtocol.ContinuousTimeJump.JumpPath.isValid_concat` |
| Complete-path concatenation and measurability in the suffix | `MeasureProtocol.ContinuousTimeJump.FullPath.concat`, `MeasureProtocol.ContinuousTimeJump.FullPath.measurable_concat` |
| One forward window built from the actual fixed-initial path law | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.forwardWindowKernel` |
| Forward-aligned reverse window | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.reverseWindowKernel` |
| Forward law obtained by recursively binding window endpoints | `MeasureProtocol.ContinuousTimeJump.Driven.forwardDrivenLaw` |
| Reverse-order driven law starting from the final Gibbs state | `MeasureProtocol.ContinuousTimeJump.Driven.reverseDrivenLaw` |
| Almost-sure forward-window boundary matching | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.forwardWindowKernel_ae_boundary` |
| Almost-sure reverse-window boundary matching | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.reverseWindowKernel_ae_boundary` |
| All-window physical support of the forward/reverse laws | `MeasureProtocol.ContinuousTimeJump.Driven.forwardDrivenLaw_ae_isProtocolValid`, `MeasureProtocol.ContinuousTimeJump.Driven.reverseDrivenLaw_ae_isProtocolValid` |
| Chronological concatenation of every complete window mark | `MeasureProtocol.ContinuousTimeJump.Driven.concatenateWindows` |
| Total holding time and summed-duration validity of the concatenated window chart | `MeasureProtocol.ContinuousTimeJump.Driven.totalHoldingTime_concatenateWindows`, `MeasureProtocol.ContinuousTimeJump.Driven.isValid_concatenateWindows` |
| Division-free finite-generator detailed balance | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.IsDetailedBalanceWeight` |
| Instantaneous Gibbs detailed balance | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.IsGibbsDetailedBalance` |
| Gibbs-weighted jump products telescope under reversal | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.gibbsWeight_mul_jumpProduct_eq_reverse` |
| Weighted mixture of actual fixed-initial full path laws | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.sum_smul_pathLawFrom` |
| Reversal invariance of the weighted full path law | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.map_weightedFullPathLaw_reverse` |
| Path-level window balance from instantaneous Gibbs detailed balance | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.windowBalance_of_gibbsDetailedBalance` |
| Endpoint-switch work `Σₖ(Eₖ₊₁-Eₖ)(xₖ,end)` | `MeasureProtocol.ContinuousTimeJump.Driven.work` |
| Explicit finite-state partition function | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.finitePartitionFunction` |
| Explicit finite-state free energy | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.finiteFreeEnergy` |
| Crooks relation on the constructed driven path laws | `MeasureProtocol.ContinuousTimeJump.Driven.crooks_of_gibbsDetailedBalance` |
| Jarzynski equality on the constructed forward driven law | `MeasureProtocol.ContinuousTimeJump.Driven.jarzynski_of_gibbsDetailedBalance` |
| Average-work second law for the constructed driven law | `MeasureProtocol.ContinuousTimeJump.Driven.second_law_of_gibbsDetailedBalance` |
| One-window work is the terminal energy quench | `MeasureProtocol.ContinuousTimeJump.Driven.work_one` |
| Reverse work observable is the negated forward work | `MeasureProtocol.ContinuousTimeJump.Driven.reverseWork_eq_neg` |
| Work-distribution Crooks relation for driven protocols | `MeasureProtocol.ContinuousTimeJump.Driven.work_distribution_crooks_of_gibbsDetailedBalance` |
| Measure-level work-distribution Crooks theorem using intrinsic reverse work | `MeasureProtocol.ContinuousTimeJump.Driven.work_distribution_crooks_reverseWork_of_gibbsDetailedBalance` |
| Conventional atomwise ratio `P_F(W=w) = e^{β(w-ΔF)} P_R(W_R=-w)` | `MeasureProtocol.ContinuousTimeJump.Driven.crooks_work_atom_of_gibbsDetailedBalance` |
| Two-window three-state protocol with positive-probability `0` and `log 2` work atoms for positive windows | `MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_zero_atom_pos`, `MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_log_two_atom_pos` |
| Erasing marks commutes with the marked path construction, yielding the endpoint-marginal Markov law | `MeasureProtocol.Marked.map_reversedForwardPathMeasure_eraseMarks` |
| Endpoint marginal of one forward window kernel is the finite generator's transition kernel | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.endpointMarginal_forwardWindowKernel` |
| Erasing all marks from the forward driven law gives the endpoint Markov chain of the window transition kernels | `MeasureProtocol.ContinuousTimeJump.Driven.map_forwardDrivenLaw_endpoints` |
| Singleton endpoint cylinders of the driven law are initial-atom times matrix-exponential products | `MeasureProtocol.ContinuousTimeJump.Driven.forwardDrivenLaw_endpointCylinder_eq_exp_product` |
| Positive-measure events with equal endpoints `(0, 0)` realizing work `0` and `log 2` | `MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_zero_same_endpoints_event_pos`, `MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_log_two_same_endpoints_event_pos` |
| The realized work is not almost surely a function of the endpoint pair, nor of the final state | `MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_not_ae_initialFinalFunction`, `MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_not_ae_finalStateFunction` |

The path carrier stores one complete `FullPath` mark per window. The recursive
kernel construction passes each recorded terminal state to the next window, and
the all-window support theorems record both boundary continuity and valid
fixed-horizon real-time charts almost surely. The
headline Crooks and Jarzynski statements are about these constructed measures,
not about an intermediate sector sum. The reverse-oriented carrier is read by
`windowAt` in chronological order, and `concatenateWindows` glues those marks
into one pointwise global real-time chart. No measure-level law for that global
chart is asserted.

## Concrete specializations

| Informal statement | Lean declaration |
| --- | --- |
| Non-atomic Gaussian-state Crooks theorem | `MeasureProtocol.GaussianExample.multiStep_crooks` |
| Non-atomic Gaussian-state Jarzynski equality | `MeasureProtocol.GaussianExample.multiStep_jarzynski` |
| Metropolis–Hastings detailed balance for a Gibbs measure | `MeasureProtocol.MetropolisHastings.detailedBalance` |
| Metropolis random-walk Crooks theorem on `ℝ` | `MeasureProtocol.MetropolisExample.multiStep_crooks` |
| Metropolis random-walk Jarzynski equality | `MeasureProtocol.MetropolisExample.multiStep_jarzynski` |
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
| The fixed-initial path law is normalized with Poisson jump counts | `MeasureProtocol.ContinuousTimeJump.TwoState.tsum_sectorLawFrom_univ` |
| The terminal-state marginal of the fixed-initial path law | `MeasureProtocol.ContinuousTimeJump.TwoState.map_pathLawFrom_terminalState` |
| The fixed-initial terminal marginal equals the entries of `exp (TQ)` | `MeasureProtocol.ContinuousTimeJump.TwoState.pathLawFrom_terminalState_eq_exp_generator` |
| Chapman--Kolmogorov for the explicit transition probabilities | `MeasureProtocol.ContinuousTimeJump.TwoState.transitionProbability_chapman_kolmogorov` |
| The terminal laws form a Markov transition kernel with `exp (TQ)` entries | `MeasureProtocol.ContinuousTimeJump.TwoState.transitionKernel_real_singleton_eq_exp_generator` |
| Chapman--Kolmogorov for the packaged transition kernel | `MeasureProtocol.ContinuousTimeJump.TwoState.transitionKernel_chapman_kolmogorov` |
| Asymmetric-chain sector masses sum to one for every initial state | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_sectorMass` |
| The raw simplex reference is reversal invariant | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.map_rawSectorReference_reverse` |
| The normalized asymmetric forward path law is a probability measure | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_forwardSectorLaw_univ` |
| The normalized asymmetric reverse path law is a probability measure | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_reverseSectorLaw_univ` |
| Nonequilibrium full-path Crooks relation with free-energy factor two | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_crooks` |
| Nonequilibrium full-path Jarzynski equality | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_lintegral` |
| Nonequilibrium real-integral Jarzynski equality | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_toReal` |
| The work observable is not a.e. constant under the forward law | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.fullWorkWeight_not_ae_const` |
| The asymmetric generator is conservative | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physicalGenerator_row_sum` |
| The asymmetric rates satisfy detailed balance for an explicit Gibbs state | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physical_detailedBalance` |
| The Gibbs distribution is stationary for the asymmetric generator | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.equilibriumProbability_stationary` |
| The initial and final partition functions are `3` and `6` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.initial_partitionFunction`, `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.final_partitionFunction` |
| The physical free-energy difference is `-log 2` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.physicalDeltaFreeEnergy_eq` |
| The Crooks factor two is `exp (-β ΔF)` for explicit energies | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.freeEnergyWeight_eq_exp_delta` |
| The path-work weight is `exp (-β W)` for the final-quench work | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.fullWorkWeight_eq_exp_thermodynamicWork` |
| Physical Crooks relation with `exp (-β W)` and `exp (-β ΔF)` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_crooks_physical` |
| Physical Jarzynski equality for the real work observable | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_physical` |
| Physical Jarzynski average evaluates to the explicit factor two | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_jarzynski_physical_eq_two` |
| Density-free Crooks relation for the work distributions | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_work_distribution_crooks` |
| Average-work second law for the asymmetric chain | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_second_law` |
| Integral fluctuation theorem for the entropy production | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_entropyProduction_integral_fluctuation` |
| The forward terminal distribution is `(1/3, 2/3)` at every horizon | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.forwardPathLaw_terminalEvent_zero`, `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.forwardPathLaw_terminalEvent_one` |
| The reverse terminal distribution is uniform at every horizon | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.reversePathLaw_terminalEvent` |
| Exact work atoms `P(W = -log 3) = 1/3`, `P(W = log (2/3)) = 2/3` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.forward_work_atom_low`, `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.forward_work_atom_high` |
| Exact mean work `(2/3) log 2 - log 3` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_average_work` |
| Strict second law `ΔF < ⟨W⟩`, reducing to `27 < 32` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.full_second_law_strict` |
| Reverse work sign convention `W_rev = -W` on reversed paths | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.reverseThermodynamicWork_eq_neg` |
| Conventional atomwise Crooks ratio `P_F(W=w) = e^{β(w-ΔF)} P_R(W_rev=-w)` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.crooks_work_atom` |
| Poisson-type tail bound for an arbitrary rate cap `R` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.arrivalIntegral_le` |
| The fixed-initial asymmetric path law is a probability measure | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_asymmetricSectorLawFrom_univ` |
| Its terminal marginal is a parity-filtered sector-mass sum | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.map_asymmetricPathLawFrom_terminalState_apply` |
| Chapman--Kolmogorov for the explicit asymmetric transition matrix | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.asymmetricTransitionProbability_chapman_kolmogorov` |
| The explicit asymmetric matrix is `exp (t Q)` for the physical generator | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.exp_smul_physicalGenerator_fun_apply` |
| Renewal evaluation of the parity-filtered sector-mass sums | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.tsum_sectorMass_parity` |
| The fixed-initial asymmetric terminal marginal is the explicit matrix row | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.asymmetricPathLawFrom_terminalState_real_singleton` |
| The fixed-initial asymmetric terminal marginal equals `exp (TQ)` | `MeasureProtocol.ContinuousTimeJump.TwoState.AsymmetricExample.asymmetricPathLawFrom_terminalState_eq_exp_generator` |
| The finite-generator counting reference carries the physical mass `T^n / n!` | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.simplexSectorMass_eq` |
| The general fixed-initial path law is a probability measure (non-explosion) | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.tsum_sectorMassFrom`, `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.instIsProbabilityMeasurePathLawFrom` |
| Entrywise first-jump renewal equation for `exp (TQ)` | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.exp_smul_apply_renewal` |
| Continuous solutions of the renewal equation are unique | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.eq_exp_smul_apply_of_renewal` |
| The general terminal marginal equals the row of `exp (TQ)` | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_terminalState_eq_exp_generator` |
| The general terminal marginals form a Markov kernel | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel`, `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.instIsMarkovKernelTransitionKernel` |
| Chapman--Kolmogorov for the general transition kernel | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel_chapman_kolmogorov` |
| The identification specialized to the branching three-state Y chain | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.ThreeStateBranching.pathLawFrom_terminalState_eq_exp_generator` |
| Almost every path is a valid real-time trajectory (positive waits, horizon) | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_ae_isValid` |
| The real-time trajectory starts at the prescribed state and ends at the recorded terminal state | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_ae_trajectory_endpoints` |
| Path-level Chapman--Kolmogorov for the fixed-initial path law | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_add` |
| Path-level Chapman--Kolmogorov in kernel form | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathKernel_add` |
| The transition-kernel semigroup law recovered from path-level concatenation | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel_add_from_pathLawFrom_add` |
| Every finite-dimensional marginal is the chronological path measure of the transition kernels | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_finiteDimensional_eq` |
| Every single-time marginal is the corresponding transition-kernel row | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.map_pathLawFrom_trajectory_eq_transitionKernel` |
| Every finite-dimensional atom is a product of matrix-exponential entries | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_sampleAt_real_singleton_eq_exp_product` |
| Every single-time atom is the corresponding matrix-exponential entry | `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_trajectory_real_singleton_eq_exp_generator` |
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
Poisson-flip kernel of its jump count with the matrix exponential `exp (TQ)`.
The normalized fixed-initial terminal laws are additionally packaged as a
Mathlib Markov kernel whose entries are `exp (TQ)` and which satisfies
Chapman--Kolmogorov.

The asymmetric example starts from the reversible Gibbs equilibrium selected
by the conservative rates `q(0,1)=2` and `q(1,0)=1`, and then applies a final
energy quench. A telescoping evaluation of weighted simplex integrals proves
that the sector masses of every initial state sum to one, and reversal
invariance of the raw simplex reference upgrades both the forward law and the
dynamically constructed reverse law to probability measures. The factorized
path weight telescopes pointwise to the Boltzmann factor of the real quench
work. The free-energy factor is derived from partition functions `Z₀=3` and
`Z₁=6`, so the resulting normalized Crooks theorem has the physical form
`e^{-βW}` versus `e^{-βΔF}` and implies the real-valued Jarzynski equality,
the work-distribution Crooks relation, the average-work second law, and the
entropy-production integral fluctuation theorem.

Restricting the measure-level Crooks relation to the two terminal-state
events makes the work weight constant on each event, so the four terminal
masses of the forward and reverse laws satisfy an explicitly solvable linear
system. This determines, at every horizon and without computing any
transition probability, the exact terminal distributions `(1/3, 2/3)` and
`(1/2, 1/2)`, the exact two-atom work distribution, the exact mean work
`(2/3) log 2 - log 3`, and hence a strict second law whose final inequality
is `log 27 < log 32`. The conventional Crooks ratio
`P_F(W = w) = e^{β(w-ΔF)} P_R(W_rev = -w)` is stated with the reverse
experiment's own work observable, whose sign reversal on chronologically
reversed paths is itself a theorem.

## Explicit scope boundaries

- The discrete-time theorem permits arbitrary measurable state spaces and has a
  finite horizon.
- The generic continuous-time theorem covers segment-indexed factorized
  finite-jump laws: finite-jump paths, their countable sector sum,
  piecewise-constant rate factors on jump sectors, and a measurable fixed
  horizon. The escape and jump rates carry a `Fin` sector index and the
  survival factor of a segment is `exp (-λᵢ(x) τᵢ)` in that segment's own
  holding time; no construction here depends on absolute calendar time.
- A nonzero reversal-invariant fixed-horizon simplex reference is constructed,
  rather than assumed.
- A normalized fixed-initial path law and a non-explosion theorem are proved for
  every `FiniteJumpGenerator` on a finite state space.
- The stepwise driving layer covers a fixed finite family of piecewise-constant
  finite-state windows, with one complete path mark per window. Boundary
  matching is proved almost surely, and the reverse-oriented marks can be read
  chronologically and concatenated into a single pointwise global real-time
  trajectory. A measure-level law for the concatenated chart is not asserted.
- A normalized, non-explosive path law is constructed for the symmetric
  unit-rate two-state CTMC. Its normalized fixed-initial terminal laws form a
  Markov kernel with matrix-exponential entries and Chapman--Kolmogorov.
- A normalized, non-explosive physical quench model is constructed from an
  asymmetric reversible two-state generator, with explicit Gibbs equilibrium,
  energies, partition functions, free-energy difference, real work, physical
  Crooks and Jarzynski relations, work-distribution Crooks, the average-work
  second law, and the entropy-production integral fluctuation theorem.
- General calendar-time-dependent integrated escape rates and Langevin/SDE path
  laws are not formalized.
- Reverse discrete-time kernels and local balance are supplied; reverse-kernel
  existence by disintegration is not formalized. In `multiStep_crooks`,
  `multiStep_crooks_chronological` and `multiStep_crooks_physical` the reverse
  kernel is an input of the theorem, constrained only by the local-balance
  hypothesis. A forward kernel that is reversible for the corresponding
  equilibrium measure satisfies that hypothesis with itself as the reverse
  kernel.

`CrooksJarzynski/AxiomAudit.lean` lists the declarations whose kernel axioms are
checked in CI.
