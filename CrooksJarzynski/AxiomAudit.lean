/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski

/-!
# Axiom audit

This module prints the kernel axioms used by the headline results. The CI log
therefore records whether a proof placeholder or any custom axiom has entered
the trusted base of the development.
-/

#print axioms CrooksJarzynski.Trajectory.reverse_reverse
#print axioms CrooksJarzynski.Protocol.boltzmann_crooks
#print axioms CrooksJarzynski.Protocol.crooks_partition_ratio
#print axioms CrooksJarzynski.Protocol.crooks
#print axioms CrooksJarzynski.Protocol.jarzynski
#print axioms CrooksJarzynski.Protocol.integral_fluctuation_theorem
#print axioms CrooksJarzynski.Protocol.second_law
#print axioms CrooksJarzynski.Protocol.workConvention_difference
#print axioms CrooksJarzynski.WorkConvention.discrepancy_summation_by_parts
#print axioms CrooksJarzynski.WorkConvention.discrepancy_abs_le
#print axioms CrooksJarzynski.WorkConvention.discrepancy_uniform_grid_abs_le
#print axioms CrooksJarzynski.WorkConvention.discrepancy_uniform_tendsto_zero
#print axioms CrooksJarzynski.WorkConvention.discrepancy_tendsto_zero
#print axioms CrooksJarzynski.TransitionThenQuenchProtocol.sum_forwardWeight
#print axioms CrooksJarzynski.Protocol.reverseProtocol_forwardWeight_reverse
#print axioms CrooksJarzynski.Protocol.reverseProtocol_work_reverse
#print axioms CrooksJarzynski.Protocol.work_distribution_crooks
#print axioms CrooksJarzynski.Protocol.work_distribution_crooks_ratio
#print axioms CrooksJarzynski.MeasureProtocol.jarzynski_lintegral
#print axioms CrooksJarzynski.MeasureProtocol.jarzynski_integral
#print axioms CrooksJarzynski.MeasureProtocol.work_distribution_crooks
#print axioms CrooksJarzynski.MeasureProtocol.Markov.compProd_withDensity_fst
#print axioms CrooksJarzynski.MeasureProtocol.Markov.oneStep_crooks
#print axioms CrooksJarzynski.MeasureProtocol.Markov.oneStep_jarzynski
#print axioms CrooksJarzynski.MeasureProtocol.Markov.trajectoryMeasure_step
#print axioms CrooksJarzynski.MeasureProtocol.Markov.reversedFiniteMarginal_eq_reversedForwardPathMeasure
#print axioms CrooksJarzynski.MeasureProtocol.Markov.finiteMarginal_eq_chronologicalForwardPathMeasure
#print axioms CrooksJarzynski.MeasureProtocol.Markov.liftLocalBalance_past
#print axioms CrooksJarzynski.MeasureProtocol.Markov.extendReversedPrefix_crooks
#print axioms CrooksJarzynski.MeasureProtocol.Markov.multiStep_crooks
#print axioms CrooksJarzynski.MeasureProtocol.Markov.multiStep_jarzynski
#print axioms CrooksJarzynski.MeasureProtocol.Markov.multiStep_crooks_chronological
#print axioms CrooksJarzynski.MeasureProtocol.Gibbs.reweight_freeEnergy
#print axioms CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_crooks_physical
#print axioms CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_jarzynski_integral
#print axioms CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_second_law
#print axioms CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_work_distribution_crooks
#print axioms CrooksJarzynski.MeasureProtocol.GaussianExample.multiStep_crooks
#print axioms CrooksJarzynski.MeasureProtocol.GaussianExample.multiStep_jarzynski
#print axioms CrooksJarzynski.MeasureProtocol.MetropolisHastings.detailedBalance
#print axioms CrooksJarzynski.MeasureProtocol.MetropolisExample.proposal_symmetry
#print axioms CrooksJarzynski.MeasureProtocol.MetropolisExample.localBalance
#print axioms CrooksJarzynski.MeasureProtocol.MetropolisExample.multiStep_crooks
#print axioms CrooksJarzynski.MeasureProtocol.MetropolisExample.multiStep_jarzynski
#print axioms CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.crooks_of_reference_density
#print axioms CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.map_pathMeasure_involution
#print axioms CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.JumpPath.crooks_of_density_identity
#print axioms CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.JumpPath.jarzynski_of_density_identity
#print axioms CrooksJarzynski.Protocol.measure_forwardWeight_singleton
#print axioms CrooksJarzynski.Protocol.measure_reverseWeight_singleton
#print axioms CrooksJarzynski.Protocol.measure_crooks
#print axioms CrooksJarzynski.Protocol.measure_jarzynski_integral
