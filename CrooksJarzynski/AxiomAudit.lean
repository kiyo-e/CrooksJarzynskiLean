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
#print axioms CrooksJarzynski.TransitionThenQuenchProtocol.sum_forwardWeight
#print axioms CrooksJarzynski.Protocol.reverseProtocol_forwardWeight_reverse
#print axioms CrooksJarzynski.Protocol.reverseProtocol_work_reverse
#print axioms CrooksJarzynski.Protocol.work_distribution_crooks
#print axioms CrooksJarzynski.Protocol.work_distribution_crooks_ratio
