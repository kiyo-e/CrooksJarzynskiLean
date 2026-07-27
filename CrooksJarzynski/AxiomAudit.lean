import CrooksJarzynski

/-!
# Axiom audit

This module prints the kernel axioms used by the headline results.  The CI log
therefore records whether `sorryAx` or any custom axiom has entered the trusted
base of the development.
-/

#print axioms CrooksJarzynski.Protocol.boltzmann_crooks
#print axioms CrooksJarzynski.Protocol.crooks_partition_ratio
#print axioms CrooksJarzynski.Protocol.crooks
#print axioms CrooksJarzynski.Protocol.jarzynski
#print axioms CrooksJarzynski.Protocol.integral_fluctuation_theorem
#print axioms CrooksJarzynski.Protocol.second_law
