/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
-/
import CrooksJarzynski.Probability
import CrooksJarzynski.Equilibrium
import CrooksJarzynski.Protocol
import CrooksJarzynski.TimeReversal
import CrooksJarzynski.ContinuousTimeLimit
import CrooksJarzynski.MathlibBridge
import CrooksJarzynski.PhyslibBridge
import CrooksJarzynski.Examples

/-!
# Finite-state Crooks and Jarzynski theory

This root module exports the complete finite-state, discrete-time development,
including explicit time reversal, both standard discrete-time work conventions,
a path-independent continuous-time-limit estimate for those conventions,
work-distribution fluctuation relations, bridges to Mathlib's measure-theoretic
Markov-kernel API, and Physlib's finite canonical-ensemble API. The main results
include `Protocol.crooks`, `Protocol.jarzynski`,
`WorkConvention.uniformMesh_difference_tendsto_zero`,
`Protocol.work_distribution_crooks`, and `Protocol.second_law`.
-/
