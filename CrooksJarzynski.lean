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
import CrooksJarzynski.MathlibBridge
import CrooksJarzynski.PhyslibBridge
import CrooksJarzynski.Examples

/-!
# Crooks–Jarzynski theory

This root module exports the finite-state, discrete-time development together
with a measure-theoretic development on arbitrary measurable state spaces. The
measure-theoretic layer includes one-step and finite-horizon Crooks relations,
the corresponding Lebesgue-integral Jarzynski equalities, and an
Ionescu–Tulcea trajectory-measure adapter for time-inhomogeneous Mathlib Markov
kernels.

The finite-state results include explicit time reversal, both standard
discrete-time work conventions, a path-uniform `O(1/N)` continuous-time limit
for their discrepancy, work-distribution fluctuation relations, bridges to
Mathlib's measure-theoretic Markov-kernel API, and Physlib's finite
canonical-ensemble API. The main results include `Protocol.crooks`,
`Protocol.jarzynski`, `MeasureProtocol.Markov.multiStep_crooks`,
`MeasureProtocol.Markov.multiStep_jarzynski`,
`MeasureProtocol.Markov.trajectoryMeasure`,
`Protocol.work_distribution_crooks`,
`WorkConvention.discrepancy_uniform_tendsto_zero`, and `Protocol.second_law`.
-/
