import CrooksJarzynski.Probability
import CrooksJarzynski.Equilibrium
import CrooksJarzynski.Protocol
import CrooksJarzynski.MathlibBridge
import CrooksJarzynski.PhyslibBridge
import CrooksJarzynski.Examples

/-!
# Finite-state Crooks and Jarzynski theory

This root module exports the complete finite-state, discrete-time development,
including bridges to Mathlib's measure-theoretic Markov-kernel API and
Physlib's finite canonical-ensemble API. The main results are
`Protocol.crooks`, `Protocol.jarzynski`,
`Protocol.integral_fluctuation_theorem`, and `Protocol.second_law`.
-/
