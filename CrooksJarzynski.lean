import CrooksJarzynski.Probability
import CrooksJarzynski.Equilibrium
import CrooksJarzynski.Protocol
import CrooksJarzynski.MathlibBridge
import CrooksJarzynski.Examples

/-!
# Finite-state Crooks and Jarzynski theory

This root module exports the complete finite-state, discrete-time development,
including its bridge to Mathlib's measure-theoretic Markov-kernel API. The main
results are `Protocol.crooks`, `Protocol.jarzynski`,
`Protocol.integral_fluctuation_theorem`, and `Protocol.second_law`.
-/
