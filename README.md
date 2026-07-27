# Crooks–Jarzynski in Lean 4

A machine-checked finite-state, discrete-time development of stochastic thermodynamics.

The library proves, without `sorry` or custom axioms:

- normalization and nonnegativity of forward and reverse path probabilities;
- a multi-step Crooks path identity from local detailed balance;
- the usual Crooks ratio when the reverse path probability is nonzero;
- the Jarzynski equality;
- the integral fluctuation theorem for dissipated work;
- the average-work second law `ΔF ≤ ⟨W⟩`;
- a deterministic quench constructor and a two-state partition-function example.

The pathwise theorem is stated first in the division-free form

```text
P_F(γ) · exp(β ΔF) = P_R(γ†) · exp(β W(γ)),
```

so zero-probability trajectories do not require case splits. The ratio form is a corollary with the expected nonzero hypothesis.

## Build

```bash
lake exe cache get
lake build
```

The project is pinned to Lean and Mathlib `v4.32.0`. GitHub Actions preserves the complete compiler log as the `lean-build-log` artifact on every build attempt.

## Main declarations

```lean
CrooksJarzynski.Protocol.crooks_partition_ratio
CrooksJarzynski.Protocol.crooks
CrooksJarzynski.Protocol.crooks_ratio
CrooksJarzynski.Protocol.jarzynski
CrooksJarzynski.Protocol.integral_fluctuation_theorem
CrooksJarzynski.Protocol.second_law
```

## Scope

The system is finite and the protocol is discrete in time. Every time step consists of an instantaneous energy quench followed by a Markov transition. Forward and reverse kernels are supplied separately and satisfy local detailed balance at the post-quench energy. Reversible dynamics are obtained by choosing the same kernel in both directions.
