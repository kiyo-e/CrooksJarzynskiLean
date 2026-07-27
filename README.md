# Crooks–Jarzynski in Lean 4

A machine-checked finite-state, discrete-time development of stochastic thermodynamics.

The library proves, without `sorry` or custom axioms:

- normalization and nonnegativity of forward and reverse path probabilities;
- a multi-step Crooks path identity from local detailed balance;
- the usual Crooks ratio when the reverse path probability is nonzero;
- an explicit physical reverse protocol with reversed energies, kernels, and trajectories;
- sign reversal of work under the physical reverse experiment;
- Crooks' theorem for the probability mass of each exact work value;
- an exact comparison of the quench-then-transition and transition-then-quench work conventions;
- the Jarzynski equality;
- the integral fluctuation theorem for dissipated work;
- the average-work second law `ΔF ≤ ⟨W⟩`;
- a deterministic quench constructor and a two-state partition-function example.

The pathwise theorem is stated first in the division-free form

```text
P_F(γ) · exp(β ΔF) = P_R(γ†) · exp(β W(γ)),
```

so zero-probability trajectories do not require case splits. The ratio form is a corollary with the expected nonzero hypothesis.

## Time reversal and discrete-time work

A forward step first quenches the energy from `E_t` to `E_{t+1}` while the state remains `x_t`, and then applies a Markov transition at `E_{t+1}`. Its physical time reverse therefore traverses the reverse transition from `x_{t+1}` to `x_t` at `E_{t+1}` and performs the reverse quench only afterward.

The formalization defines trajectory reversal as an involution and constructs this transition-then-quench reverse protocol explicitly. It proves

```text
P_rev(γ†) = P_R(γ†),
W_rev(γ†) = -W(γ).
```

For the same forward schedule, the alternative transition-then-quench convention evaluates each quench at `x_{t+1}` instead of `x_t`. The theorem `Protocol.workConvention_difference` gives the exact trajectory-wise difference between the two conventions, and `Protocol.workConvention_eq_of_stationary` shows that they agree when no transition changes the state.

## Work-distribution Crooks theorem

For an exact work value `w`, let `p_F(w)` be the total forward weight of trajectories with work `w`, and let `p_R(-w)` be the corresponding mass in the explicit reverse experiment. The library proves the division-free identity

```text
p_F(w) · exp(β ΔF) = p_R(-w) · exp(β w),
```

and derives the usual ratio whenever `p_R(-w) ≠ 0`.

## Build

```bash
lake exe cache get
lake build
```

The project is pinned to Lean and Mathlib `v4.32.0`. GitHub Actions preserves the complete compiler log as the `lean-build-log` artifact on every build attempt.

## Main declarations

```lean
CrooksJarzynski.Trajectory.reverse
CrooksJarzynski.Trajectory.reverse_reverse
CrooksJarzynski.Protocol.crooks_partition_ratio
CrooksJarzynski.Protocol.crooks
CrooksJarzynski.Protocol.crooks_ratio
CrooksJarzynski.Protocol.reverseProtocol
CrooksJarzynski.Protocol.reverseProtocol_forwardWeight_reverse
CrooksJarzynski.Protocol.reverseProtocol_work_reverse
CrooksJarzynski.Protocol.workConvention_difference
CrooksJarzynski.Protocol.work_distribution_crooks
CrooksJarzynski.Protocol.work_distribution_crooks_ratio
CrooksJarzynski.Protocol.jarzynski
CrooksJarzynski.Protocol.integral_fluctuation_theorem
CrooksJarzynski.Protocol.second_law
```

## Scope

The system is finite and the protocol is discrete in time. Every forward time step consists of an instantaneous energy quench followed by a Markov transition. Forward and reverse kernels are supplied separately and satisfy local detailed balance at the post-quench energy. The explicit physical reverse experiment uses the reversed transition first and the reverse quench second. Reversible dynamics are obtained by choosing the same kernel in both directions.
