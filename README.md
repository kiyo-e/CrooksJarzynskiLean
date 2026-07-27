# Crooks–Jarzynski in Lean 4

A machine-checked finite-state, discrete-time development of stochastic thermodynamics, together with a path-uniform refinement limit for the two standard discrete work conventions.

The library proves, without `sorry` or custom axioms:

- normalization and nonnegativity of forward and reverse path probabilities;
- a multi-step Crooks path identity from local detailed balance;
- the usual Crooks ratio when the reverse path probability is nonzero;
- an explicit physical reverse protocol with reversed energies, kernels, and trajectories;
- sign reversal of work under the physical reverse experiment;
- Crooks' theorem for the probability mass of each exact work value;
- an exact comparison of the quench-then-transition and transition-then-quench work conventions;
- a discrete summation-by-parts identity and a path-uniform `O(1/N)` refinement limit for the difference between those conventions;
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

### Path-uniform continuous-time refinement limit

The module `CrooksJarzynski.WorkConventionLimit` separates this comparison from the stochastic protocol. It needs only an energy schedule and a path. Write

```text
q_i(x) = E_{i+1}(x) - E_i(x)
```

for the energy increment across mesh edge `i`, and let `D_N` be the transition-then-quench work minus the quench-then-transition work on an `N`-edge path. The theorem `WorkConvention.discrepancy_summation_by_parts` proves the discrete summation-by-parts identity

```text
D_N = q_{N-1}(x_N) - q_0(x_0)
    + ∑_{i=1}^{N-1} (q_{i-1}(x_i) - q_i(x_i)).
```

The interior expression compares two temporal increments at the same state. In particular, it contains no state increment and requires no continuity, finite-jump, or probabilistic assumption on the path.

Suppose that a uniform mesh has width `h = T / N` and that the energy increments obey the path-independent bounds

```text
|q_i(x)| ≤ M h,
|q_i(x) - q_{i+1}(x)| ≤ L h².
```

Then `WorkConvention.discrepancy_uniform_grid_abs_le` proves, for every path,

```text
|D_N| ≤ 2 M h + (N - 1) L h²
      ≤ (2 M T + L T²) / N.
```

Consequently, `WorkConvention.discrepancy_tendsto_zero` proves that the two conventions converge to one another for every choice of paths on successively refined meshes. Since the bound is independent of the paths and their probability laws, the convergence is path-uniform. This is a finite-variation time-discretization result for externally driven work; it is not an Itô–Stratonovich conversion statement, and it does not assert a continuous-time Crooks theorem.

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
CrooksJarzynski.WorkConvention.discrepancy_summation_by_parts
CrooksJarzynski.WorkConvention.discrepancy_abs_le
CrooksJarzynski.WorkConvention.discrepancy_uniform_grid_abs_le
CrooksJarzynski.WorkConvention.discrepancy_tendsto_zero
CrooksJarzynski.Protocol.work_distribution_crooks
CrooksJarzynski.Protocol.work_distribution_crooks_ratio
CrooksJarzynski.Protocol.jarzynski
CrooksJarzynski.Protocol.integral_fluctuation_theorem
CrooksJarzynski.Protocol.second_law
```

## Scope

The Crooks–Jarzynski system is finite-state and discrete in time. Every forward time step consists of an instantaneous energy quench followed by a Markov transition. Forward and reverse kernels are supplied separately and satisfy local detailed balance at the post-quench energy. The explicit physical reverse experiment uses the reversed transition first and the reverse quench second. Reversible dynamics are obtained by choosing the same kernel in both directions.

The work-convention refinement theorem has a narrower and more general scope: it is independent of the kernels, path probabilities, and finite-state assumption, but it compares only the two discrete approximations to externally driven work. A measure-theoretic general-state-space Crooks theorem and a genuinely continuous-time stochastic process are outside the current scope.

## References

The formalized results correspond to the finite-state, discrete-time versions of:

- C. Jarzynski, *Nonequilibrium equality for free energy differences*, Phys. Rev. Lett. **78**, 2690 (1997). [doi:10.1103/PhysRevLett.78.2690](https://doi.org/10.1103/PhysRevLett.78.2690)
- G. E. Crooks, *Nonequilibrium measurements of free energy differences for microscopically reversible Markovian systems*, J. Stat. Phys. **90**, 1481 (1998). [doi:10.1023/A:1023208217925](https://doi.org/10.1023/A:1023208217925)
- G. E. Crooks, *Entropy production fluctuation theorem and the nonequilibrium work relation for free energy differences*, Phys. Rev. E **60**, 2721 (1999). [doi:10.1103/PhysRevE.60.2721](https://doi.org/10.1103/PhysRevE.60.2721)
- G. E. Crooks, *Path-ensemble averages in systems driven far from equilibrium*, Phys. Rev. E **61**, 2361 (2000). [doi:10.1103/PhysRevE.61.2361](https://doi.org/10.1103/PhysRevE.61.2361)
- L. Peliti and S. Pigolotti, *Stochastic Thermodynamics: An Introduction*, Princeton University Press (2021) — for the discrete-time conventions.
- P. Hack, S. Gottwald, and D. A. Braun, *Jarzynski's equality and Crooks' fluctuation theorem for general Markov chains with application to decision-making systems*, Entropy **24**, 1731 (2022). [doi:10.3390/e24121731](https://doi.org/10.3390/e24121731) — the closest modern treatment; its discussion of the discrete-time work asymmetry corresponds to `Protocol.workConvention_difference` here.

## License

Released under the Apache License 2.0 (see [LICENSE](LICENSE)), matching the licensing of [Mathlib](https://github.com/leanprover-community/mathlib4) and [Physlib](https://github.com/leanprover-community/physlib). See [CITATION.cff](CITATION.cff) for how to cite this repository.
