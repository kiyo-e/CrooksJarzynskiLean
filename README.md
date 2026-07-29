# Crooks–Jarzynski in Lean 4

A machine-checked development of stochastic thermodynamics in Lean 4. The library contains a complete finite-state, discrete-time Crooks–Jarzynski theory, a measure-theoretic core for arbitrary measurable state spaces, and a path-uniform refinement limit for the two standard discrete work conventions.

The library proves, without `sorry` or custom axioms:

- a measure-level Crooks relation on arbitrary measurable trajectory spaces and its Lebesgue-integral Jarzynski consequence;
- a one-step Crooks theorem and Jarzynski equality on arbitrary measurable state spaces from equilibrium reweighting and measure-theoretic local detailed balance;
- a finite-horizon, multi-step Crooks theorem on arbitrary measurable state spaces, with chronological paths and measurable path reversal;
- Gibbs specialization from a base measure and measurable energies, including the physical `exp (-β W)` and `exp (-β ΔF)` form;
- real-integral Jarzynski and density-free work-distribution Crooks theorems;
- a non-atomic example on `ℝ` built from a Gaussian base measure;
- a bridge deriving the general measure theorem from the original finite-state protocol;
- an Ionescu–Tulcea trajectory measure for time-inhomogeneous Mathlib Markov kernels, together with its finite-prefix evolution law;
- an identification of every finite-dimensional marginal of that infinite path measure with the recursive finite-horizon forward path measure;
- normalization and nonnegativity of finite forward and reverse path probabilities;
- a finite-state multi-step Crooks path identity from local detailed balance;
- the usual Crooks ratio when the reverse path probability is nonzero;
- an explicit physical reverse protocol with reversed energies, kernels, and trajectories;
- sign reversal of work under the physical reverse experiment;
- Crooks' theorem for the probability mass of each exact work value;
- an exact comparison of the quench-then-transition and transition-then-quench work conventions;
- a discrete summation-by-parts identity and a path-uniform `O(1/N)` refinement limit for the difference between those conventions;
- the finite-state Jarzynski equality;
- the integral fluctuation theorem for dissipated work;
- the average-work second law `ΔF ≤ ⟨W⟩`;
- a deterministic quench constructor and a two-state partition-function example.

The finite pathwise theorem is stated first in the division-free form

```text
P_F(γ) · exp(β ΔF) = P_R(γ†) · exp(β W(γ)),
```

so zero-probability trajectories do not require case splits. The ratio form is a corollary with the expected nonzero hypothesis.

## General measurable state spaces

The module `CrooksJarzynski.MeasureProtocol` moves the probability-theoretic core from finite sums to Mathlib measures and kernels. For an arbitrary measurable trajectory space `Γ`, it represents Crooks' relation by the measure identity

```lean
forward.withDensity workWeight = freeEnergyWeight • reverse
```

and proves

```lean
∫⁻ γ, workWeight γ ∂forward = freeEnergyWeight
```

whenever `reverse` is a probability measure. The specialization `jarzynski_exponential` uses the physical weights `exp (-β W)` and `exp (-β ΔF)`.

For one Markov step on an arbitrary measurable state space `Ω`, the theorem `MeasureProtocol.Markov.oneStep_crooks` assumes the equilibrium reweighting identity

```lean
initial.withDensity workWeight = freeEnergyWeight • final
```

and local detailed balance as an equality of measures on `Ω × Ω`:

```lean
final ⊗ₘ forward = (final ⊗ₘ reverse).map Prod.swap
```

It then proves the corresponding Crooks relation for the forward one-step path measure `initial ⊗ₘ forward`; `oneStep_jarzynski` gives the integral equality directly. This formulation does not use singleton masses, ratios, or a finite-state assumption.

The finite-horizon theorem `MeasureProtocol.Markov.multiStep_crooks` iterates
the same two hypotheses over an arbitrary number of steps. Its chronological
form, `multiStep_crooks_chronological`, transports the internal recursive path
representation to `Fin (n + 1) → Ω` and an explicit measurable path reversal.

`MeasureProtocol.Gibbs` constructs equilibrium measures by exponential tilting
of a base measure and proves that their quench weights satisfy the required
reweighting identity. The resulting physical theorem
`Gibbs.multiStep_crooks_physical` uses the standard weights
`exp (-β W)` and `exp (-β ΔF)`. The same layer proves a real-integral
Jarzynski equality and a work-distribution Crooks relation stated as a
pushforward-measure identity, without assuming a density for the work law. Its
reverse-hand side is explicitly the reverse-work law pushed forward by
`w ↦ -w`, i.e. the measure-theoretic form of `P_R(-W)`.

`MeasureProtocol.GaussianExample` applies the theory on `ℝ` using a Gaussian
base measure and independently resampled Gibbs kernels. Every singleton has
zero mass under the base and equilibrium state measures, so the example
exercises genuinely non-atomic state spaces.
`MeasureProtocolFiniteBridge` proves that the original finite protocol supplies
the measure-level reweighting and local-balance hypotheses and is therefore a
specialization of the general theorem. It also proves pointwise that the
general chronological forward and time-reversed reverse path measures recover
the legacy `forwardWeight` and `reverseWeight`.

For a time-inhomogeneous family `K t : ProbabilityTheory.Kernel Ω Ω`,
`MeasureProtocol.Markov.trajectoryMeasure` adapts each ordinary Markov kernel
to the history-dependent interface used by Mathlib's Ionescu–Tulcea
construction. The resulting probability measure lives on the full path space
`ℕ → Ω`. The theorem
`finiteMarginal_eq_chronologicalForwardPathMeasure` proves that its first
`n + 1` coordinates, for every `n`, have exactly the recursively constructed
chronological finite-horizon path law.

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

Consequently, `WorkConvention.discrepancy_uniform_tendsto_zero` proves directly that, for every `ε > 0`, all paths on every sufficiently fine mesh have discrepancy less than `ε`. The theorem `WorkConvention.discrepancy_tendsto_zero` gives the corresponding convergence for any chosen sequence of paths. Since the bound is independent of the paths and their probability laws, the convergence is path-uniform. This is a finite-variation time-discretization result for externally driven work; it is not an Itô–Stratonovich conversion statement, and it does not assert a continuous-time Crooks theorem.

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
CrooksJarzynski.MeasureProtocol.CrooksRelation
CrooksJarzynski.MeasureProtocol.jarzynski_lintegral
CrooksJarzynski.MeasureProtocol.jarzynski_exponential
CrooksJarzynski.MeasureProtocol.Markov.compProd_withDensity_fst
CrooksJarzynski.MeasureProtocol.Markov.oneStep_crooks
CrooksJarzynski.MeasureProtocol.Markov.oneStep_jarzynski
CrooksJarzynski.MeasureProtocol.Markov.multiStep_crooks
CrooksJarzynski.MeasureProtocol.Markov.multiStep_jarzynski
CrooksJarzynski.MeasureProtocol.Markov.multiStep_crooks_chronological
CrooksJarzynski.MeasureProtocol.Markov.trajectoryMeasure
CrooksJarzynski.MeasureProtocol.Markov.trajectoryMeasure_step
CrooksJarzynski.MeasureProtocol.Markov.finiteMarginal_eq_chronologicalForwardPathMeasure
CrooksJarzynski.MeasureProtocol.Gibbs.reweight_freeEnergy
CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_crooks_physical
CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_jarzynski_integral
CrooksJarzynski.MeasureProtocol.Gibbs.multiStep_work_distribution_crooks
CrooksJarzynski.MeasureProtocol.GaussianExample.multiStep_crooks
CrooksJarzynski.MeasureProtocol.GaussianExample.multiStep_jarzynski
CrooksJarzynski.MathlibBridge.trajectoryMeasure
CrooksJarzynski.Protocol.measure_crooks
CrooksJarzynski.Protocol.measure_jarzynski_integral
CrooksJarzynski.Protocol.measure_forwardWeight_singleton
CrooksJarzynski.Protocol.measure_reverseWeight_singleton
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
CrooksJarzynski.WorkConvention.discrepancy_uniform_tendsto_zero
CrooksJarzynski.WorkConvention.discrepancy_tendsto_zero
CrooksJarzynski.Protocol.work_distribution_crooks
CrooksJarzynski.Protocol.work_distribution_crooks_ratio
CrooksJarzynski.Protocol.jarzynski
CrooksJarzynski.Protocol.integral_fluctuation_theorem
CrooksJarzynski.Protocol.second_law
```

## Scope

The complete finite-horizon, multi-step Crooks–Jarzynski development is
discrete in time but permits arbitrary measurable state spaces. Forward and
reverse kernels are supplied separately and satisfy measure-level local
detailed balance; this library does not construct reverse kernels by
disintegration. The Gibbs specialization assumes the integrability and
nonvanishing conditions needed by Mathlib's exponentially tilted measures.

A genuinely continuous-time stochastic-process theorem is outside the current
scope.

The work-convention refinement theorem has a narrower and more general scope: it is independent of the kernels, path probabilities, and finite-state assumption, but it compares only the two discrete approximations to externally driven work.

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
