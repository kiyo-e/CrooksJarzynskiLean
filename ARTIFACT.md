# Artifact guide

This file is a reviewer-oriented route through the continuous-time theorem
spine of the development: from a finite-state jump generator to global
Crooks–Jarzynski fluctuation relations on constructed path measures. It
complements [FORMALIZATION.md](./FORMALIZATION.md), which maps every
paper-level statement to its Lean declaration, and
[DRIVEN_PROTOCOL.md](./DRIVEN_PROTOCOL.md), which records the design of the
driven-window layer.

Unless stated otherwise, all declarations below live in the namespace
`CrooksJarzynski.MeasureProtocol.ContinuousTimeJump` and all modules live
under `CrooksJarzynski/`.

## Building and checking the artifact

The project is pinned by `lean-toolchain` (Lean 4), `lakefile.lean`
(Mathlib and Physlib, the latter by commit), and `lake-manifest.json`.
The principal verification commands are:

```sh
lake exe cache get
lake build
lake env lean CrooksJarzynski/AxiomAudit.lean
lake env lean CrooksJarzynski/AxiomAuditDriven.lean
```

`lake build` compiles the whole library. The two audit files run
`#print axioms` on the headline theorems; every report should list at most
the standard foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`.

The continuous-integration workflow (`.github/workflows/lean.yml`)
additionally rejects proof placeholders (`sorry`, `admit`, `sorryAx`) and
custom `axiom`/`constant` declarations anywhere in the library, and fails if
the kernel audit reports an axiom outside the approved set or misses a
headline theorem.

## The six-stage theorem spine

The end-to-end result is organized as six stages. Each stage names the
principal module and the declarations a reviewer should open first.

### Stage 1 — Nonzero fixed-horizon reference and simplex volume

Module: `ContinuousTimeJumpSimplex.lean` (namespace suffix `Simplex`).

A path with exactly `n` jumps within a horizon `T` is charted by free simplex
coordinates; the final holding interval is the no-jump remainder.

- `Simplex.volume_freeSimplexSet` — the free `n`-simplex has volume `1/n!`,
  so the scaled reference is nonzero (see also
  `Simplex.volume_freeSimplexSet_pos`).
- `Simplex.sum_holdingTimesOfFree` — the reconstructed holding times sum to
  the full horizon, so the chart really parameterizes fixed-horizon paths.

### Stage 2 — Sector masses, tail disappearance, and normalization

Module: `ContinuousTimeJumpFiniteGeneratorPathLaw.lean`
(namespace suffix `FiniteJumpGenerator`).

- `tendsto_arrivalMassFrom` — the unfinished-arrival mass admits a
  Poisson-type bound `(RT)^n / n!` and tends to zero: no probability escapes
  to infinitely many jumps within the horizon.
- `tsum_sectorMassFrom` — the fixed-jump-count sector masses sum to one.

### Stage 3 — Actual probability measure and terminal-coordinate bridge

Module: `ContinuousTimeJumpFiniteGeneratorFullPath.lean`
(namespace suffix `FiniteJumpGenerator`).

- `pathLawFrom` — the fixed-initial, fixed-horizon path law on the dependent
  sum `FullPath` of all finite jump-count sectors.
- `instIsProbabilityMeasurePathLawFrom` — that law is a probability measure.
- `pathLawFrom_terminalState_singleton` — the bridge theorem: the arithmetic
  transition mass is the terminal-state pushforward of the constructed law,
  not merely a numerical coincidence.

### Stage 4 — Matrix-exponential terminal law and Markov semigroup

Modules: `ContinuousTimeJumpFiniteGeneratorBridge.lean` and, for the renewal
analysis it relies on, `ContinuousTimeJumpFiniteGeneratorRenewal.lean` and
`ContinuousTimeJumpRenewalIntegrals.lean`.

- `pathLawFrom_terminalState_eq_exp_generator` — the terminal marginal of the
  constructed law is the corresponding row of `exp (T • Q)`. The proof
  matches a first-jump renewal equation satisfied by the path construction
  against a uniqueness theorem for the matrix-exponential solution.
- `transitionKernel_add` (in `ContinuousTimeJumpConcatPathLawBridge.lean`) —
  the terminal laws form a Mathlib Markov kernel satisfying
  Chapman–Kolmogorov, obtained as the shadow of a path-level
  cut-and-concatenate identity.

### Stage 5 — Finite-dimensional distributions

Module: `ContinuousTimeJumpFiniteDimensional.lean`
(namespace suffix `FiniteJumpGenerator`).

- `pathLawFrom_finiteDimensional_eq` — sampling the right-continuous
  trajectory at monotone observation times pushes the path law forward to
  Mathlib's chronological finite path measure of the transition kernels.
- `pathLawFrom_sampleAt_real_singleton_eq_exp_product` — consequently every
  finite-dimensional atom is a product of matrix-exponential entries.

### Stage 6 — Global driven path law and fluctuation relations

Modules: `ContinuousTimeJumpDrivenConcat.lean`,
`ContinuousTimeJumpDrivenGlobalLaw.lean`, and
`ContinuousTimeJumpDrivenGlobalCrooks.lean` (namespace suffix `Driven`).

- `concatenateWindows` — measurable chronological concatenation of finitely
  many complete window paths into one global `FullPath`.
- `forwardGlobalLaw`, `reverseGlobalLaw` — the global forward and reverse
  laws as pushforwards of the marked window laws along concatenation.
- `global_crooks_of_gibbsDetailedBalance` — the division-free measure-level
  Crooks relation on the global chart, from local Gibbs detailed balance in
  every window.
- `global_jarzynski_of_gibbsDetailedBalance` — Jarzynski's equality on the
  global law.
- `global_second_law_of_gibbsDetailedBalance` — the average-work second law
  `ΔF ≤ ⟨W⟩`.
- `global_work_distribution_crooks_of_gibbsDetailedBalance` — the work-law
  Crooks relation mapped to the work coordinate.

## Examples and regression targets

- `ContinuousTimeJumpTwoState.lean` and the
  `ContinuousTimeJumpTwoStateAsymmetric*.lean` files — symmetric and
  asymmetric two-state chains: explicit sector masses, Poisson jump-count
  law, parity-filtered `exp (T • Q)` rows, and exact work atoms with
  physical Crooks/Jarzynski instances.
- `ContinuousTimeJumpFiniteGeneratorBridge.lean`
  (`ThreeStateBranching`) — a Y-shaped three-state chain validating the
  terminal-law theorem beyond two-state parity arguments.
- `ContinuousTimeJumpDrivenThreeStateTwoWindow.lean` and
  `ContinuousTimeJumpDrivenGlobalThreeStateTwoWindow.lean` — a two-window
  three-state protocol whose work is not almost surely a function of the
  endpoint pair, exercising the retention of full window paths.

## Scope notes for reviewers

The continuous-time headline results are deliberately scoped to finite state
spaces, finite horizons, and finitely many piecewise-constant protocol
windows; reverse dynamics and local detailed balance are supplied as modeled
hypotheses. The repository also contains a broader discrete-time
measure-theoretic development (see [FORMALIZATION.md](./FORMALIZATION.md))
that supports and tests the library but is not part of the six-stage spine.
