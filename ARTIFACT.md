# Artifact guide and paper theorem spine

This file gives reviewers and contributors a compact route through the continuous-time result that the paper treats as the main contribution.

## Claim under review

The artifact connects one chain of objects:

> finite-state generator -> normalized fixed-horizon path measure -> finite-horizon sector-tail non-explosion -> actual terminal and finite-dimensional marginals -> measurable global driven path law -> physical Crooks--Jarzynski relations.

The paper does not rely on every module in the repository. The six stages below are the intended reviewer path.

## Snapshot and dependencies

- Archived release: [`v1.0.0`](https://github.com/kiyo-e/CrooksJarzynskiLean/releases/tag/v1.0.0). One checkout of this tag contains the complete formalization -- including the time-reversal mirror theorems (`ContinuousTimeJumpTrajectoryReversal.lean`), the KL dissipation identity (`ContinuousTimeJumpDrivenKL.lean`), and the interior-time theorem (`ContinuousTimeJumpTwoStateInteriorTime.lean`) -- together with the manuscript sources and this artifact guide. An archival copy is deposited on Zenodo: version DOI [10.5281/zenodo.22176568](https://doi.org/10.5281/zenodo.22176568), concept DOI [10.5281/zenodo.22176567](https://doi.org/10.5281/zenodo.22176567).
- Lean toolchain: `leanprover/lean4:v4.32.0`.
- Mathlib and all Lake dependencies: fixed by `lake-manifest.json`.
- Physlib: pinned by commit in `lakefile.lean`.

## Build and proof audit

```bash
lake exe cache get
lake build
```

The CI workflow additionally rejects `sorry`, `admit`, `sorryAx`, and custom `axiom` or `constant` declarations, then runs:

```bash
lake env lean CrooksJarzynski/AxiomAudit.lean
lake env lean CrooksJarzynski/AxiomAuditDriven.lean
```

The audit permits only the standard environment axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Six-stage theorem spine

### 1. A nonzero fixed-horizon reference

File: [`CrooksJarzynski/ContinuousTimeJumpSimplex.lean`](CrooksJarzynski/ContinuousTimeJumpSimplex.lean)

Key declarations:

- `MeasureProtocol.ContinuousTimeJump.Simplex.volume_freeSimplexSet` proves free-coordinate volume `1 / n!`;
- `MeasureProtocol.ContinuousTimeJump.Simplex.sum_holdingTimesOfFree` proves that the residual coordinate makes the total holding time exactly `T`;
- `MeasureProtocol.ContinuousTimeJump.Simplex.rawPathProbability_ae_horizon` proves fixed-horizon support.

Why it matters: restricting ambient product Lebesgue measure to `sum τ = T` would be null. The free-coordinate chart gives a nonzero measure that can be normalized and reversed.

### 2. Tail disappearance and normalization

File: [`CrooksJarzynski/ContinuousTimeJumpFiniteGeneratorPathLaw.lean`](CrooksJarzynski/ContinuousTimeJumpFiniteGeneratorPathLaw.lean)

Key declarations:

- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.tendsto_arrivalMassFrom` proves disappearance of the unfinished-arrival mass;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.sum_sectorMassFrom_add_arrivalMassFrom` is the telescoping identity;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.tsum_sectorMassFrom` proves that all completed sector masses sum to one.

Why it matters: this is the finite-horizon non-explosion argument. No probability mass escapes to infinitely many jumps before the horizon.

### 3. The actual full path probability measure

File: [`CrooksJarzynski/ContinuousTimeJumpFiniteGeneratorFullPath.lean`](CrooksJarzynski/ContinuousTimeJumpFiniteGeneratorFullPath.lean)

Key declarations:

- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom` constructs the measure on the disjoint union of jump sectors;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.instIsProbabilityMeasurePathLawFrom` packages normalization as an `IsProbabilityMeasure` instance;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_terminalState_singleton` proves that the arithmetic transition mass is the terminal pushforward of this measure.

Why it matters: all downstream theorems refer to a constructed probability law, not only to separately computed sector sums.

### 4. Matrix exponential and Markov semigroup

File: [`CrooksJarzynski/ContinuousTimeJumpFiniteGeneratorBridge.lean`](CrooksJarzynski/ContinuousTimeJumpFiniteGeneratorBridge.lean)

Key declarations:

- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionReal_eq_exp` identifies the residual-fraction renewal solution with the matrix exponential;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_terminalState_eq_exp_generator` identifies the actual terminal marginal with a row of `exp (TQ)`;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel` packages the terminal laws as a Mathlib Markov kernel;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.transitionKernel_add` proves the kernel semigroup law.

Related path-level result:

- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_add` in `ContinuousTimeJumpConcatPathLaw.lean` proves Chapman--Kolmogorov before taking the terminal pushforward.

### 5. Finite-dimensional distributions

File: [`CrooksJarzynski/ContinuousTimeJumpFiniteDimensional.lean`](CrooksJarzynski/ContinuousTimeJumpFiniteDimensional.lean)

Key declarations:

- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_finiteDimensional_eq` identifies the finite-time sampling pushforward with the chronological transition-kernel path measure for nondecreasing observation families starting at time zero;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_sampleAt_real_singleton_eq_exp_product` gives the matrix-exponential product formula for the corresponding finite-dimensional atoms;
- `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_finiteDimensional_eq_general` and `MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.pathLawFrom_sampleAt_real_singleton_eq_exp_product_general` extend both statements to arbitrary nondecreasing observation times, without the time-zero requirement.

Why it matters: the bridge is not restricted to the endpoint. The constructed real-time path has the expected finite-dimensional laws.

### 6. Global driven laws and fluctuation relations

Files:

- [`CrooksJarzynski/ContinuousTimeJumpDrivenConcat.lean`](CrooksJarzynski/ContinuousTimeJumpDrivenConcat.lean)
- [`CrooksJarzynski/ContinuousTimeJumpDrivenGlobalLaw.lean`](CrooksJarzynski/ContinuousTimeJumpDrivenGlobalLaw.lean)
- [`CrooksJarzynski/ContinuousTimeJumpDrivenGlobalCrooks.lean`](CrooksJarzynski/ContinuousTimeJumpDrivenGlobalCrooks.lean)

Key declarations:

- `MeasureProtocol.ContinuousTimeJump.Driven.concatenateWindows` glues complete window paths in chronological order;
- `MeasureProtocol.ContinuousTimeJump.Driven.measurable_concatenateWindows` proves measurability;
- `MeasureProtocol.ContinuousTimeJump.Driven.forwardGlobalLaw` and `reverseGlobalLaw` construct probability laws on one global `FullPath` chart;
- `MeasureProtocol.ContinuousTimeJump.Driven.globalWork` reads switching work from the global trajectory;
- `MeasureProtocol.ContinuousTimeJump.Driven.global_crooks_of_gibbsDetailedBalance` proves the global path-measure Crooks relation;
- `MeasureProtocol.ContinuousTimeJump.Driven.global_jarzynski_of_gibbsDetailedBalance` proves Jarzynski's equality;
- `MeasureProtocol.ContinuousTimeJump.Driven.global_second_law_of_gibbsDetailedBalance` proves the average-work second law;
- `MeasureProtocol.ContinuousTimeJump.Driven.global_work_distribution_crooks_reverseWork_of_gibbsDetailedBalance` and `global_crooks_work_atom_of_gibbsDetailedBalance` provide the work-distribution and conventional atomwise forms.

## Concrete validation targets

- `FiniteJumpGenerator.ThreeStateBranching` exercises a genuinely branching chain beyond two-state parity.
- `Driven.ThreeStateTwoWindow` has positive-probability work values `0` and `log 2`, including events with the same endpoint pair `(0, 0)`, proving that work is not almost surely an endpoint-only observable.
- `TwoState.AsymmetricExample` supplies explicit rates, Gibbs weights, partition functions, free energy, work atoms, mean work, strict second law, and a one-window driven specialization.

## Documentation map

- [`PAPER.md`](PAPER.md): publication-package entry point;
- [`paper/main.tex`](paper/main.tex): manuscript draft;
- [`RELATED_WORK.md`](RELATED_WORK.md): literature positioning and bounded priority statement;
- [`FORMALIZATION.md`](FORMALIZATION.md): complete paper-level-to-Lean declaration map;
- [`DRIVEN_PROTOCOL.md`](DRIVEN_PROTOCOL.md): design notes for marked windows, concatenation, global work, and examples;
- [`CITATION.cff`](CITATION.cff): software citation metadata.

## Release checklist

1. Freeze a versioned tag from a green CI commit.
2. Archive the tag and add its DOI to `CITATION.cff` and the paper.
3. Re-audit Ripple and PhysicsAI at fixed commits and update `RELATED_WORK.md` if their scope has changed.
4. Compile `paper/main.tex` and archive the PDF with the source.
5. Keep the abstract and introduction focused on the end-to-end connection rather than on broad “first” claims.
