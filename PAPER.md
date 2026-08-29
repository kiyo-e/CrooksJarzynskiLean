# Paper and publication package

The continuous-time paper is organized around one deliberately scoped contribution:

> finite-state generator -> normalized fixed-horizon path measure -> finite-horizon sector-tail non-explosion -> actual terminal and finite-dimensional marginals -> measurable global driven path law -> physical Crooks--Jarzynski relations.

The individual physical identities and standard CTMC constructions are classical. The paper contribution is the machine-checked connection between these layers for one explicitly constructed family of probability laws.

## Start here

- [`paper/main.tex`](paper/main.tex) is the full manuscript draft.
- [`paper/references.bib`](paper/references.bib) contains the manuscript bibliography.
- [`RELATED_WORK.md`](RELATED_WORK.md) records the literature comparison, safe novelty language, and bounded search statement.
- [`ARTIFACT.md`](ARTIFACT.md) gives a reviewer-oriented six-stage theorem route through the Lean development.
- [`FORMALIZATION.md`](FORMALIZATION.md) is the complete paper-level-to-Lean declaration map.
- [`DRIVEN_PROTOCOL.md`](DRIVEN_PROTOCOL.md) documents the driven protocol and global path-law design.

## Paper direction

The recommended title is:

> **Machine-Checked Path Measures and Fluctuation Relations for Finite-State Continuous-Time Jump Processes in Lean 4**

The paper does not claim the first mechanized CTMC, the first Lean trajectory measure, the first machine-checked non-explosion theorem, or the first Lean fluctuation theorem. It claims an end-to-end construction for finite-state, finite-horizon jump processes and finitely many piecewise-constant protocol windows.

General calendar-time-dependent hazards, countably infinite state spaces, diffusions, Langevin dynamics, and SDE path measures are outside the current scope.

## Build the manuscript

A TeX Live installation with `latexmk` and `biber` is sufficient:

```bash
cd paper
make
```

The generated PDF and LaTeX auxiliary files are ignored by Git. The Lean artifact itself is built independently with:

```bash
lake exe cache get
lake build
```

## Publication checklist

Before submission, freeze a green versioned release, archive it with a persistent identifier, replace the draft author metadata and artifact baseline, and re-audit the fixed Ripple and PhysicsAI snapshots recorded in [`RELATED_WORK.md`](RELATED_WORK.md).
