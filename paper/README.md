# Paper draft

This directory contains the first full manuscript draft for the continuous-time core of CrooksJarzynskiLean.

## Direction

The paper is deliberately centered on one end-to-end contribution:

> finite-state generator -> normalized fixed-horizon path measure -> finite-horizon sector-tail non-explosion -> actual terminal and finite-dimensional marginals -> piecewise-constant global driven path law -> physical Crooks--Jarzynski relations.

The manuscript does **not** claim new fluctuation identities, the first mechanized CTMC, the first Lean trajectory measure, or the first Lean fluctuation theorem. See [`../RELATED_WORK.md`](../RELATED_WORK.md) for the reviewed comparison and the exact scope of the positioning statement.

## Build

A standard TeX Live installation with `latexmk` and `biber` is sufficient:

```bash
cd paper
make
```

The generated `main.pdf` is intentionally ignored by Git. Use `make clean` to remove auxiliary files.

## Files

- [`main.tex`](main.tex): manuscript entry point and shared preamble;
- [`sections/`](sections/): the eleven top-level paper sections;
- [`references.bib`](references.bib): paper bibliography;
- [`Makefile`](Makefile): reproducible local build.

The Lean theorem spine is documented in [`../ARTIFACT.md`](../ARTIFACT.md) and the complete declaration map remains in [`../FORMALIZATION.md`](../FORMALIZATION.md).

## Before submission

1. Replace the draft author name and affiliation as appropriate.
2. Freeze a versioned release and archival DOI, then update the artifact snapshot in the paper and `CITATION.cff`.
3. Re-audit the fixed Ripple and PhysicsAI comparison snapshots immediately before submission.
4. Select the venue template only after the content and page budget are stable; `main.tex` currently uses the portable `article` class.
