# Related work and positioning

- Review completed: 2026-08-26; final quality check: 2026-08-27.
- CrooksJarzynskiLean core-formalization baseline: [`efbf55e`](https://github.com/kiyo-e/CrooksJarzynskiLean/commit/efbf55ea2876fe016df8d64b25a661a7394b6464). The manuscript sources and the interior-time theorem live in the artifact commit that extends this baseline; a release replaces both references with a single versioned artifact tag.
- Intended audience: researchers in stochastic thermodynamics, probability, and interactive theorem proving.

## Positioning in one sentence

CrooksJarzynskiLean contributes an end-to-end Lean 4 construction that starts from finite-state jump generators, builds normalized fixed-horizon path measures, identifies their actual terminal and finite-dimensional laws with the matrix-exponential semigroup, and transports windowwise Gibbs detailed balance through finitely many piecewise-constant windows to global Crooks--Jarzynski relations.

The fluctuation relations, finite-state CTMC theory, and jump-path densities are classical. The contribution is the machine-checked connection between them.

## What is and is not claimed

A safe paper statement is:

> We present an end-to-end Lean 4 construction that starts from finite-state jump generators, builds normalized finite-horizon path measures, identifies their terminal and finite-dimensional laws with the matrix-exponential semigroup, and transports windowwise Gibbs detailed balance through finitely many piecewise-constant protocol windows to global Crooks--Jarzynski relations.

The following priority claims are intentionally avoided:

- first formalization of continuous-time Markov chains;
- first Lean CTMC or jump-and-hold path law;
- first machine-checked proof of non-explosion;
- first Lean trajectory measure;
- first formalization of thermodynamics or statistical mechanics in Lean;
- first Lean fluctuation theorem, Crooks relation, Jarzynski identity, or second-law consequence; and
- first rigorous Markov-jump path density.

The fully connected scope is finite-state, finite-horizon, and finitely many piecewise-constant protocol windows. The project does not claim arbitrary calendar-time-dependent rates, countably infinite state spaces, diffusions, Langevin dynamics, or SDE path measures.

## Comparison by the connected probability law

The important comparison is not whether an artifact contains an individual CTMC or fluctuation theorem, but whether it connects all layers to the same constructed law.

| Development | CTMC or trajectory law | Non-explosion form | Constructed terminal law identified with `exp(TQ)` | FDD identified with kernel chain | Global driven path law | Crooks/Jarzynski on that law |
| --- | --- | --- | --- | --- | --- | --- |
| [Hölzl / AFP Markov Models](https://isa-afp.org/entries/Markov_Models.html) | Jump-and-hold CTMC in Isabelle/HOL | Infinite-process a.s. non-explosion under bounded escape rates in the current AFP artifact | Not identified in the reviewed source snapshot | Not a stated focus | No | No |
| [Marion / Mathlib](https://arxiv.org/abs/2506.18616) | General Ionescu--Tulcea trajectory measure | Not specific to CTMC explosion | General infrastructure rather than this bridge | General trajectory infrastructure | No | No |
| [Ripple](https://github.com/zinan-huang/Ripple/tree/e9ce148d3975f9e75bb9724e01ec763ad9b368a9) | Canonical finite-state CTMC jump-and-hold law | Infinite record construction, a.s. under additional assumptions | A matrix-exponential transition API exists; a bridge from the reviewed canonical law was not identified | A bridge from the reviewed canonical law was not identified | No | No |
| [PhysicsAI DFT moment body](https://github.com/gecrooks/PhysicsAI/tree/0e03deca084de46e11047a8bb9aafa3e22261a70/dft-moment-body) | Takes a DFT measure identity as input | Not applicable | Not applicable | Not applicable | No | Abstract DFT consequences, integral FT, second law, and Crooks pairs |
| CrooksJarzynskiLean | Sum of explicit fixed-horizon jump-count sectors | Finite-horizon arrival tail vanishes, so no mass escapes to infinitely many jumps | Yes, for the actual terminal pushforward | Yes, for every finite monotone observation family | Yes, by measurable concatenation of complete windows | Yes, on the resulting global laws |

“Not identified” reports a search of the specified public snapshot. It is negative evidence, not a mathematical proof of absence.

## Classical stochastic thermodynamics

Jarzynski introduced the nonequilibrium work equality in 1997 and also derived it using a time-dependent master equation. Crooks derived forward/reverse work relations for microscopically reversible Markovian dynamics and developed the path-ensemble formulation. For continuous-time Markov and jump processes, path-space entropy production and fluctuation symmetries were developed by Lebowitz--Spohn, Maes--Netočný, Seifert, and others. Time-dependent finite-state jump processes and detailed fluctuation theorems are standard models.

Principal sources:

- C. Jarzynski, [“A nonequilibrium equality for free energy differences”](https://arxiv.org/abs/cond-mat/9610209), *Physical Review Letters* 78 (1997).
- C. Jarzynski, [“Equilibrium free energy differences from nonequilibrium measurements: a master equation approach”](https://arxiv.org/abs/cond-mat/9707325), *Physical Review E* 56 (1997).
- G. E. Crooks, [“Nonequilibrium Measurements of Free Energy Differences for Microscopically Reversible Markovian Systems”](https://doi.org/10.1023/A:1023208217925), *Journal of Statistical Physics* 90 (1998).
- G. E. Crooks, [“The Entropy Production Fluctuation Theorem and the Nonequilibrium Work Relation for Free Energy Differences”](https://arxiv.org/abs/cond-mat/9901352), *Physical Review E* 60 (1999).
- J. L. Lebowitz and H. Spohn, [“A Gallavotti--Cohen Type Symmetry in the Large Deviation Functional for Stochastic Dynamics”](https://arxiv.org/abs/cond-mat/9811220), *Journal of Statistical Physics* 95 (1999).
- C. Maes and K. Netočný, [“Time-Reversal and Entropy”](https://doi.org/10.1023/A:1021026930129), *Journal of Statistical Physics* 110 (2003).
- U. Seifert, [“Entropy Production along a Stochastic Trajectory and an Integral Fluctuation Theorem”](https://doi.org/10.1103/PhysRevLett.95.040602), *Physical Review Letters* 95 (2005).
- R. Rao and M. Esposito, [“Detailed Fluctuation Theorems: A Unifying Perspective”](https://doi.org/10.3390/e20090635), *Entropy* 20 (2018).

Accordingly, the paper states explicitly:

> The fluctuation relations formalized here are classical. Our contribution is a machine-checked construction that connects them to explicitly constructed finite-state jump-process path measures.

## CTMC path laws and matrix exponentials

The embedded jump chain, exponential holding times, explosion theory, Kolmogorov equations, and `P_t = exp(tQ)` are standard; a primary textbook reference is J. R. Norris, *Markov Chains*, Chapter 2. Explicit finite-state jump-path densities on a disjoint union of finite records are also standard. Rao and Teh give a closely related path representation and density in the Markov-jump-process literature.

- J. R. Norris, [*Markov Chains*](https://www.cambridge.org/core/books/markov-chains/B0A8AB4D3187DFE76E17B1E7F33D1B20), Cambridge University Press (1997).
- V. Rao and Y. W. Teh, [“Fast MCMC Sampling for Markov Jump Processes and Extensions”](https://www.jmlr.org/papers/v14/rao13a.html), *JMLR* 14 (2013).

The free-coordinate path density and products of matrix exponentials are therefore not novelty claims. The formal contribution is the verified bridge from the constructed measure to those standard objects.

## Mechanized probability and physics

### Isabelle/HOL

Johannes Hölzl's [“Markov Processes in Isabelle/HOL”](https://doi.org/10.1145/3018610.3018628) constructs Markov processes and a jump-and-hold CTMC, proving the Markov property, a transition semigroup, and a backward equation. The current [AFP Markov Models](https://isa-afp.org/entries/Markov_Models.html) artifact also contains an almost-sure non-explosion result under bounded escape rates. This rules out broad “first mechanized CTMC” and “first formal non-explosion” claims.

### Lean trajectory measures

Étienne Marion's [formalization of the Ionescu--Tulcea theorem in Mathlib](https://arxiv.org/abs/2506.18616) provides general trajectory-measure infrastructure. CrooksJarzynskiLean should be presented as an application and extension within that ecosystem, not as the first Lean trajectory measure.

### Ripple

[Ripple](https://github.com/zinan-huang/Ripple) is the closest Lean CTMC comparison. The reviewed snapshot, commit [`e9ce148d`](https://github.com/zinan-huang/Ripple/commit/e9ce148d3975f9e75bb9724e01ec763ad9b368a9), includes finite-state Q-matrices, exponential holding-time laws, an embedded chain, a canonical Ionescu--Tulcea record measure, matrix-exponential transition probabilities, and non-explosion results for its infinite record construction under additional assumptions.

In that snapshot, the review did not identify a theorem connecting the terminal pushforward of the canonical path law to the matrix-exponential transition API, a finite-dimensional pushforward bridge, or a driven stochastic-thermodynamic layer. This comparison must be rechecked against a fixed Ripple commit immediately before submission.

### PhysicsAI DFT moment body

The reviewed [PhysicsAI DFT moment-body snapshot](https://github.com/gecrooks/PhysicsAI/tree/0e03deca084de46e11047a8bb9aafa3e22261a70/dft-moment-body) formalizes a detailed fluctuation theorem as a measure identity and derives reflection, integral fluctuation, second-law, moment, and finite-support Crooks-pair consequences. It assumes the DFT law rather than constructing Markov generators, holding times, CTMC path measures, global driven protocols, or physical work/free energy.

The two projects are complementary: PhysicsAI studies the structure and consequences of fluctuation-symmetric distributions, while CrooksJarzynskiLean derives a physical fluctuation relation from explicit finite-state dynamics.

### Lean physics ecosystem

[LeanChemicalTheories](https://arxiv.org/abs/2210.12150) and [Physlib](https://github.com/leanprover-community/physlib) are prior Lean developments in chemical physics, thermodynamics, and canonical ensembles. They rule out broad priority claims about formalizing thermodynamics or statistical mechanics in Lean, while providing relevant ecosystem context.

## Search-bounded positioning statement

The following language may be used in the paper or artifact description:

> To our knowledge, among the public Lean 4 and Mathlib artifacts reviewed at the fixed snapshots recorded in the bibliography (search completed on 26 August 2026), we did not identify a development that connects an explicitly constructed finite-state continuous-time jump-process path measure to its matrix-exponential terminal and finite-dimensional laws and then to global path measures for finitely many piecewise-constant protocol windows carrying physical Crooks--Jarzynski work relations.

This is a bounded search report, not a universal “first” claim. The reviewed search covered primary papers, official artifacts, arXiv, AFP, Mathlib, and public GitHub sources. It does not cover private repositories, unpublished manuscripts, or every proof-assistant project in every language.

The full bibliography used by the manuscript is in [`paper/references.bib`](paper/references.bib).
