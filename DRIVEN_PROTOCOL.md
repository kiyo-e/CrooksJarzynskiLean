# Stepwise driven continuous-time jump protocols

This branch adds a finite-window driven protocol on top of the normalized
fixed-initial finite-state jump-process law.

## Constructed path laws

For each protocol window `i`, a `FiniteJumpGenerator` and a duration determine

```lean
(generator i).pathLawFrom (duration i) x
```

for a prescribed initial state `x`. The forward window kernel records both the
terminal state and the complete finite-jump path:

```lean
γ ↦ (FullPath.terminalState γ, γ)
```

The forward driven law recursively binds the next window at the terminal state
of the preceding window. The reverse experiment starts from the final Gibbs
state, visits protocol windows in reverse order, samples the corresponding
fixed-initial path law, and stores the reversed complete path as its mark.

The principal declarations are:

```lean
MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.forwardWindowKernel
MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.reverseWindowKernel
MeasureProtocol.ContinuousTimeJump.Driven.forwardDrivenLaw
MeasureProtocol.ContinuousTimeJump.Driven.reverseDrivenLaw
```

The kernel support records the window-boundary matching explicitly:

```lean
MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.forwardWindowKernel_ae_boundary
MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.reverseWindowKernel_ae_boundary
```

The forward theorem states almost surely that the stored path starts at the
kernel input and terminates at the recorded next endpoint. The reverse theorem
states that the forward-aligned reversed path starts at its recorded preceding
endpoint and terminates at the reverse kernel input.

## Work convention

The work observable is the sum of the instantaneous energy switches evaluated
at the terminal state of each window:

```text
W = Σᵢ [Eᵢ₊₁(Xᵢ,end) - Eᵢ(Xᵢ,end)].
```

This is the transition-then-quench convention. For one window, the formalized
observable reduces exactly to the terminal quench:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.work_one
```

The product of the endpoint Gibbs work factors is proved equal to
`exp (-β W)`, while the product of free-energy factors is proved equal to
`exp (-β ΔF)`.

## Headline results

The low-level marked-path theorems accept one measure-level `WindowBalance`
hypothesis per window:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.crooks
MeasureProtocol.ContinuousTimeJump.Driven.jarzynski
MeasureProtocol.ContinuousTimeJump.Driven.second_law
```

For finite counting spaces, the generator-to-window bridge discharges those
hypotheses from instantaneous Gibbs detailed balance. The resulting public
statements are:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.crooks_of_gibbsDetailedBalance
MeasureProtocol.ContinuousTimeJump.Driven.jarzynski_of_gibbsDetailedBalance
MeasureProtocol.ContinuousTimeJump.Driven.second_law_of_gibbsDetailedBalance
```

All of these theorems concern the recursively constructed `pathLawFrom`-driven
measures, rather than an abstract sequence of endpoint kernels or a sector-mass
surrogate.

The marked-path induction supporting them is exposed separately through:

```lean
MeasureProtocol.Marked.extendEndpoint_crooks
MeasureProtocol.Marked.multiStep_endpoint_crooks
MeasureProtocol.Marked.multiStep_endpoint_jarzynski
MeasureProtocol.Marked.multiStep_endpoint_crooks_physical
MeasureProtocol.Marked.multiStep_endpoint_jarzynski_integral
MeasureProtocol.Marked.multiStep_endpoint_second_law
```

## Detailed balance interface

The generator-level hypothesis is division-free:

```lean
weight x * G.jumpRate x y = weight y * G.jumpRate y x.
```

For Gibbs weights, this becomes `FiniteJumpGenerator.IsGibbsDetailedBalance`.
The forward jump-rate product weighted at the initial state is proved equal to
the reversed jump-rate product weighted at the terminal state:

```lean
FiniteJumpGenerator.weight_mul_jumpProduct_eq_reverse
FiniteJumpGenerator.gibbsWeight_mul_jumpProduct_eq_reverse
```

The unsymmetrized finite-state counting chart is already invariant under path
reversal. The weighted sum of the actual fixed-initial sector laws is identified
with the common-reference weighted sector law, and the identity is summed over
all jump counts. Normalizing the finite Gibbs weights then gives a reversible
mixture of the actual `pathLawFrom` laws.

The endpoint-marked transport is summarized by:

```lean
FiniteJumpGenerator.sum_smul_pathLawFrom
FiniteJumpGenerator.map_weightedFullPathLaw_reverse
FiniteJumpGenerator.gibbsPathLaw_eq_weightedFullPathLaw
FiniteJumpGenerator.windowBalance_of_gibbsDetailedBalance
```

For the counting-measure Gibbs specialization, the partition function and free
energy are exposed in explicit finite-sum form through
`FiniteJumpGenerator.finitePartitionFunction` and
`FiniteJumpGenerator.finiteFreeEnergy`.

## Deferred extensions

The present path carrier is a reverse-oriented tuple of complete window paths.
Boundary continuity is proved almost surely for the constructed laws; a subtype
or structure that stores the same equalities as fields can be added without
changing the measure construction.

A later extension may also concatenate the window marks into one global
real-time trajectory. General calendar-time-dependent rates and integrated
hazards remain outside this stepwise protocol layer.
