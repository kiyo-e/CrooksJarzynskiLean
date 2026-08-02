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

Assuming measure-level path balance for every window, the constructed path laws
satisfy:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.crooks
MeasureProtocol.ContinuousTimeJump.Driven.jarzynski
MeasureProtocol.ContinuousTimeJump.Driven.second_law
```

These theorems concern the recursively constructed `pathLawFrom`-driven
measures, rather than an abstract sequence of endpoint kernels.

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

This pathwise identity is the algebraic core required to derive the remaining
measure-level `WindowBalance` theorem from generator detailed balance.

## Remaining bridge

The current public Crooks, Jarzynski, and second-law theorems accept one
`WindowBalance` hypothesis per protocol window. The remaining general bridge is
to combine:

1. reversal invariance of the fixed-jump-count simplex reference;
2. the Gibbs jump-product identity above;
3. equality of forward and aligned reverse holding factors; and
4. the countable sum over all jump-count sectors.

Once that bridge is complete, the headline results can expose only the
instantaneous generator detailed-balance assumptions.
