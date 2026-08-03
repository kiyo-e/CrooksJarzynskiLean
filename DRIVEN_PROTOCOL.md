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

The raw kernel laws satisfy boundary matching almost surely:

```lean
MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.forwardWindowKernel_ae_boundary
MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator.reverseWindowKernel_ae_boundary
```

The forward theorem states that the stored path starts at the kernel input and
terminates at the recorded next endpoint. The reverse theorem states that the
forward-aligned reversed path starts at its recorded preceding endpoint and
terminates at the reverse kernel input.

The recursively constructed laws inherit all window equations simultaneously:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.forwardDrivenLaw_ae_isBoundaryConsistent
MeasureProtocol.ContinuousTimeJump.Driven.reverseDrivenLaw_ae_isBoundaryConsistent
```

Thus both laws are almost surely supported on `Driven.IsBoundaryConsistent`.
The same equations are also available structurally, rather than only almost
surely. `Driven.ConnectedPath` is the corresponding subtype. New windows can
be added with their endpoint equations through:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.IsBoundaryConsistent
MeasureProtocol.ContinuousTimeJump.Driven.ConnectedPath
MeasureProtocol.ContinuousTimeJump.Driven.ConnectedPath.prepend
```

## Work convention

The work observable is the sum of the instantaneous energy switches evaluated
at the terminal state of each window:

```text
W = Σᵢ [Eᵢ₊₁(Xᵢ,end) - Eᵢ(Xᵢ,end)].
```

The carrier stores windows in reverse chronological order, so `endpointAt`
reads the endpoint associated with a protocol index. The recursive definition
is identified with the ordinary finite sum by:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.endpointAt
MeasureProtocol.ContinuousTimeJump.Driven.reversedEndpointSum_eq_sum
MeasureProtocol.ContinuousTimeJump.Driven.work_eq_sum
```

For one window, the observable reduces exactly to the terminal quench:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.work_one
```

On a finite state space and over finitely many windows, work is uniformly
bounded. Consequently, it is integrable under every finite measure on driven
paths; the constructed forward and reverse laws with probability boundary
measures are the two corollaries used downstream:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.workBound
MeasureProtocol.ContinuousTimeJump.Driven.norm_work_le
MeasureProtocol.ContinuousTimeJump.Driven.integrable_work_of_isFiniteMeasure
MeasureProtocol.ContinuousTimeJump.Driven.integrable_work
MeasureProtocol.ContinuousTimeJump.Driven.integrable_work_reverse
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

All three theorems concern the recursively constructed `pathLawFrom`-driven
measures, rather than an abstract sequence of endpoint kernels or a sector-mass
surrogate. The public second-law theorem has no separate work-integrability
argument: `Driven.integrable_work` supplies it internally.

The measure-level relation is also connected to the presentation standard in
the physics literature. The reverse experiment's own work observable
`reverseWork` is defined intrinsically in reverse chronology and proved equal
to the negated forward work on the aligned carrier; pushing the measure-level
relation forward along the work observable then yields the work-distribution
Crooks relation, and evaluating it on singleton events yields the conventional
atomwise ratio `P_F(W = w) = e^{β(w-ΔF)} P_R(W_R = -w)`:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.reverseWork
MeasureProtocol.ContinuousTimeJump.Driven.reverseWork_eq_neg
MeasureProtocol.ContinuousTimeJump.Driven.work_distribution_crooks_of_gibbsDetailedBalance
MeasureProtocol.ContinuousTimeJump.Driven.crooks_work_atom_of_gibbsDetailedBalance
```

Beyond the one-window recovery of the legacy quench model, a genuinely
multi-window example instantiates the headlines on three states with two
distinct generators and three energy landscapes.  Its endpoint work observable
provably separates two boundary-consistent carrier points (a `0 → 1 → 0` hop
through the raised state versus resting), so the work function is genuinely
nonconstant on structurally connected paths.  Every window mark of both
comparison points is a valid real-time trajectory chart — the hop marks hold
each state for half a unit window (`hopMark_isValid`, `restMark_isValid`).  This does not by itself assert
nondegeneracy of the pushforward work distribution — for zero window durations
the constructed laws never leave the initial state — and no such distributional
claim is made:

```lean
MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.crooks
MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.jarzynski_eq_one
MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.second_law
MeasureProtocol.ContinuousTimeJump.Driven.ThreeStateTwoWindow.work_not_constant
```

The marked-path induction supporting the headline statements is exposed
separately through:

```lean
MeasureProtocol.Marked.extendEndpoint_crooks
MeasureProtocol.Marked.multiStep_endpoint_crooks
MeasureProtocol.Marked.multiStep_endpoint_jarzynski
MeasureProtocol.Marked.multiStep_endpoint_crooks_physical
MeasureProtocol.Marked.multiStep_endpoint_jarzynski_integral
MeasureProtocol.Marked.multiStep_endpoint_second_law
```

## Detailed-balance interface

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

The unsymmetrized finite-state counting chart is invariant under path reversal.
The weighted sum of the actual fixed-initial sector laws is identified with the
common-reference weighted sector law, and the identity is summed over all jump
counts. Normalizing the finite Gibbs weights then gives a reversible mixture of
the actual `pathLawFrom` laws.

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

### Two independent formalization routes

Detailed balance is lifted to the path level along two deliberately
independent routes, and only one of them feeds the headline theorems.

The *density route* (`ContinuousTimeJumpDrivenDensity`) proves that the Gibbs
forward rate density and the aligned reverse rate density agree pointwise on
the reversal-invariant counting chart, and derives fixed-sector and
all-jump-count Gibbs reversal statements from that pointwise identity.  It is
a pointwise-density formalization strategy in the style of the existing
two-state Crooks development.

The *mixture route* (`ContinuousTimeJumpDrivenMixture`,
`ContinuousTimeJumpDrivenStationary`, `ContinuousTimeJumpDrivenWindowBalance`)
never manipulates densities: it identifies the Gibbs mixture of the actual
`pathLawFrom` laws with a weighted common-reference law, proves that law
reversal-invariant, and extracts the measure-level `WindowBalance` used by the
marked-path Crooks induction.

The headline theorems depend only on the mixture route; the density route is
an independent consistency check that the same physical hypothesis supports
the pointwise strategy.  The two routes share only the balance vocabulary
(`ContinuousTimeJumpDrivenBalance`) and are import-independent of each other.
The shared balance module itself imports only the low-level generator,
counting-chart, and Gibbs modules — not the marked driven-protocol layer — so
the independence claim is visible in the import graph, and full-path reversal
lives in its own low-level module (`ContinuousTimeJumpFullPathReversal`)
usable by both routes.

## Asymmetric two-state one-window recovery

The existing asymmetric chain with rates `q(0,1)=2` and `q(1,0)=1` is packaged
as a `FiniteJumpGenerator`. Its derived generator is identified with the
previous thermodynamic generator, and the original Gibbs detailed-balance
calculation supplies the unique window hypothesis:

```lean
TwoState.AsymmetricExample.physicalFiniteGenerator
TwoState.AsymmetricExample.physicalFiniteGenerator_generator_eq
TwoState.AsymmetricExample.physicalFiniteGenerator_isGibbsDetailedBalance
TwoState.AsymmetricExample.oneWindow_isGibbsDetailedBalance
```

The new endpoint work agrees with the earlier final-quench observable at three
levels: directly on the recorded endpoint, pointwise on a `ConnectedPath`, and
almost surely for the constructed forward window kernel. The general free
energy also reduces to the earlier explicit `-log 2` change.

```lean
TwoState.AsymmetricExample.drivenWork_oneWindow_eq_thermodynamicStateWork
TwoState.AsymmetricExample.connectedDrivenWork_oneWindow_eq_thermodynamicWork
TwoState.AsymmetricExample.forwardWindowKernel_ae_thermodynamicWork
TwoState.AsymmetricExample.drivenDeltaFreeEnergy_oneWindow_eq
```

The public generator-level theorems then yield the one-window physical
statements in the variables of the existing example:

```lean
TwoState.AsymmetricExample.driven_oneWindow_crooks_physical
TwoState.AsymmetricExample.driven_oneWindow_jarzynski_physical
TwoState.AsymmetricExample.integrable_drivenOneWindowWork
TwoState.AsymmetricExample.driven_oneWindow_second_law
```

The generic finite-generator path law and the earlier hand-built asymmetric
path law use different simplex reference charts. Their terminal-state
pushforwards are nevertheless identical: both have singleton masses equal to
the same row of `exp (TQ)`, where the generator identity above identifies the
two matrices.

```lean
TwoState.AsymmetricExample.physicalFiniteGenerator_terminalState_real_singleton_eq_legacy
TwoState.AsymmetricExample.map_physicalFiniteGenerator_pathLawFrom_terminalState_eq_legacy
```

## Deferred extensions

The measure construction intentionally remains on the raw reverse-oriented
marked carrier; `ConnectedPath` supplies a structural view when pointwise
boundary equations are useful. A future extension may package the almost-sure
support theorem as a probability law directly on that subtype.

Another extension may concatenate all window marks into one global real-time
trajectory. General calendar-time-dependent rates and integrated hazards remain
outside this stepwise protocol layer.
