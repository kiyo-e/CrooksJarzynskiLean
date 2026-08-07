# Crooks–Jarzynski Lean — Progress Log

## Milestone M1 — Endpoint law (branch `pi/m1-m3-endpoint-law`)
File: `CrooksJarzynski/MeasureProtocolMarkedEndpoints.lean`

### Completed (module builds; `lake build` success)

- `eraseMarksContinuation`, `eraseMarks` — forget transition marks of marked
  continuations / paths.
- `measurable_eraseMarksContinuation`, `measurable_eraseMarks` — measurability
  (both carry `[fun_prop]`).
- `endpointMarginalKernel`, `instIsMarkovKernelEndpointMarginalKernel`.
- `eraseMarks_comp_prependEquiv`, `erase_prod_comm` (`Measure.ext` +
  `map_apply` + `lintegral_congr` + `Kernel.comap_apply`/`map_apply`).
- `instSFiniteReversedForwardPathMeasure`.
- **Main theorem** `map_reversedForwardPathMeasure_eraseMarks`
  `(Marked.reversedForwardPathMeasure initial K).map eraseMarks =
   Markov.reversedForwardPathMeasure initial (fun i => endpointMarginalKernel (K i))`.
  - induction step (`succ n ih`): builds cleanly.
  - base (`zero`, `n = 0`): unblocked via the **annotated-pair trick**.

### Key insight that unblocked the `n = 0` base (universe bug workaround)

The naive erased map `μ.map (fun a => (a, (PUnit.unit : MarkedContinuation Ω Λ 0))).map eraseMarks`
failed to elaborate: Lean's unifier refuses to identify
`Ω × (Continuation (Ω × Λ) 0)` (universe `max u v`, via the semireducible
`Continuation` `def`) with the `PUnit.{max (u+1) (v+1)}` that the pair was
inferred at. This surfaced only **inside** a `(μ.map f).map g` requirement that
`f`'s codomain unfold to `g`'s domain `MarkedPath Ω Λ 0`.

Fix — give the whole pair an explicit type annotation forcing the codomain:

```lean
(fun a : Ω => ((a, (PUnit.unit : MarkedContinuation Ω Λ 0)) : MarkedPath Ω Λ 0))
```

Then `Measurable`/`Measure.map_map measurable_eraseMarks hm` elaborate and
`rw [hgh]` (composition collapse) closes via `rfl`. The trailing Markov-side
rewrite is closed by `exact (Measure.compProd_deterministic measurable_const).symm`.

### Notes
- The `n`-unused linter warning at the top of the file is intentionally benign.
- No `sorry`/`axiom`/`unsafe` anywhere; all exported lemmas have complete proofs.