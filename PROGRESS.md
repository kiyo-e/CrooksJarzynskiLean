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
## M2 — DONE (2025) — `ContinuousTimeJumpDrivenEndpointExp.lean`
- `Markov.reversedForwardPathMeasure_ofFn_rev` (discrete stemma) fully proved.
- `ContinuousTimeJump.Driven.forwardDrivenLaw_endpointCylinder_eq_exp_product`
  proved. The final real/ENNReal block:
  - `rw [ENNReal.toReal_mul]` after the discrete lemma;
  - per-factor `hfact` via `rw [← Measure.real_def]` + `exact
    FiniteJumpGenerator.transitionKernel_real_singleton_eq_exp_generator`;
  - the `∏`-`toReal` inside the product via `rw [ENNReal.toReal_prod (Finset.univ)]`;
  - closing the commuted product by `rw [mul_comm]` (ring/ring_nf both fail: ring
    needs cancellation, ring_nf reduces to a `∨` disjunction — avoid them).
- Key gotcha: `simp only [Measure.real_def, transitionKernel_real_singleton_eq_exp_generator]`
  on the whole goal errors "function expected / NormedSpace.exp"; do the
  `.toReal → .real` fold per-factor with explicit `rw [← Measure.real_def]`.

## M3 — DONE — three-state two-window: work is not a function of the endpoints
- `work_zero_same_endpoints_event_pos` / `work_log_two_same_endpoints_event_pos`:
  positive measure of `twoWindowEvent 0 0 0` / `twoWindowEvent 0 1 0` (+ pinned
  endpoints `(0,0)` and work `0` / `log 2`).
- `ae_endpoint_pair_value` (private helper): an a.e. equality restricted to a
  positive pinned event forces the value at the pinned endpoints; uses
  `ae_iff` + `MeasureTheory.nonempty_of_measure_ne_zero` + `measure_sdiff_null'`.
- `work_not_ae_initialFinalFunction`: no `f : Fin 3 → Fin 3 → ℝ` reproduces
  `work energy` a.e. from `(startpointAt γ 0, endpointAt γ (Fin.last 1))`
  (both events pin `(0,0)`, work `0` vs `log 2` → contradiction).
- `work_not_ae_finalStateFunction`: same obstruction for final-state-only `f`.
- Gotchas: `Driven.startpointAt`/`endpointAt` unfold to `Fin.lastCases`; rewrite
  the numeral index to `(0:Fin 1).castSucc` / `Fin.last 0` explicitly before
  applying the `[simp]` fold lemmas; the `change` on the carrier needs the
  explicit `: Marked.MarkedPath (Fin 3) (FullPath (Fin 3)) 2` type annotation
  (the bare tuple misfires the continuation/pair unification).
- Root module `lake build CrooksJarzynski` green (8731 jobs).
