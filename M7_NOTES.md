# M4 `pi/m4-fullpath-concat` — status notes

Status of the M4 specification on `CrooksJarzynski/ContinuousTimeJumpConcat.lean`
(plus the FullPath section) as of the last commit.

## Done and green (all with no `sorry`/`axiom`, zero warnings)

- **§1 Concatenation accessor library** — `concat`, `concat_fst_castAdd`,
  `concat_fst_natAdd`, `concat_snd_castAdd`, `concat_snd_natAdd`,
  `concat_snd_boundary`, `concat_state_zero`, `concat_state_last`,
  `fin_cast_roundtrip`, `sum_Iio_eq_sum_range`, `concat_snd_range_left/right`,
  `concat_snd_value_at`. Committed `2e74355`.
- **§2 Jump-time arithmetic** — `jumpTimes_concat_left`,
  `jumpTimes_concat_right` (via the four helper lemmas `concat_jump_sum_left`,
  `concat_jump_seam`, `concat_seam_split`, `concat_delta_join`) and
  `totalHoldingTime_concat`. Committed `7457200`.
- **§4 Sectorwise validity** — `isValid_concat` (with positivity and a
  summed-horizon bound) and its helper `concat_holding_pos`. Committed
  `a7eaeca`.
- **§5 Full-path level** — `FullPath.concat` and pointwise measurability
  `measurable_concat` (via the JumpPath-level `measurable_concat_fixed_fst`).
  Committed `c3e53e8`.
- **Partial §3** — `trajectory_concat_zero` (time-zero gluing). Committed
  `2574bbe`.

## Deferred (documented, not implemented)

### §3 Full trajectory gluing (`trajectory_concat_left` / `trajectory_concat_right`)
The general real-time gluing law is not proved.  The obstruction is structural:
`JumpPath.trajectory` is defined by recursion that peels `dropLast` from the
*end* of the path (`trajectory γ t = if jumpTimes γ (last n) ≤ t then γ.1 (last n)
else trajectory (dropLast γ) t`), while a concatenation is split at the seam in
the *middle*.  So `dropLast (concat γ δ)` does not equal `concat (dropLast γ) δ`,
and the prefix/suffix parts of the concatenated trajectory are not reached by a
simple induction matching the two recursions.  A proof would need to establish
that `dropLast^m (concat γ δ)` collapses to a path sharing the prefix states and
jump times of `γ`, then run a strong induction over the remaining jump count,
plus the matching condition `γ.1 (last n) = δ.1 0` for the seam state.
`trajectory_concat_zero` records the `t = 0` case; the general left/right
gluing law is left as a future extension.

### §6 `Driven.concatenateWindows`
Concatenating all window marks of `Driven.Path Ω M` into one global real-time
trajectory is not implemented.  It is an explicit deferred extension in
`DRIVEN_PROTOCOL.md` ("Another extension may concatenate all window marks into
one global real-time trajectory"), and would require iterating the
`JumpPath.concat`/`FullPath.concat` operation over `M` windows while tracking
the boundary-matching of each window's terminal state to the next window's
initial state.  The measure construction intentionally stays on the raw
reverse-oriented marked carrier, so no measure-level concatenation is built.
