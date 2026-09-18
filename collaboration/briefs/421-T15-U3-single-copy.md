# Lane 421-T15-U3-single-copy — T15 U3: lattice summability + single copy (six fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/421-T15-U3-single-copy` (git branch `erenup/421-T15-U3-single-copy`, based on `origin/erenup/integration-section3`, which contains
`Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement}.lean` — lane 376's `Placement.lean` (`scaledVelocity/Pressure/Force_tsupp_subset`, `_slice_subset_cube`,
`_slice_hasCompactSupport`) and lane 384's canonical raw-field `PlacementData`/`ScalingAPI` in `Scaling.lean`). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U3**
(`:61-67`; targets the six fields `velocity_summable/pressure_summable/force_summable` (`research/T15/Spec.lean:671,682,693`) and `velocity_singleCopy/pressure_singleCopy/force_singleCopy`
(`:704,715,726`) — read their canonical spellings in `Section3/T15/Scaling.lean`), `research/T15/REPORT_376.md`, `REPORT_384.md`, the periodization lemmas
`Section3/T13/ConstantEndpoints.lean:308 eq_zero_of_mem_cube`, `:332 periodize_eq_of_mem_cube`, `:349 tsupport_subset_cube` (and the vendor `periodize_locally_eq_sum`/`periodize_add_lattice`
via lane 362's `Bridges.lean`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder `Prop` fields; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only (except the registry/work-items additions named below).
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T15/SingleCopy.lean` (namespace `NSFormalization.Section3.T15`): the six canonical fields verbatim (types literally equal to the
`ScalingAPI` fields — probe by `exact`), over the raw-field `PlacementData` hypotheses of lane 384: each rescaled slice is supported in `interior fundamentalCube` (Placement, lane 376),
so the lattice sum defining the periodization is summable (only the `n = 0` term is nonzero on the cube, finitely many terms nonzero at any point) and equals the single copy on the
cube. Deliverables: the module, `research/T15/probes/single_copy_closes.lean` (six `exact` checks against the `ScalingAPI` fields + the concrete geometric instance of
`research/T15/probes/placement_closes.lean` fired at an active time), `research/T15/axioms_u3.lean`, `research/T15/ATTEMPTS_U3.md`, U3 status line in `T15_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.SingleCopy` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_421.md`.
