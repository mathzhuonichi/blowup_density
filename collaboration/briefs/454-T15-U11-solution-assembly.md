# Lane 454-T15-U11-solution-assembly — T15 U11: the `solution` field (one `ClassicalSolutionT ν 0 F_ε place.T` for the periodized fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker in
`/data_8T/ping/blowup_density/.claude/worktrees/454-T15-U11-solution-assembly` (branch `erenup/454-T15-U11-solution-assembly`). On this base: `Section3/T15/Equation.lean` (U8: `periodized_initial`,
`periodized_divergence`, `periodized_momentum`), `Blowup.lean`/`ForceMem.lean` (U6/U7), `Pressure.lean` (U10: `pressureSlice_integrable`, `pressure_gauge`), `SobolevPath.lean` (U9, lane 450:
`periodized_sobolev`, `periodized_pressure_gradient`), `Energy.lean` (U4: `scaledVelocity_slice_contDiff`, `contDiff_periodize_of_subset_interior`), `SingleCopy.lean`, `Placement.lean`,
`Scaling.lean` (the `ScalingAPI.solution` field `:301-305`: `∀ ε ∈ Ioc 0 place.ε₀, ∃ S : ClassicalSolutionT ν 0 (periodizedScaledForce f place.x₀ place.T ε) place.T, S.velocity = periodizedScaledVelocity …
∧ S.pressure = normalizedScaledPressure …`), and `Section3/T10/PeriodicData.lean:265-300` (the 13 fields of `ClassicalSolutionT`: `horizon_pos`, `velocity_smooth`, `pressure_smooth`, `initial`,
`divergence`, `momentum`, `sobolev`, `pressure_gradient`, `velocity_periodic`, `pressure_periodic`, `pressure_gauge`, …). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U11** (`:147-151`),
`research/T15/REPORT_{442,446,447,450}.md` §1 (exact hypotheses and statements of every ingredient), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first.
- No `sorry`/`admit`/`axiom`/`native_decide`; no edits to existing modules; new files only. **No named inputs, no placeholders.** Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T15/Solution.lean` (namespace `NSFormalization.Section3.T15`): `def periodizedSolution … : ClassicalSolutionT ν 0 (periodizedScaledForce …) place.T` built
from the landed pieces (velocity := `periodizedScaledVelocity`, pressure := `normalizedScaledPressure`; `horizon_pos` from `place.eps_time`+`eps_pos`; smoothness/periodicity of the periodized fields on
`Ico 0 T ×ˢ univ` from the single copy + `contDiff_periodize`, `periodize_add_lattice` (the pressure after normalisation: subtracting a smooth-in-time mean — read how `normalizePressureT` is
defined and prove its slab smoothness/periodicity; lane 436's `Section3/T18/Lifespan.lean` has `isPeriodicOn_normalizePressureT`/`pressure_periodic` patterns); `initial`/`divergence`/`momentum` from U8;
`sobolev`/`pressure_gradient` from U9; `pressure_gauge` from U10), and `theorem solution` with type literally the `ScalingAPI.solution` field under the raw packet clauses actually needed (union of the
ingredients' clauses — list it in the report). Deliverables: the module, `research/T15/probes/solution_closes.lean` (field by `exact` + the concrete nonzero PDE packet instance of
`equation_closes.lean`), `research/T15/axioms_u11.lean`, `research/T15/ATTEMPTS_U11.md`, U11 status line in `T15_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Solution` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and the clause list / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_454.md`.
