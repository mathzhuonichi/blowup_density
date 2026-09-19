# Lane 450-T15-U9-sobolev-path — T15 U9: the periodized velocity's `H^m` datum path (every `m : ℕ`) and `pressure_gradient` for the periodized fields

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/450-T15-U9-sobolev-path` (git branch `erenup/450-T15-U9-sobolev-path`, based on `origin/erenup/integration-section3`: `Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement,SingleCopy,Energy,Mixed}.lean`
— lane 439's `Energy.lean` (`scaledVelocity_slice_contDiff`, `contDiff_periodize_of_subset_interior`, `memLp_torusLift_gradientVector`, `torusLift_congr_cube`) and `Mixed.lean` (§1 chart lemmas, §3
`torusSlicePath`/`continuous_torusSlicePath`); the T10 datum machinery `Section3/T10/ForcePaths.lean:82 continuous_datum_path`, `:280 smooth_homogeneous_datum_one`, `Section3/T10/DatumBasics.lean:129
datum_unique`, `T10.smooth_periodic_datum`, `T10.memLp_torusLift_vector`; T11's `exists_periodicDatum_smooth` and `continuousOn_periodicDatum_path_of_slab` (used by lane 436 for the inserted solution's
`sobolev` field — read `Section3/T18/Lifespan.lean` `sobolev_path`/`pressure_gradient_memLp` for the exact pattern, it is on this base)). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U9**
(`:133-138`), the two `ClassicalSolutionT` fields `sobolev` (`Section3/T10/PeriodicData.lean:287-291`: `∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev m, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T, IsPeriodicDatum m
(velocity slice t) (G t)` — read the exact text) and `pressure_gradient` (`:292-294`), `research/T15/REPORT_{421,439}.md`, `research/T18/REPORT_436.md` §1 (route change: slab-smooth unit-periodic
slices already carry a datum at every order + a continuous selected path), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T15/SobolevPath.lean` (namespace `NSFormalization.Section3.T15`): over the raw packet clauses of `scalingStatement` (smoothness of `zeroPastField u/p`
on `Iio 1 ×ˢ univ`, compact carrier) and `place : PlacementData u p f K`, for `ε ∈ Ioc 0 place.ε₀`: `periodized_sobolev` — the `sobolev` field of `ClassicalSolutionT ν 0 (periodizedScaledForce …) place.T`
for `velocity := periodizedScaledVelocity u place.x₀ place.T ε` (exact field type with that velocity substituted), and `periodized_pressure_gradient` — the `pressure_gradient` field for
`pressure := normalizedScaledPressure p place.x₀ place.T ε`. Route: the periodized velocity is smooth on the slab `Iio place.T ×ˢ univ` (or on a neighbourhood of every `t < T`: source time `< 1`)
and unit-periodic (single copy in the cube + `contDiff_periodize`), so T11's slab theorems give a datum at every order and a continuous selected path on `Ico 0 T` — the same two calls lane 436
made (`exists_periodicDatum_smooth`, `continuousOn_periodicDatum_path_of_slab`); `pressure_gradient` by `T10.memLp_torusLift_vector` on the continuous slice gradient. Deliverables: the module,
`research/T15/probes/sobolev_path_closes.lean` (both fields instantiated on the concrete nonzero packet of `research/T15/probes/energy_mixed_closes.lean`), `research/T15/axioms_u9.lean`,
`research/T15/ATTEMPTS_U9.md`, U9 status line in `T15_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.SobolevPath` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_450.md`.
