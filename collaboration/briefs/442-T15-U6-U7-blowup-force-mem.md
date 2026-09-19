# Lane 442-T15-U6-U7-blowup-force-mem — T15 U6 `unboundedSpeed` + U7 `force_mem` (canonical `ScalingAPI` fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/442-T15-U6-U7-blowup-force-mem` (git branch `erenup/442-T15-U6-U7-blowup-force-mem`, based on `origin/erenup/integration-section3`:
`Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement,SingleCopy}.lean` — lane 384's raw-field `PlacementData`/`ScalingAPI` (`Scaling.lean:106` structure, fields `:286` `force_mem`,
`:329` `unboundedSpeed`), lane 376's placement (`scaledVelocity/Pressure/Force_tsupp_subset`, `_slice_subset_cube`, `_slice_hasCompactSupport`), lane 421's `velocity/pressure/force_singleCopy` +
summability and the four generic lattice lemmas). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0, unit U6 (`:112-116`) and unit U7 (`:118-123`)**, `research/T15/REPORT_{376,384,421}.md`, the
Section 4 suppliers `verification/Bindings/Scaling.lean:110 scaled_blowup` (SpeedUnboundedAt for the ℝ³ `scaledPacket` — but `formalization/` cannot import `Bindings`: find the canonical
`Section4/I03`/`Source` theorem it wraps, `grep -rn "scaled_blowup\|SpeedUnboundedAt" formalization/NSFormalization/Section4 formalization/NSFormalization/Source`), `T10/ForcePaths.lean:395`
(`memForceT_time_smul` pattern for the positive-time support witness), the vendor `contDiff_periodize` / `periodize_add_lattice` (through lane 362's `Bridges.lean`), the definitions
`SpeedUnboundedAt` and `MemForceT` (registered spellings; read them), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
Two new modules (namespace `NSFormalization.Section3.T15`): `Section3/T15/Blowup.lean` — `theorem unboundedSpeed` with type literally the `ScalingAPI` field (`∀ ε ∈ Ioc 0 place.ε₀, SpeedUnboundedAt
place.T (periodizedScaledVelocity u place.x₀ place.T ε)`) under the raw packet clauses actually needed (the packet's own `SpeedUnboundedAtOne u` clause and the placement); route: the ℝ³ scaled packet
blows up at `place.T` (source-time-1 witnesses mapped through the parabolic rescaling, `place.eps_time` for `ε² ≤ T`), U3's single copy identifies the periodized field with the scaled field on the
cube, so witnesses `t ↑ T`, `x ∈ Q` transfer. `Section3/T15/ForceMem.lean` — `theorem force_mem` (`∀ ε ∈ Ioc 0 place.ε₀, MemForceT (periodizedScaledForce f place.x₀ place.T ε)`): smoothness from
`contDiff_periodize` (compact single copy inside the cube), unit periodicity from `periodize_add_lattice`, compact positive-time support from the packet's `CompactPositiveTimeSupport f` transported by
the rescaling (support in `(T − 2ε², T + 2ε²)`-type window with `t > 0` from `eps_time`). Deliverables: the two modules, `research/T15/probes/blowup_force_mem_closes.lean` (both fields by `exact`
against the `ScalingAPI` field types + the concrete geometric instance of `research/T15/probes/energy_mixed_closes.lean`/`placement_closes.lean` if it applies), `research/T15/axioms_u6_u7.lean`,
`research/T15/ATTEMPTS_U6_U7.md`, status lines for U6/U7 in `T15_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Blowup NSFormalization.Section3.T15.ForceMem` (0 errors), `lake env lean` on each module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_442.md`.
