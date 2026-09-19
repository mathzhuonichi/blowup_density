# Lane 466-T19-U10-U11-U12-projection — T19 wave 4: `extendedProductDensity` (U10), `projectionOntoInitialData` (U11), `zeroInitialProjection` (U12)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/466-T19-U10-U11-U12-projection` (git branch `erenup/466-T19-U10-U11-U12-projection`, = `origin/erenup/integration-section3` after lane 464 (T19 U7–U9) merged).
Read `CLAUDE.md`, **`research/T19/T19_SPLIT.md`** (§0; wave 4 units U10/U11/U12 verbatim targets and routes), `research/T19/REPORT_464.md` + `Section3/T19/DensityEngine.lean` (`fixedInitialDensity`), `Section3/T19/Density.lean`
(`ProjectionAPI.extendedProductDensity`, `.projectionOntoInitialData`, `.zeroInitialProjection`; `extendedBreakdownSetT` — read the exact definitions/statements), `verification/Contracts/V1/TorusLocalTheory.lean` (`RelativelyDenseT`, `breakdownSetT`,
`forceClassT`, `initialClassT`; grep `zero_mem_forceClassT` / `zero_mem_initialClassT` analogues in `Section3/T10`/`T11` and `Bindings/DensityFromInsertion.lean:57`), the R³ templates `PeriodicDensityFiber.lean` / `PeriodicDense.lean` cited in
`T19_SPLIT.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T19.DensityEngine`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T19/Projection.lean` (namespace `NSFormalization.Section3.T19`): the three theorems with the canonical fields' types (probe by `exact`). U10: apply `fixedInitialDensity` at `(a, ν, T, s)`, unfold
`RelativelyDenseT` on `g, r`, repackage `f ∈ 𝓕 ∧ maximalLifespanT ν a f ≤ ofReal T` (+ `a ∈ 𝓧`) as `(a, f) ∈ extendedBreakdownSetT ν T`. U11: `Set.ext`; `⊆` from the membership's `a ∈ initialClassT` component; `⊇` via U10 with the zero force (prove
`(0 : SpaceTimeField) ∈ forceClassT` if not in the tree — smooth, periodic, compactly supported in positive time: check the exact `forceClassT` definition; if the zero force is *not* in `forceClassT` because of a nonzero-support clause, use any
registered nonzero member instead, e.g. the T14 packet force through `Bindings.packetImportFamily`) and any `r > 0`, `s < 1/2`. U12: `⊆` as in U11 restricted to `a = 0` (show `(fun _ => 0) ∈ initialClassT`), `⊇`: U10 at `a = fun _ => 0`.
Deliverables: the module, `research/T19/probes/projection_closes.lean` (three fields by `exact`), `research/T19/axioms_u10_u12.lean`, `research/T19/ATTEMPTS_U10_U12.md`, status lines in `T19_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Projection` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T19/REPORT_466.md`.
