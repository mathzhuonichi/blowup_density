# Lane 255-I03-path-measurability — close lane 250's single named input `CompactHomogeneousRealization`: D01's `compactHomogeneousPath` of a smooth compactly supported force is a.e. strongly measurable for `Data.forceTimeMeasure` (order `-3/2 < s < 0`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/255-I03-path-measurability` (git branch `erenup/255-I03-path-measurability`, based on lane 250's branch `erenup/250-I03-homogeneous-scaling` =
`origin/erenup/integration` + `formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean` + `verification/Bindings/ScalingHomogeneous.lean` (36 declarations; **read both fully**, especially the
definition of the named input `CompactHomogeneousRealization` (grep it), the theorems that consume it (`packetNegativeHomogeneous`/`correctionNegativeHomogeneous` bindings), and
`research/I03/REPORT_250.md` §3 + `research/I03/ATTEMPTS_HOMOGENEOUS.md` (what was tried for the measurability and why it was isolated)). Then the D01 path machinery: `compactHomogeneousPath`
(grep `Section4/D01/` — its definition, presumably `t ↦ the homogeneous datum of the slice f(t,·)` via the Bessel-to-homogeneous conversion or the angular realization), lane 221's
`Section4/R43/ForcePath.lean` (**template**: it proved the canonical order-`1/2` homogeneous force path of a `MemForceR` force is `MemLp` of order one and **strongly measurable for the
positive-time measure** — `grep -n "AEStronglyMeasurable\|aestronglyMeasurable\|Continuous" Section4/R43/ForcePath.lean`), `Section4/D01/HalfOrder.lean:140-180` (the `AEStronglyMeasurable G forceTimeMeasure`
clause inside `forceSobolevENorm`/`forceHomogeneousENorm`'s infimum and how `forceSobolevENormL1 (1/2) f ≠ ⊤` exhibits a measurable path), `Contracts/V1/Data.lean:375-410` (`IsHomogeneousPath`,
`forceHomogeneousENorm`, `forceTimeMeasure`), lane 216/219's `R43/CriticalDatumPath.lean`/`CriticalMomentum.lean` (the conversion is a continuous linear map for `s ≥ 0`; for `s < 0` lane 250
has its own realization — see how it is built), `CLAUDE.md`, `collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules (250's files are on your base but unmerged — do not edit them);
  new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s.
- **Satisfiability rule:** if a step resists, isolate ONE named hypothesis with the exact statement.

## Goal
1. `compactHomogeneousPath_continuous` (or `_aestronglyMeasurable`): for `MemForceCompact f` (smooth, compact spacetime support) and `-3/2 < s < 0`, the path `t ↦ compactHomogeneousPath f s t`
   into `RealVectorSobolev s` is continuous on `[0,∞)` (the slices' jets are continuous in time in `L²` with uniformly compact support; the homogeneous datum depends continuously on the slice —
   through whatever realization lane 250 uses; for `s < 0` the map slice ↦ `|ξ|^s f̂` needs the low-frequency integrability `-3/2 < s`, which `HomogeneousPartial`'s `lowFrequencyIntegrable`
   provides), hence `AEStronglyMeasurable … Data.forceTimeMeasure`.
2. `compactHomogeneousRealization : CompactHomogeneousRealization` (the exact named input) and the two I03 fields unconditional: `packetNegativeHomogeneous'`, `correctionNegativeHomogeneous'`
   (lane 250's theorems with the input discharged; state them in `research/I03/Spec.lean`'s exact shapes).
3. Audit `research/I03/axioms_path_measurability.lean`; records `research/I03/ATTEMPTS_MEASURABILITY.md`; update `research/I03/COMPARISON.md` rows 46/48 (closed).

## Deliverables
New module `formalization/NSFormalization/Section4/I03/PathMeasurability.lean` and/or `verification/Bindings/ScalingHomogeneousClosed.lean` (whichever layer the statements need; say why).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build <modules>` (silent), `lake env lean` on each (0 output), the audit, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/I03/REPORT_255.md`.
