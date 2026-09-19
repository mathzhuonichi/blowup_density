# Lane 448-T21-SPLIT-plan — T21 proof-lane split (`cor:nondensity` + `thm:main`): `research/T21/T21_SPLIT.md`

**Incremental-output rule (lead, 2026-09-19 15:05Z — added after two sessions died in `Reconnecting` loops with nothing on disk):** within the first 5 minutes write a skeleton of the split file (unit list with one-line targets) and `git commit` it; then refine section by section and commit after each section. A session death must leave the partial split on disk. Do not spend more than ~15 minutes reading before the first commit.

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **planning** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/448-T21-SPLIT-plan` (git branch `erenup/448-T21-SPLIT-plan`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md`, the reconciled statement
`research/T21/Spec.lean` (`NonDensityAPI` 9 fields, `MainTheoremAPI` 5 fields, the two `…Statement` defs, the assembly signatures `nonDensityOfCritical`/`mainOfDensityAndNonDensity`/`mainOfInputs`),
`research/T21/RECONCILIATION.md` (§0 lead approval, §1 clause tables, §2 base/threading, §3 owner questions, **§4 the sixteen proof units N0–N15 with suppliers**, §5 next steps), the paper
`paper/sections/03-torus.tex:1-16` and `:506-525`, the consumed canonical records `Section3/T20/CriticalRegularity.lean` (`CriticalRegularityTAPI`; its fields are being proved — U1–U11 landed,
U12 lane 441 in flight, U13 assembly/registration next) and `research/T19/Spec.lean` (`PeriodicDensityAPI`; T19 U1–U6 proved in `Section3/T19/Bookkeeping.lean`, U7–U14 blocked on T18 U12),
the registered `Contracts/V1/TorusLocalTheory.lean` (`RelativelyDenseT`, `forceClassT`, `forceSobolevENormT`, `maximalLifespanT`) and `Bindings/TorusLocalTheory.lean` (`maximalLifespanT_eq`),
the Section 4 twin `Section4/R41/*.lean` (`NonDensityL1.lean` is the line-by-line template for N7–N10, N14, N15; `lowerVectorL` for N3) and `Contracts/V1/MainThresholds.lean`, the existing
torus pieces `Paper1/PeriodicCriticalRegularity.lean` (`critical_regular_ball:81`, `paper1_main_with_critical_interfaces:99`) and `Paper1/PeriodicMain.lean:59`, and the house-style split documents
`research/T18/T18_SPLIT.md` (header, §0 ground rules incl. the peeling rule, unit format "**Uk — name** (kind). New module. Targets (verbatim, Spec line). Route. **Size, model.** Deps."),
`research/T20/T20_SPLIT.md` (waves table, risks section).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- This is a **planning** lane: no Lean proofs, no placeholder fields, no edits to existing modules. Every claim "X is in the tree" must be verified by `grep -rn`/`sed -n` and cited with file:line; every claim "X is missing" must show the grep that returned nothing. Read the paper lines you cite with `sed -n`.

## Deliverable
`research/T21/T21_SPLIT.md`: the T21 proof-lane split in house style — header (target, design, twin, house style, size legend, model legend **codex-sol = bookkeeping/transport, codex-astra = analytic
core/planning** (no Opus)); §0 ground rules (peeling rule; T21 has no named inputs: everything is threaded from `CriticalRegularityTAPI`/`PeriodicDensityAPI` or registered); §1 units — one per
N0–N15 grouped sensibly into lanes of S/M size (e.g. N4+N5+N12 "zero force/zero datum bookkeeping", N1+N2 "datum order-lowering + sliceSobolevMonotone", N3 "forceSobolevMonotone via a
`PeriodicSobolev t →L[ℝ] PeriodicSobolev s` contraction (torus `lowerVectorL`; check lane 428's `critLower` in `Section3/T20/YBound.lean` — grep — as a ready-made pattern)", N6 "triangle
inequality for `forceSobolevENormT 1 s` (also needed by T18 U11, lane 445 — coordinate: whichever lands first is reused)", N7–N10 "ball bookkeeping + nonDensity", N0+N8+N9 "the T20 bridge and
disjointness", N11+N13+N14+N15 "MainTheoremAPI assembly", plus a final "assembly + `Nonempty` statements + contract/bindings/tests" unit gated on the T19 and T20 registrations) with for each unit:
exact target field(s) with `Spec.lean` line, the route with **verified** file:line citations, size, model, deps; §2 a dependency ledger table (unit → registered/threaded input it consumes); §3 waves
(≤ 3 concurrent, what can start now: everything not needing T20 U13 or T19 U7+); §4 risks (the `Prop`-vs-`Type` owner question; registration order T19 → T20 → T21 and where the
`maximalLifespanT_eq` bridge lives after registration; the `ballRelativelyOpen` N6 cost). Commit on your branch. Report in four parts (what the split decides / files / open questions / commands); write
it to `research/T21/REPORT_448.md`.
