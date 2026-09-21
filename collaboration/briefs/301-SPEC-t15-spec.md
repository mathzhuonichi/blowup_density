# Lane 301-SPEC-t15-spec — produce the reconciled specification of T15 (scaling at fixed viscosity (`prop:scaling`: placement, single-copy periodization, `eq:packetEscale/Fscale/Hs`)) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/301-SPEC-t15-spec` (git branch `erenup/301-SPEC-t15-spec`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T15/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/291-SPEC-t15-draft-a:research/T15/DraftA.lean`, `git show erenup/291-SPEC-t15-draft-a:research/T15/COMPARISON_A.md`,
`git show erenup/292-SPEC-t15-draft-b:research/T15/DraftB.lean`, `git show erenup/292-SPEC-t15-draft-b:research/T15/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T15/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_291.md`, `REPORT_292.md` copied verbatim from the two branches (provenance).
2. `research/T15/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing the cited paper file and line (`03-torus.tex:<line>`, `02-preliminaries.tex:<line>`) and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T15/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T15/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T15/REPORT_301.md`; commit on your branch.

## T15-specific instructions (binding)
- **Vocabulary**: the T10 data layer is registered — `import Contracts.V1.TorusData` (namespace `BlowupDensity.Contracts.V1.TorusData`) and use its names directly (`IsPeriodicSpatial`, `torusLift`,
  `IsPeriodicDatum` with the integrability conjunct, `periodicSobolevENorm`, `meanT`, …); do **not** copy them. Copy verbatim (T13 copy policy, delimited blocks with source-line markers) only the
  still-unregistered T10 solution-class declarations you use (`IsPeriodicSobolevPath`, `forceSobolevENormT`, `MemForceT`/`forceClassT`, `pressureMeanT`/`PressureGaugeT`/`normalizePressureT`,
  `ClassicalSolutionT`, `energyEssSupT`/`energyGradientT`/`energyENormT`), T14's packet structures, and T13's `LocalizationAPI` (+ the T13 defs it needs) in their own namespaces
  (`BlowupDensity.T10.Draft`, `BlowupDensity.T14.Draft`, `BlowupDensity.T13.Spec` as the reconciliation says). Check every copy that has a registered twin with `example … := rfl`.
- **Structures and fields exactly as `research/T15/RECONCILIATION.md` §3**: `PlacementData` (A's, as a parameter), the explicit `def`s for the rescaled fields and the lattice periodization,
  `SpeedUnboundedAt`, `alphaT`, and the single Type-valued `ScalingAPI {ν} (P : PacketImportAPI ν) (place : PlacementData P)` with the constants (`sobolevConst`, `sobolevConst_pos`) as data
  fields followed by the clauses in the §3 table order (incl. `forceConvergence`; without the dropped `rfl`-true / junk-dischargeable clauses). Mirror `verification/Contracts/V1/Scaling.lean`
  (`I03.scaling`) spellings token-for-token where the reconciliation says so, with `example … := rfl` checks where both sides elaborate.
- **No junk-value traps**: every norm identity/bound is guarded exactly as the reconciliation prescribes (`*_summable`, `*_singleCopy`, `pressureSlice_integrable`, `energySlices_memLp`,
  `mixed_memLp`, `forceSobolev_memLp`); say in each docstring which guard makes the Bochner integrals honest.
- Report the elaboration of `research/T15/Spec.lean` and the `rfl` checks; do not prove anything.
