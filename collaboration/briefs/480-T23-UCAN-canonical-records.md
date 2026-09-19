# Lane 480-T23-UCAN-canonical-records — T23 U-CAN: one canonical module for the reconciled T23 records (`DomainPlacementData` 16, `CutoffData` 7, `ClassicalSolutionOmega` + domain classes, `BoundaryInsertionAPI` 48) and the repaired statement

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/480-T23-UCAN-canonical-records` (git branch `erenup/480-T23-UCAN-canonical-records`, = `origin/erenup/integration-section3` after lanes 476 (U1), 477 (U2 partial) and 478 (U7) merged). Three parallel lanes each restated a piece of the T23 vocabulary:
`Section3/T23/Placement.lean` (476: `DomainPlacementData`, `domainPlacementData`, `interiorBall_in_domain`), `Section3/T23/LocalCorrection.lean` + `SpatialExtension.lean` + `LocalCorrectionBridge.lean` + `StatementRepair.lean` (477: `CutoffData`, `localCorrectionData`, `LocalCorrection…` record, cross transports, `zeroCutoff` G0 obstruction), `Section3/T23/NoSlipUniqueness.lean` + `BoxIntegration.lean` (478:
`ClassicalSolutionOmega`, `IsBoundedBoxOrSmoothDomain`, `IsBoxDomain`, `IsRegularLevelDomain`, `initialClassOmega`, `forceClassOmega`, `SmoothOnClosedSlab`, …). Read `CLAUDE.md`, **`research/T23/T23_SPLIT.md`** (§0 "consume versus thread", §1 field ownership incl. U9's list, §4), **`research/T23/SPEC_ISSUES.md`** (G0 ruling + lane 477 addendum with the exact literal/repaired statements; G1), `research/T23/Spec.lean` (the 48-field
`BoundaryInsertionAPI`, `boundaryInsertionStatement :1037-1050`, all records/classes with docstrings), `research/T23/RECONCILIATION.md`, the three lanes' reports `research/T23/REPORT_{476,477,478}.md`, how T18/T24 did it (`Section3/T18/Insertion.lean` raw-field `InsertionData`; `Section3/T24/Multiple.lean`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first (`lake build` of the seven T23 modules above).
- No `sorry`/`admit`/`axiom`/`native_decide`. **Existing modules may be edited only to remove a duplicate definition in favour of the canonical one** (record every such edit in `ATTEMPTS_UCAN.md`; keep every theorem statement of 476/477/478 valid — `rfl`-transparent renames only). Never import `Paper1/BoundaryCorollary.lean`.
- **No placeholders, no `True` fields.** Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Commit incrementally.

## Goal
`Section3/T23/Boundary.lean` (namespace `NSFormalization.Section3.T23`): the canonical `BoundaryInsertionAPI` (48 fields, token-for-token from the Spec over the **raw** packet fields and the records already canonical in 476/477/478 — import them; do not restate), `boundaryInsertionStatement` (literal, as in the Spec) and `boundaryInsertionStatement'` (the repaired existential form from
`SPEC_ISSUES.md` G0 addendum; both as `def … : Prop`), and the probe `research/T23/probes/boundary_api_on_canonical.lean` checking field-by-field agreement with `research/T23/Spec.lean` (as lane 457 did for T19, 467 for T24). Resolve every naming overlap among the three lanes' modules (one `CutoffData`, one `ClassicalSolutionOmega`, one domain-class family). Update `T23_SPLIT.md` §1 with
the final canonical names each later unit (U3–U6, U8, U9) must consume. Deliverables: the module, the probe, `research/T23/axioms_ucan.lean`, `research/T23/ATTEMPTS_UCAN.md`, status line, `research/T23/REPORT_480.md` (four parts).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.Boundary` (0 errors) plus rebuilding the three lanes' modules and probes after any dedupe, `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Lead note (2026-09-19 16:34Z) — reviewer follow-up from lane 476
Also add to `Placement.lean`'s successor (or a small `Section3/T23/Geometry.lean`) the three auxiliary geometry lemmas `T23_SPLIT.md:40` requested and lane 476 skipped: compactness of the prescribed closed ball, a smaller closed ball around `x₀` inside the prescribed ball, and separation of the closed ball from `frontier Ω` under `IsOpen Ω` (explicit premise). Each with a one-line probe.
