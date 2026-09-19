# Lane 483-T23-U4-differences-boundary — T23 U4: localized differences and boundary retention (8 API fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/483-T23-U4-differences-boundary` (git branch `erenup/483-T23-U4-differences-boundary`, = lane 480's branch (T23 U-CAN, in review) + `origin/erenup/integration-section3` with 476/477/478 merged). Read `CLAUDE.md`, **`research/T23/T23_SPLIT.md`** (§0; your unit verbatim; §2; §4), `research/T23/SPEC_ISSUES.md` (G0, G1), `research/T23/Spec.lean` (the exact field statements), `Section3/T23/Boundary.lean` (lane 480: canonical `BoundaryInsertionAPI` 48 fields, `boundaryInsertionStatement`/`'`, geometry lemmas), `Placement.lean` (476), `LocalCorrection.lean` + `SpatialExtension.lean` + `LocalCorrectionBridge.lean` + `StatementRepair.lean` (477), `DomainSolution.lean` + `NoSlipEnergy.lean` + `DifferenceEnergy.lean` + `BoxIntegration.lean` (478), `research/T23/REPORT_{476,477,478b,480}.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first (`lake build NSFormalization.Section3.T23.Boundary` and the modules you consume).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only under `formalization/NSFormalization/Section3/T23/` (your own module names below) and `research/T23/`. Never import `Paper1/BoundaryCorollary.lean`.
- **Parallel lanes**: U2b (481), U3 (482), U4 (483), U5 (484), U6 (485), U8 (486) run at the same time on the same base. Do not create another lane's module; where you need another lane's result, **thread it as an explicit hypothesis** (state your theorems over the needed fields/facts as parameters, exactly as the T21 lanes 472/474 did) — the assembly lane (U9) discharges them. Never restate a record that `Section3/T23/Boundary.lean`, `Placement.lean`, `LocalCorrection.lean` or `DomainSolution.lean` already provides.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file. **Commit a module skeleton within 15 minutes and after each closed lemma.**

## Goal
Exactly `T23_SPLIT.md` U4: `collar_agreement`, `noSlip_preserved`, `velocityDifference_divFree`, `diffSupportRadius`/`_pos`, `velocityDifference_support`, `diffSupport_in_chart`, `forceDifference_spatialSupport` — with `ρ` strictly larger than the cutoff and packet carrier radii, `tsupport` of the sum bounded by the union, `ε` shrunk so `ball x₀ (ερ) ⊆ B`; I02 support fields as cited in U2 (through lane 477's modules) and the scaled carrier from I03 `carrier_subset`; force support at all real times (after `T` too) via the correction-force support and the scaled force support; `tsupport (zeroExtension Ω (fε(t) − g(t))) ⊆ closure B` by closedness. Thread the U3 formulas (`velocity = v + w + scaledPacket`, …) as hypotheses on abstract fields rather than importing lane 482.

Deliverables: your module(s) (`Section3/T23/Differences.lean`), a probe `research/T23/probes/T23-U4-differences-boundary_closes.lean` (each field by `exact` against `Boundary.lean`/`Spec.lean`, instantiated at the threaded hypotheses), `research/T23/axioms_T23-U4-differences-boundary.lean`, `research/T23/ATTEMPTS_T23-U4-differences-boundary.md`, status line in `T23_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build <each new module>` (0 errors), `lake env lean` on each (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T23/REPORT_483.md`.
