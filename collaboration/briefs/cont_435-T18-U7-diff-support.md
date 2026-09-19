# Lane 435-T18-U7-diff-support — codex-sol continuation after an astra scaffold

The codex run of this lane (see `research/T18/REPORT_435.md`, `ATTEMPTS_U7.md`, commit `400e8e7e` "WIP scaffold") delivered only `diffSupportRadius` and its positivity and declared the two
support theorems blocked because "`PlacementData` lacks the carrier radius `R_K`" and "no packet-support bridge for `periodizedScaledVelocity`". Treat both claims as unverified — likely wrong:
(1) the packet carrier `K` is compact (`PlacementData.carrier_compact`/`carrier_subset` — read the raw-field record in `Section3/T15/Scaling.lean`), so a radius `R_K` with `K ⊆ closedBall 0 R_K`
exists (`IsCompact.isBounded` + `Metric.isBounded_iff_subset_closedBall`) and can be *defined* by `Classical.choose`, or read off the record's own ball (`eps_space`: `ε·θR < r`, `chartBall_in_cube`);
choose `diffSupportRadius` accordingly (any explicit positive radius that makes the Spec field true is acceptable — the Spec field `diffSupportRadius : ℝ` is data); (2) the support of a slice of
`periodizedScaledVelocity` is the periodic set of the single-copy support — lane 421's `velocity_singleCopy`/summability (`Section3/T15/SingleCopy.lean`), lane 376's `scaledVelocity_tsupp_subset`
(`Placement.lean`) and lane 425's `latticeLift_spaceSupport` (`Section3/T17/ForceSupport.lean`) are the bridges. Rebuild the T18 closure first (`lake build NSFormalization.Section3.T18.Momentum`),
then finish U7 per the original brief below: `velocityDifference_support` and `diffSupport_in_chart` with the exact Spec types under `InsertionData` projections, the probe, the axioms file,
truthful `ATTEMPTS_U7.md`/`REPORT_435.md` (keep the codex text under a "superseded" heading), U7 status in `T18_SPLIT.md`. Commit on the same branch `erenup/435-T18-U7-diff-support`.

---

# Lane 435-T18-U7-diff-support — T18 U7: localization of the velocity difference (clause (iii))

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/435-T18-U7-diff-support` (git branch `erenup/435-T18-U7-diff-support`, = lane 433's branch + `origin/erenup/integration-section3`: the T18 layer
`Section3/T18/{Insertion,ForceClass,Kinematics,Divergence,CrossTransport,Momentum}.lean` (U1–U6), the canonical T15 `ScalingAPI` (`Section3/T15/Scaling.lean`: `velocity_singleCopy`, placement fields
`eps_space`, `chartBall_in_cube`), the canonical T17 `CorrectionAPI` (`correction_support`, `θRadius`), `Section3/T16/LatticeLift.lean` (`latticeLift_sliceSupport :275`, `periodicSet`), lane 425's
`Section3/T17/ForceSupport.lean` (`latticeLift_spaceSupport`)). Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0 and unit U7** (`:119-127`; note: the single-ball form is FALSE for a periodic
difference — keep `periodicSet`), the Spec fields `research/T18/Spec.lean:1863` (`diffSupportRadius`), `:1865` (`diffSupportRadius_pos`), `:1873` (`velocityDifference_support`), `:1880`
(`diffSupport_in_chart`), `research/T18/RECONCILIATION.md` §"False clauses", `research/T18/REPORT_{422,426,433}.md` and the probes `research/T18/probes/{insertion_closes,u2_u4_closes,u5_u6_closes}.lean`
(the `InsertionData` conventions), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** — every fact comes from a threaded record field, the registered T11/T12 contracts, or the T18 U1–U6 layer. An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T18/Support.lean` (namespace `NSFormalization.Section3.T18`): `def diffSupportRadius (data : InsertionData) : ℝ := max data.D.θRadius R_K`
(`R_K` = the packet-carrier radius available in `PlacementData`/`ScalingAPI` — read what the records provide and use that), `diffSupportRadius_pos`, `velocityDifference_support` (each spatial
slice of `u_ε − v = w_ε + U_ε` has `tsupport ⊆ periodicSet (Metric.ball data.place.x₀ (ε · diffSupportRadius data))` — exact Spec form under `InsertionData` projections) and
`diffSupport_in_chart` (the ball sits inside the chart / cube: `place.eps_space`, `chartBall_in_cube`). Route: `w_ε` is a lattice lift of the single-copy correction supported in the ball of radius
`ε·θR` (`correction_support` + `latticeLift_sliceSupport`/`latticeLift_spaceSupport`), `U_ε` is the periodized packet whose single copy lives in the ball of radius `ε·R_K` (`velocity_singleCopy` +
placement); the sum's support is in the union, hence in the periodic set of the larger ball; `tsupport` of a sum ⊆ union of tsupports (`tsupport_add`-type lemma, `closure` monotone; the periodic set of
an open ball may not be closed — use the closed ball or prove closedness as lane 431 did with the closed-ball trick, whichever the Spec spelling requires — read it exactly). Deliverables: the module,
`research/T18/probes/u7_closes.lean` (Spec-form fields via the U1 conversions), `research/T18/axioms_u7.lean`, `research/T18/ATTEMPTS_U7.md`, U7 status line in `T18_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Support` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T18/REPORT_435.md`.
