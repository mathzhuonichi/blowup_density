# Lane 425-T17-U7-force-support — T17 U7: `force_smooth` / `force_periodic` / `force_support` of the periodized correction force (canonical fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/425-T17-U7-force-support` (git branch `erenup/425-T17-U7-force-support`, based on `origin/erenup/integration-section3`, which contains
`Section3/T17/{CorrectionProfile,Transport,LatticeDeriv,CorrectionDeriv,ForceDeriv,ForceProfile,Correction}.lean` — lane 373's `Transport.force_eq` (periodized correction force = lattice
lift of the single-copy chart force), lane 394's canonical 45-field `CorrectionAPI` (`Correction.lean`, over lane 384's raw-field `PlacementData`), lane 375/412's `ForceProfile.lean`
(`force_profile_smooth`, `force_profile_support`, `force_eq_chart`, `force_profile_identity`), and `Section3/T16/{LatticeLift,Assembly}.lean` (`latticeLift_smooth :116`, `latticeLift_periodic :124`,
`latticeLift_timeSupport :247`, `latticeLift_sliceSupport :271` — verify the line numbers)). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U7** (`:186-192`), the canonical fields
`force_smooth`/`force_periodic`/`force_support` in `Section3/T17/Correction.lean` (grep; Spec form `research/T17/Spec.lean:836-852`: `ContDiff ℝ ∞ (correctionForce ν v D ε)`,
`IsPeriodicOn univ (correctionForce ν v D ε)`, `tsupport (correctionForce ν v D ε) ⊆ Ioo (T − 2ε²) (T + 2ε²) ×ˢ periodicSet (ball x₀ (ε·θRadius))` — **open** ball, read the exact canonical
spelling), `research/T17/SPEC_ISSUES.md` (G1: the Paper1 profile lemmas need global `ContDiff ℝ ∞ v`; the canonical record has only `reference_periodic`, so these three fields are proved
under the explicit `hv : ContDiff ℝ ∞ v` premise exactly as U3–U6 were — state it), `research/T17/REPORT_{373,375,394,412}.md`, `research/T17/ATTEMPTS_UCAN.md`, the Paper1 suppliers
`Paper1/CorrectionVectorNorms.lean` (`physicalForce_smooth :22`, `physicalForce_compact :37`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** The only extra premise allowed is the documented G1 `hv : ContDiff ℝ ∞ v` (say where it is used). An honest partial with the exact
  residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T17/ForceSupport.lean` (namespace `NSFormalization.Section3.T17`): the three theorems `force_smooth`, `force_periodic`, `force_support`
with types literally the canonical `CorrectionAPI` fields at the concrete `correctionData` (probe by `exact`, as `research/T17/probes/correction_canonical.lean` does for U3–U6), for
`ε ∈ Ioc 0 D.ε₀`. Route: `Transport.force_eq` writes `correctionForce ν v D ε` as the lattice lift of the single-copy chart force; smoothness from `physicalForce_smooth` + `latticeLift_smooth`
(a lattice lift of a smooth function with compact spatial support inside one cell is smooth — check the exact hypotheses); periodicity from `latticeLift_periodic`; support from
`physicalForce_compact` (support in `Ioo (T − 2ε²) (T + 2ε²) × ball x₀ (ε·θRadius)`) transported by `latticeLift_timeSupport`/`latticeLift_sliceSupport` to the periodic set of the open ball.
If the T16 lattice-lift support lemma yields a closed ball, prove the open-ball form from the compact-support-inside-the-open-ball fact (do not weaken the field). Deliverables: the module,
`research/T17/probes/force_support_closes.lean` (the three canonical fields closed by `exact` at concrete data; instantiate at the non-vacuity witness of `research/T17/probes/rev394_nonvacuity.lean`
if applicable), `research/T17/axioms_u7.lean`, `research/T17/ATTEMPTS_U7.md`, U7 status line in `T17_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.ForceSupport` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and where `hv` enters / files / gaps with error text / commands and results). Try `research/T17/REPORT_425.md`;
if the report-file guard blocks it, put the full report in your final message.
