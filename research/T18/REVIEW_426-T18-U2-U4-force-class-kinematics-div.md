ACCEPT-WITH-NOTES

## What the lane claims

`REPORT_426.md` claims the nine U2/U3/U4 Spec fields are proved from `InsertionData`, with no extra hypotheses, and that the three modules, probe, axiom audit, and notes are complete. The claimed target statements match the Spec: `force_mem` and `forceDifference_mem` at `research/T18/Spec.lean:1741-1749`, smoothness and initial fields at `:1753-1765`, history and periodicity at `:1780-1790`, and divergence fields at `:1858-1867`.

## What is in Lean

The declarations have the claimed types. The force membership proofs are at [ForceClass.lean](/data_8T/ping/blowup_density/.claude/worktrees/426-T18-U2-U4-force-class-kinematics-div/formalization/NSFormalization/Section3/T18/ForceClass.lean:50) and `:56`; the correction support interval and positivity argument are explicit at `:36-48`. The kinematics declarations are at [Kinematics.lean](/data_8T/ping/blowup_density/.claude/worktrees/426-T18-U2-U4-force-class-kinematics-div/formalization/NSFormalization/Section3/T18/Kinematics.lean:20), `:29`, `:71`, `:77`, and `:84`. The divergence declarations are at [Divergence.lean](/data_8T/ping/blowup_density/.claude/worktrees/426-T18-U2-U4-force-class-kinematics-div/formalization/NSFormalization/Section3/T18/Divergence.lean:26) and `:43`. No silent hypotheses or vacuous interval/zero substitutions were found. The whole Section4 tree was searched for the report's “not in tree” gaps; none are asserted.

## Gaps

No mathematical gap or statement-fidelity defect was found. The required substantive negative mutation was run in `research/T18/probes/rev426_negative.lean`: replacing the history constant `2` by `3` makes the proof fail with `linarith failed to find a contradiction` at line 9, as expected. The probe and axiom file compile, and the 17 audited declarations print exactly `[propext, Classical.choice, Quot.sound]`. Greps found no `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override in the lane modules. One procedural note: the report's `make check` claim is reproducible from the repository root; running `make check` from `verification/` has no such target. Also, the literal command `python3 check_contracts.py ...` from the repository root is invalid because the script is `experiments/check_contracts.py`; `scripts/gates.sh` itself completed its contract check successfully.

## Commands and results

From `verification/`, with `. scripts/lean-env.sh` and `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T18.ForceClass NSFormalization.Section3.T18.Kinematics NSFormalization.Section3.T18.Divergence`: **Build completed successfully (10019 jobs)**.
- `lake env lean` on each of the three modules, the probe, and `research/T18/axioms_u2_u4.lean`: **0 output / pass** (axioms file printed 17 standard-three-axiom lines).
- From the repository root, `make check`: **pass**; `make test-mutations`: **Mutation suite passed** (`extra_axiom`, `weakened_hypothesis` rejected as required).
- `scripts/gates.sh NSFormalization.Section3.T18.ForceClass NSFormalization.Section3.T18.Kinematics NSFormalization.Section3.T18.Divergence`: **gates OK**, including base compatibility and contract checks.
- `git diff --name-only origin/erenup/integration-section3...HEAD`: no existing module modifications were reported.

Verdict: ACCEPT-WITH-NOTES — fix the report/command documentation to say `make check` is run at repository root and use `experiments/check_contracts.py` (or rely on `scripts/gates.sh`).
