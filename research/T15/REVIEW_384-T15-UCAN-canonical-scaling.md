ACCEPT-WITH-NOTES

## what the lane claims

The worker claims a raw-field restatement of the T15 `PlacementData` and `ScalingAPI`, plus `scalingStatement`, fieldwise Spec/canonical conversions, and the standard axiom footprint.  The cited source block is `research/T15/Spec.lean:560-924`; the implementation declarations are `formalization/NSFormalization/Section3/T15/Scaling.lean:106-189` and `:201-457`, with `scalingStatement` at `:459-509`.

## what is in Lean

The implementation has 17 placement fields and 21 scaling fields, and the raw hypotheses in `scalingStatement` include the packet and both energy clauses (`Scaling.lean:459-509`).  The mapping table is explicit in `research/T15/ATTEMPTS_UCAN.md:7-74`; the probe contains both conversions and round trips (`research/T15/probes/scaling_canonical.lean`).  The source tree has no `sorry`, `admit`, `axiom`, or `native_decide` in the lane files.  `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the six expected new/record files.

## gaps

No missing T15 declaration was found by searching `formalization/NSFormalization/Section4` for `PlacementData`, `ScalingAPI`, and `scalingStatement`.  A substantive negative probe was run in `research/T15/probes/rev384_negative.lean`: changing `2 * ε ^ 2 < T` to `3 * ε ^ 2 < T` fails with the expected type mismatch at line 8.  The worker report supplies no concrete non-vacuity instance, so add one small probe instance (or document why the full API cannot be instantiated) before merge.  This is the sole fix.

## commands and results

All commands were run after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6` and `lake` from `verification/`.

- `lake build NSFormalization.Section3.T15.Scaling`: pass, build completed successfully.
- `lake env lean ../formalization/NSFormalization/Section3/T15/Scaling.lean`: pass, 0 output.
- `lake env lean ../research/T15/probes/scaling_canonical.lean`: pass, 0 output.
- `lake env lean ../research/T15/axioms_ucan.lean`: pass; every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
- `make check`: pass (plan check, contract policy, 13 policy tests, work queue); it reports pre-existing copied-closure `sorry` tokens and `source_hashes_match: false`, outside this lane.
- `scripts/gates.sh NSFormalization.Section3.T15.Scaling`: pass through build, tests, mutation suite, and contract check; output contains the same pre-existing `make check` warnings.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: pass architecture/policy checks (`base_compatibility_checked: false` is the script's reported status).
- Negative probe: expected failure, `place.eps_time` has type `2 * ε ^ 2 < T` but `3 * ε ^ 2 < T` was expected.

ACCEPT-WITH-NOTES — add one concrete non-vacuity probe instance/documented obstruction.
