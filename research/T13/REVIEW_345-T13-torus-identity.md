ACCEPT-WITH-NOTES

## what the lane claims

The report claims the `LocalizationAPI.torus_identity` field is proved for `0 < s < 1`, smooth periodic `f`, with finiteness and the exact equality. The API statement at [research/T13/probes/api_on_canonical.lean:52](../probes/api_on_canonical.lean) matches the theorem at [formalization/NSFormalization/Section3/T13/TorusIdentity.lean:1174](../../formalization/NSFormalization/Section3/T13/TorusIdentity.lean). The paper's displayed identity is at `paper/sections/03-torus.tex:53-72`; the Fourier weight and `2π` factor agree with the implementation's `kernelIntegral_eq` at `.../TorusIdentity.lean:126`.

## what is in Lean

`torus_identity_smooth` proves the equality, and `torus_identity` adds finiteness using `cFrac_lt_top` and `periodicHomogeneousENorm_lt_top` ([TorusIdentity.lean:1100-1104](../../formalization/NSFormalization/Section3/T13/TorusIdentity.lean), [1174-1179](../../formalization/NSFormalization/Section3/T13/TorusIdentity.lean)). The non-vacuity probe contains a genuinely nonconstant smooth periodic mode ([research/T13/probes/torus_identity_closes.lean:29-72](../probes/torus_identity_closes.lean)). No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the new module; the three max-heartbeat declarations are commented and use 400000 ([TorusIdentity.lean:792,861,1098](../../formalization/NSFormalization/Section3/T13/TorusIdentity.lean)). A whole-Section4 grep found no pre-existing declaration supplying the claimed residual single-mode computation.

## gaps

The report is honest that the explicit numerical value of `ITorus` on the cosine mode is not proved; this is outside the API field. The required negative mutation was run in `research/T13/probes/rev345_mutation.lean`, changing the RHS by `+ 1`; Lean rejects it with a type mismatch showing the original conclusion. The lane's `git diff --name-only origin/erenup/integration-section3...HEAD` also lists unrelated pre-existing T11 files, so integration should preserve only the lane's new T13 artifacts when reviewing scope.

## commands and results

* `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.TorusIdentity`: success (0 errors; upstream linter warnings only).
* `lake env lean` on the module and `torus_identity_closes.lean`: success, no output.
* `lake env lean` on `axioms_torus_identity.lean`: success; every printed declaration has exactly `[propext, Classical.choice, Quot.sound]`.
* `scripts/gates.sh NSFormalization.Section3.T13.TorusIdentity`: `== gates OK` (mutation suite passed).
* `make check`: success; 13 policy tests and 45 work items consistent.
* `experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: fails before lane checks with `AssertionError: Removed stable specification: verification/Contracts/V1/TorusLocalTheory.lean`; this is a stale/mismatched base contract on the lane branch, not caused by the new T13 module, but must be resolved before merge.

The one fix is to rebase/refresh the lane against the current integration contract base and rerun `check_contracts.py` successfully.
