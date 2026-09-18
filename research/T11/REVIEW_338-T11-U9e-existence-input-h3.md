REJECT

## What the lane claims

The worker claims that `PeriodicQuantitativeLocalInputH3` is exactly amendment 2's
`PeriodicQuantitativeLocalInput'` with only the datum order changed from 1 to 3,
and that `periodicQuantitativeLocalInputH3` proves it without a named input.  The
definition is indeed written with the stated quantifiers and hypotheses at
`formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean:81-91`; the
source predicate it is compared against is
`formalization/NSFormalization/Section3/T11/LocalExistence.lean:23-29`.

The report also claims an explicit horizon and the continuation re-instantiations:
`exists_classical_on_picardHorizon` and its corollary are at
`ExistenceInputH3.lean:266-341`; `restartH3` is at `:350-370`,
`restartBeyondH3` at `:406-449`, `extendsBeyondH3` at `:456-479`,
`lifespanInfiniteOfLocallyFiniteH3` at `:484-520`, and
`exists_maximal_unconditional` at `:393-399`.  These statements match the
H³ variants written in `research/T11/probes/existence_input_h3_closes.lean:26-144`.
The report's non-vacuity witness is also substantive: the module requires a
nonzero datum/force/solution in `ExistenceInputH3.lean:524-537`, and the probe
checks it at `existence_input_h3_closes.lean:146-159`.

## What is in Lean

The mathematical route typechecks.  The L¹ force estimate and attainment claim
are present at `ExistenceInputH3.lean:98-136`; the heat contraction and L¹ affine
bound are at `:141-191`; and the horizon depends only on `ν`, `K`, and `M 3` in
`:213-250`.  The proof feeds the order-three datum, smooth force path, and Leray
projection into the Picard certificate at `:279-333`, then applies
`mild_to_classical`.
It constructs the continuous projected path directly from
`exists_smooth_forceDatumPath` at `:286-296`, rather than calling the sibling
`exists_continuous_lerayForcePath`; the resulting `P` and its continuity are the
same required objects, so this is not a statement mismatch.

The H¹ gap is honestly documented rather than silently discharged:
`research/T11/H1_GAP.md:9-41` gives the exact residual H¹ statements, and
`:43-77` explains the missing subcritical theory.  A whole-tree search of
`formalization/NSFormalization/Section4` found no exact T11
`PeriodicQuantitativeLocalInput` or `PeriodicRestartH1`; it did find the
analogous, explicitly unproved A01 predicate
`ManuscriptHorizonLowerBoundH1` at
`formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean:368-379`
and abstract `restartBeyond` declarations in A04.  Thus the lane's narrower
“not in the T11 tree” claim is supported, while the existing Section4 analogue
must not be overlooked.  This is also consistent with the manuscript's explicit
Fujita–Kato critical-force discussion (`paper/sections/03-torus.tex:371-393`).

There is, however, a blocking hygiene violation.  The lane commit itself edits
the already-existing dependency `formalization/NSFormalization/Section3/T11/MildClassical.lean`:
it deletes `hFI` at line 1291 and changes the two applications at lines 1304 and
1318.  The file was already brought into this lane's base by the 334 merge
(`0c03030c`) and is then modified by the lane commit (`57997c1b`; the exact
hunks are against `MildClassical.lean:1291,1304,1318`).  The worker explicitly
admits the repair in `research/T11/REPORT_338.md:106-116`.  The brief's “new files
only / no existing module modified” rule is therefore not met; the fact that the
base was broken does not authorize a lane edit.

## Gaps and negative check

The worker's checked-in probe has no substantive mutation test.  I added the
permitted reviewer-only probe `research/T11/probes/rev338_h1_mutation.lean`, which
changes the main datum-ball hypothesis to H¹ at lines 16-22 and attempts the same
Picard proof at line 26.  Running it gives the expected failure (so the H³
hypothesis is load-bearing):

```
../research/T11/probes/rev338_h1_mutation.lean:26:62: error: Application type mismatch: The argument
  hKa
has type
  periodicSobolevENorm 1 a ≤ K
but is expected to have type
  periodicSobolevENorm 3 a ≤ K
in the application
  exists_classical_on_picardHorizon ν hν K hK M hM a ha hKa
```

This satisfies the review negative-check requirement, but it does not cure the
new-file-only violation.  The exact fix is to move the three-line compatibility
repair into the appropriate base/dependency lane (or land the corrected
`MildClassical` before this lane), then rerun this lane with no diff to that
module.  The report should also retain the H¹ gap rather than relabeling the H³
theorem as the manuscript's H¹ input.

## Commands and results

All commands were run read-only from this worktree, after `. scripts/lean-env.sh`,
with `LEAN_NUM_THREADS=6` for Lake and with Lake invoked only from `verification/`.

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ExistenceInputH3`
  exited 0 and ended with the exact line `Build completed successfully (10579 jobs).`
  It replayed dependency linter warnings, but no module error.
* `cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean`
  exited 0 with no output.
* `cd verification && lake env lean ../research/T11/probes/existence_input_h3_closes.lean`
  exited 0 with no output.
* `cd verification && lake env lean ../research/T11/axioms_existence_input_h3.lean`
  exited 0 with no output; its 24 `#guard_msgs` checks (including the three
  explicitly named local instances) are recorded at
  `research/T11/axioms_existence_input_h3.lean:10-120` and all expect exactly
  `[propext, Classical.choice, Quot.sound]`.
* `make check` exited 0.  Its exact relevant tail was

  ```
  .............
  ----------------------------------------------------------------------
  Ran 13 tests in 0.044s

  OK
  python3 experiments/check_work_queue.py
  45 work items: ownership, contract registration and task cards consistent.
  ```
  The architecture check also reported `registered_contracts: 38` and
  `base_compatibility_checked: false` for the plain invocation.
* `scripts/gates.sh NSFormalization.Section3.T11.ExistenceInputH3` exited 0 with
  the exact mutation/gate lines:

  ```
  extra_axiom: rejected as required
  weakened_hypothesis: rejected as required
  Mutation suite passed. This is an infrastructure check, not a PDE proof.
  == gates OK
  ```

  The explicit `python3 experiments/check_contracts.py --base-ref
  origin/erenup/integration-section3` also exited 0 and ended with
  `"base_compatibility_checked": true`.
* The module itself has no `sorry`, `admit`, `native_decide`, `axiom`, or
  `maxHeartbeats` token.  The mandated changed-name check
  `git diff --name-only origin/erenup/integration-section3...HEAD` includes
  `formalization/NSFormalization/Section3/T11/MildClassical.lean` (as well as
  merged dependency files), and the lane commit's three hunks above are the
  blocking hygiene finding.
