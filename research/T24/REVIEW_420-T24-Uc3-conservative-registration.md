REJECT

## What the lane claims

`REPORT_420.md:3-16` claims that Uc3 assembles exactly the two torus clauses,
`potential_pairing` and `zero_from_rest`, with no named input.  The cited paper
proposition is `paper/sections/03-torus.tex:723-726`; its torus clause is
explicitly `f=-∇φ` for a globally defined periodic scalar, while the proof's
pairing is at `paper/sections/03-torus.tex:728-738`.  The lane's deliberate
torus-only scope is honestly documented at
`verification/Contracts/V1/ConservativeForcing.lean:10-14,53-55` and in the
registry at `verification/contracts.json:441`.

## What is in Lean

The statement fidelity check passes for the torus branch.  The source
definitions in `research/T24/Spec.lean:1367-1373` are reproduced at
`verification/Contracts/V1/ConservativeForcing.lean:41-47` and guarded by the
`rfl` bridges at `verification/Bindings/ConservativeForcing.lean:29-35`.
The two fields match `research/T24/Spec.lean:1391-1412` and are reproduced at
`verification/Contracts/V1/ConservativeForcing.lean:65-86`; in particular the
pairing has an explicit Haar integral and inner product, and the velocity
conclusion is on `Ico 0 T`, not a global function equality.  The canonical
assembly is concrete at
`formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean:26-47`.

The non-vacuity witness is genuine: `restSolution` constructs a full canonical
`ClassicalSolutionT` with zero velocity and pressure at
`formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean:55-84`,
and the contract-side existence test uses it at
`verification/Tests/ConservativeForcing.lean:45-62`.  The structure exception is
handled through the existing fieldwise conversions in
`verification/Bindings/TorusLocalTheory.lean:198-260`, used by the new binding
at `verification/Bindings/ConservativeForcing.lean:39-75`.  The registered test
and both independent field conformance examples are at
`verification/Tests/ConservativeForcing.lean:20-43`.

The bounded-domain/no-slip omission is a supported scope gap, not a silently
periodicized claim: the required search of
`formalization/NSFormalization/Section4` for bounded-domain/no-slip carriers
returned no matches, while the contract says the branch is out of V1 scope at
`verification/Contracts/V1/ConservativeForcing.lean:10-14`.

## Gaps

1. **Blocking gate failure (current-base compatibility).**  The lane report
   claims `base_compatibility_checked: true` and a 43-contract base at
   `research/T24/REPORT_420.md:90-98`, but the current
   `origin/erenup/integration-section3` has 45 contracts.  Comparing the JSON
   files gives base-only `T04.affine_variation` and `T04.bounded_domain_norm`,
   while this branch has `T04.conservative_forcing`; the required command
   fails with:

   ```text
   AssertionError: Removed stable specification: verification/Contracts/V1/AffineVariation.lean
   ```

   This is a real failure of both `check_contracts.py --base-ref ...` and the
   `scripts/gates.sh` contract gate, not a reporting-format difference.

2. **Hygiene/scope violation: existing and unrelated modules are changed.**
   `git diff --name-only origin/erenup/integration-section3...HEAD` includes
   modifications to the existing T12 modules
   `formalization/NSFormalization/Section3/T12/GradientLSix.lean:1-4,185-186`
   and `GradientLambdaL3.lean:211-213`, plus the new deduplication module
   `formalization/NSFormalization/Section3/T12/DirDeriv.lean:1-31`.  It also
   carries an unrelated MeanZero contract/binding/test
   (`verification/Contracts/V1/MeanZeroCalculus.lean:1-18`,
   `verification/Bindings/MeanZeroCalculus.lean:1-14`,
   `verification/Tests/MeanZeroCalculus.lean:1-12`).  The Uc3 brief permits
   only the named Uc3 modules and registry/work-item records; these files must
   be removed or split into their own lane, and no existing module may remain
   modified relative to the current base.

3. **The worker record has no mutation evidence.**  `ATTEMPTS_UC3.md:36-41`
   records only an elaboration failure, and `REPORT_420.md:124-127` records
   scans but no substantive negative check.  The reviewer probe
   `research/T24/probes/rev420_negative_interval.lean:13-22` changed the main
   `Ico` interval to `Ioc`; Lean rejected the attempted proof at line 22 with
   the expected type mismatch (`t ∈ Ioc 0 T` versus `t ∈ Ico 0 T`).  Preserve
   equivalent mutation evidence in the lane records after the base/scope fix.

## Commands and results

All Lean commands below were run from `verification/` after
`. ../scripts/lean-env.sh`; builds used `LEAN_NUM_THREADS=6`.  The shell emitted
the unrelated profile warning
`/home/ping/.profile: line 31: .../cargo/env: No such file or directory`.

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.ConservativeAssembly
Build completed successfully (10570 jobs).

LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean
[no output; exit 0]
```

The axiom audit is:

```text
'NSFormalization.Section3.T24.conservativeForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.restSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.ConservativeForcing.conservativeForcing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.ConservativeForcing.conservativeForcingStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.ConservativeForcing.restSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedConservativeForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` exited 0.  Its final summary included
`base_compatibility_checked: false`, the 13 contract-policy tests `OK`, and
`45 work items: ownership, contract registration and task cards consistent.`
`git diff --check` also passed.

The required full gate reached the Lean build and mutation suite, then failed
at the base contract check:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
AssertionError: Removed stable specification: verification/Contracts/V1/AffineVariation.lean
```

Running `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
reproduced the same assertion.  The forbidden-token scan over the Uc3 proof,
contract, binding, and test files found no declaration-level
`sorry`/`admit`/`axiom`/`native_decide`, and no `maxHeartbeats`; matches were
only the audit/comment words in `research/T24/axioms_uc3.lean:4` and the test
module's documentation at `verification/Tests/ConservativeForcing.lean:6`.

The negative probe command exited 1 as required:

```text
error: Application type mismatch: The argument
  ht
has type
  t ∈ Ioc 0 T
but is expected to have type
  t ∈ Ico 0 T
```

Fixes required before re-review:

- bring the lane to the current integration base while retaining all stable
  contracts, then rerun `scripts/gates.sh` and the base-ref check to exit 0;
- remove the unrelated MeanZero/T12 changes (or split them), leaving only the
  named Uc3 deliverables and permitted records;
- add the substantive mutation result to the worker's ATTEMPTS/report.
