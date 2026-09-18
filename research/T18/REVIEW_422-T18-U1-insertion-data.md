ACCEPT-WITH-NOTES

## What the lane claims

The report claims a raw-field `InsertionData` bundle, the inserted velocity,
pressure, and force, the three `eq:insertion` formulas, the common threshold,
and five threaded hypothesis/bound theorems.  These claims match the requested
U1 fields in `research/T18/Spec.lean:1684-1734`: the Spec formulas and quantifier
orders agree with the canonical declarations at
`formalization/NSFormalization/Section3/T18/Insertion.lean:59-121`.

## What is in Lean

`InsertionData` has the raw packet fields, placement/scaling records, reference,
cutoff/correction data, and the three hypotheses at
`formalization/NSFormalization/Section3/T18/Insertion.lean:37-57`.
The definitions use the exact threaded terms at lines 60-73; all three formula
theorems are definitional (`rfl`) at lines 76-96.  The threshold and its bounds
are at lines 99-111, and the positivity/membership projections are at lines
102-121.  The conformance probe discharges all eleven Spec U1 fields
fieldwise (`research/T18/probes/insertion_closes.lean:216-244`) and includes a
conditional `Nonempty` instance (`:246-256`).

## Gaps

No mathematical or elaboration gap was found.  The report says the axiom audit
contains “all 14 declarations” (`research/T18/REPORT_422.md:101`), but the audit
prints 15 declarations (the structure, four definitions, and ten theorems), as
confirmed by `research/T18/axioms_u1.lean:12-25`; this is a documentation
counting error only.  The report correctly records that no concrete full
`InsertionData` witness exists (`REPORT_422.md:77-86`), and the required
Section4 tree search found no missing U1 lemma.  A substantive sign mutation in
`research/T18/probes/rev422_mutation.lean` fails with a type mismatch at line
239, so the proof is not vacuous.

## Commands and results

All commands used `. scripts/lean-env.sh`; Lake commands ran from `verification/`
with `LEAN_NUM_THREADS=6`.

* `lake build NSFormalization.Section3.T18.Insertion` — `Build completed successfully (10016 jobs)`.
* `lake env lean` on the module and conformance probe — exit 0, no module/probe errors.
* `lake env lean ../research/T18/axioms_u1.lean` — exit 0; every printed declaration has exactly `[propext, Classical.choice, Quot.sound]`.
* Root `make check` — exit 0: plan check, contract policy (`Ran 13 tests ... OK`), and `45 work items ... consistent` (with the repository’s pre-existing `source_hashes_match=false`).
* Mutation probe — expected failure: `Type mismatch ... velocity_formula ... expected ... + -Spec.periodizedScaledVelocity` (exit 1).
* `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the new T18 module/research artifacts; no existing module is modified.  Repository grep found no forbidden token in the lane module/probe, and no declaration uses `maxHeartbeats`.

Verdict: ACCEPT-WITH-NOTES — fix the report’s “14 declarations” count to “15”.
