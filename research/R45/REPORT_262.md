# Lane 262 — R45 force classes V1

## 1. The theorem registered

Registered Corollary 4.5 (`cor:Rclasses`,
`paper/sections/04-whole-space.tex:194-199`) as the 37th contract,
`R45.force_classes`, version 1. All four fields of the reconciled
`research/R45/Spec.lean` are retained: guarded density in `F_c` or `F_rd`, the
guarded zero-datum density iff the order is strictly subcritical, the
Schwartz-datum rapid-class specialization, and the guarded regular-reference
rider with exact lifespan, both strict norm bounds, and pointwise common
history through every requested cutoff below `T`.

`ForceClassesAPI` matches the complete `RClassesAPI` structure block
byte-for-byte after replacing only the registry-conventional structure name.
The mechanical comparison printed `structure_byte_match: True`.

## 2. What Lean now contains

- `verification/Contracts/V1/ForceClasses.lean` contains the exact four-field
  API and imports only `Contracts.V1.Data`.
- `verification/Bindings/ForceClasses.lean` reuses lane 257's exact guarded
  `density` and `zeroIff` declarations and its `schwartzDensity`. It supplies
  the remaining guarded `regularReference` by eliminating
  `Y = forceClassCompact ∨ Y = forceClassRapid` and returning lane 254's
  `regularReference_compact` or lane 257's `regularReference_rapid`.
- `verification/Tests/ForceClasses.lean` defines `checkedForceClasses`, runs
  `TestSupport.checkAxioms`, and independently restates all four Spec field
  types.
- `research/R45/axioms_contract.lean` audits the suppliers, the new guarded
  rider, the final witness, and the checked contract, and applies the checked
  guarded density field concretely to both force classes.
- `verification/contracts.json` contains the honest 37th entry;
  `collaboration/work_items.json` links it to R45, and
  `python3 experiments/tasks.py render` refreshed the generated queue and R45
  task card. The attempts and comparison records document fidelity and the
  binding route.

No new `rfl` bridge is needed here: the supplier bindings already expose the
registered `Contracts.V1.Data` solution, lifespan, class, and norm vocabulary.

## 3. Gaps and scope

No Corollary 4.5 field remains open, and no statement was weakened. The class
guard permits exactly `forceClassCompact` and `forceClassRapid`; it says
nothing about an arbitrary force subclass. The contract does not claim
completed-space density, add a terminal unbounded-speed conjunct, duplicate a
Schwartz regular-reference rider, or add analytic hypotheses. The two
`CompletedDense* = CompletedDenseVia ...` definitional checks remain outside
the API because they are not clauses of this corollary.

No pre-existing frozen contract or test file was modified.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`. No push, merge, or
rebase was performed.

Focused build, exit 0:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build Tests.ForceClasses
✔ Built Contracts.V1.ForceClasses
✔ Built Bindings.ForceClasses
ℹ Built Tests.ForceClasses
info: Tests/ForceClasses.lean:16:0: Contract BlowupDensity.Tests.checkedForceClasses: checked; standard logical axioms only
Build completed successfully (10617 jobs).
```

`scripts/gates.sh` exited 0. Relevant output (the large architecture closure
JSON and other contracts' audit lines are omitted):

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/ForceClasses.lean:16:0: Contract BlowupDensity.Tests.checkedForceClasses: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The separately requested architecture command
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
exited 0. Requested fields:

```json
{
  "registered_contracts": 33,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The conformance audit
`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R45/axioms_contract.lean`
exited 0. Complete output:

```text
'BlowupDensity.Bindings.density' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.zeroIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.schwartzDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference_rapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedForceClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Requested registry stat:

```text
$ git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` exited 0 with no output.

## Lead note (review 262, 2026-09-17)

The ordinal at the time of writing was "33rd" (the lane's baseline had 32 contracts). After union-merging the registry with the concurrently landed R46 (#254), R47 (#255), A04 V2 (#256) and A01 V2 (#257) registrations, `R45.force_classes` is the **37th** entry; gates rerun on the synchronized branch.
