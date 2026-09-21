# Lane 261 report — R46 completed density V1

## 1. The theorem registered

Registered Proposition 4.6 (`prop:Renergy`) as
`R46.completed_density`, version 1.  Its `CompletedDensityAPI` is the complete
three-field `research/R46/Spec.lean` `REnergyAPI`, byte-for-byte after replacing
only the registry-conventional structure name.  It retains completed
inhomogeneous density, completed homogeneous density, and one-family strong
trajectory closure with exact lifespan, full classical solutions, both
reference-field pins, and both simultaneous limits.

The first force-distance term remains exactly
`forceSobolevENorm 1 0`.  R47 uses `mixedLebesgueENorm 1 2` for the analogous
term; these carriers are not definitionally equal.  `COMPARISON.md` now records
as an owner question whether a later vocabulary lane should bridge or align
them.  Neither specification was changed here.

This checkout started with 32 registered contracts, so its required
current-plus-one architecture result is 33.  The task's “34th” integration
position assumes the concurrent R47 V1 registration lands first; that lane's
unmerged files were not copied or edited.

## 2. What Lean now contains

- `verification/Contracts/V1/CompletedDensity.lean` imports only the registered
  `InsertionFamily` contract closure and declares the exact three-field API.
- `verification/Bindings/CompletedDensity.lean` defines the proof theorem
  `completedDensity`: lane 256 supplies `completedSobolevDensity`; lane 259
  supplies `completedHomogeneousDensity_of_realization` and
  `strongTrajectoryClosure_of_realization`; both are instantiated with lane
  255's unconditional `compactHomogeneousRealization`.
- `verification/Tests/CompletedDensity.lean` provides
  `checkedCompletedDensity`, runs `TestSupport.checkAxioms`, and restates all
  three field types in the public vocabulary.
- `research/R46/axioms_contract.lean` audits the realization, all three
  suppliers, the assembled binding, the checked witness, and the final
  conformance theorem.
- The registry and R46 work-item contract list are extended, and
  `python3 experiments/tasks.py render` regenerated the queue and R46 card.

No local vocabulary was restated in the binding.  Lane 259 already uses the
registered `ClassicalSolutionR` and registered lifespan directly, so the final
assembly needs neither a structure conversion nor the
`maximalPartial_maximalLifespanR_eq` bridge.

## 3. Gaps and scope

There is no mathematical gap or conditional premise in the registered
Proposition 4.6 witness.  No field was weakened, split between different
families, or replaced by a different topology.  No existing frozen contract or
test was modified.

The only retained owner question is vocabulary-level: whether R46's
`forceSobolevENorm 1 0` and R47's `mixedLebesgueENorm 1 2` should later receive
a mathematical bridge or be aligned in a future contract version.  Version 1
asserts no such equality.

## 4. Validation

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.  No push, merge, or rebase was performed.

The mechanical statement comparison printed:

```text
structure_byte_match: True
```

The focused build exited 0:

```text
ℹ [10639/10639] Built Tests.CompletedDensity
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
Build completed successfully (10639 jobs).
```

`scripts/gates.sh` exited 0.  Relevant output:

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
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

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
exited 0.  Requested fields:

```text
{
  "registered_contracts": 33,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean
../research/R46/axioms_contract.lean` exited 0 with complete output:

```text
'NSFormalization.Section4.I03.compactHomogeneousRealization' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.completedSobolevDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.completedHomogeneousDensity_of_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.strongTrajectoryClosure_of_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.completedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCompletedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'completedDensityContractConformance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Requested registry stat:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` exited 0 with no output.  The new Lean files contain no
`sorry`, `admit`, `axiom`, or `native_decide` declaration, and no heartbeat
override.
