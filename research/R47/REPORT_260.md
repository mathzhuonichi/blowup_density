# Lane 260 — R47 grid observations V1 contract

## 1. The theorem registered

Registered Theorem 4.7 (`thm:Rgrid`,
`paper/sections/04-whole-space.tex:297-304`) as
`R47.grid_observations`, version 1. The public `GridFamilyAPI` and
`GridObservationsAPI` are the reconciled `research/R47/Spec.lean`
`RGridFamily` and `RGridAPI` token for token apart from those two
registry-conventional names.

The universal quantifier order is unchanged: positive viscosity, admissible
initial datum and force, positive `T` and `δ`, the named reference solution on
`T + δ`, then the complete `Fin n` grid family, followed by one simultaneous
family witness. The witness retains the common ball and containing cells, the
single force/solution family, force class, history, compactness, both grid
observations, exact lifespan, both convergence fields, and all three support
clauses. In particular, force convergence uses the literal
`mixedLebesgueENorm 1 2` spelling required by the Spec.

The lane was assigned the planned integration ordinal “35th.” On the specified
local base, `origin/erenup/integration` currently contains 32 registry entries,
so the required architecture check reports 33, exactly `current + 1`. No
unrelated concurrent contract was copied or merged merely to manufacture an
ordinal in this worktree.

## 2. What Lean now contains

- `verification/Contracts/V1/GridObservations.lean` contains the two exact
  public structures and imports only `Contracts.V1.Data`.
- `verification/Bindings/GridObservations.lean` instantiates lane 258's
  `rGrid_choose_of_realization` with lane 255's unconditional
  `I03.compactHomogeneousRealization`.
- The lane-258 research record and the public contract record are distinct
  nominal structures. `gridFamilyAPI_of_rGridFamily` therefore assigns all
  nineteen fields directly from the one assembly witness. It chooses no new
  ball, force, solution, cell, or gauge and changes no proposition.
- `verification/Tests/GridObservations.lean` provides
  `checkedGridObservations`, runs `TestSupport.checkAxioms`, and restates the
  exact `choose` field type.
- `research/R47/axioms_contract.lean` audits the complete supplier chain and
  gives concrete zero-data witnesses for both an empty grid family and a
  one-element unit grid family.
- The registry and R47 work-item lists have one addition, and
  `python3 experiments/tasks.py render` regenerated the queue and R47 task
  card. No existing frozen contract or test was edited.

## 3. Gaps and scope

There is no remaining mathematical or registration gap for this V1 contract.
The only binding adapter is the field-for-field transport between two nominal
record types with identical fields; it is not a weakened API.

As required by the reconciliation, this contract does not assert Proposition
4.6 completed-space density, point observations, pressure observations,
closure/interior containment, uniformity under arbitrary refinement, or an
identity between `mixedLebesgueENorm 1 2` and an order-zero Sobolev norm.
`research/R47/ATTEMPTS_CONTRACT.md` records the nominal-structure issue and the
successful binding route; `COMPARISON.md` records the registration.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`,
and ran Lake only from `verification/`. No push, merge, or rebase was
performed.

Focused build:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build Tests.GridObservations
ℹ [10626/10626] Built Tests.GridObservations (2.6s)
info: Tests/GridObservations.lean:18:0: Contract BlowupDensity.Tests.checkedGridObservations: checked; standard logical axioms only
Build completed successfully (10626 jobs).
```

`scripts/gates.sh` exited 0. Relevant output (the large architecture closure
and the other registered contracts' audit lines are omitted):

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/GridObservations.lean:18:0: Contract BlowupDensity.Tests.checkedGridObservations: checked; standard logical axioms only
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

```text
{
  "registered_contracts": 33,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean
../research/R47/axioms_contract.lean` exited 0. Complete output:

```text
'NSFormalization.Section4.I03.compactHomogeneousRealization' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.rGridFamily_of_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.rGrid_choose_of_realization' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gridFamilyAPI_of_rGridFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gridObservations_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gridObservations' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedGridObservations' depends on axioms: [propext, Classical.choice, Quot.sound]
'GridObservationsContractConformance.choose' depends on axioms: [propext, Classical.choice, Quot.sound]
'GridObservationsContractConformance.emptyGridWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
'GridObservationsContractConformance.unitGridWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Statement fidelity comparison after replacing only `RGridFamily` with
`GridFamilyAPI` and `RGridAPI` with `GridObservationsAPI`:

```text
Spec structure diff: no output (PASS)
```

Requested registry stat:

```text
$ git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` exited 0 with no output. The authored Lean files contain no
`sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override.
