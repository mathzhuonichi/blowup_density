ACCEPT-WITH-NOTES

## 1. What the lane claims

The lane claims to register the reconciled Theorem 4.7 contract as
`R47.grid_observations` V1, with `GridFamilyAPI` / `GridObservationsAPI`
identical to `RGridFamily` / `RGridAPI` except for those registry names
(`research/R47/REPORT_260.md:5-19`). It claims that lane 258's conditional
assembly is made unconditional with lane 255's realization theorem, then
transported field-for-field across the two nominal record types
(`research/R47/REPORT_260.md:29-43`). It also claims no remaining V1
mathematical or registration gap and says `COMPARISON.md` records the
registration (`research/R47/REPORT_260.md:48-59`).

The mathematical source says: fix a finite family of complete Cartesian
grids; choose one inserted family whose velocity and force cell observations
agree on `0 ≤ t < T`, whose maximal lifespan is exactly `T`, whose energy and
three force norms converge, and whose differences are localized in a common
ball (modulo a spatially constant pressure gauge)
(`paper/sections/04-whole-space.tex:297-304`). The inherited insertion data are
an admissible datum and force, a reference regular beyond `T`, early-history
agreement, and compact force difference (`paper/sections/04-whole-space.tex:31-42`).
The invoked convergence clauses are precisely the energy limit and the
`L¹_tL²_x + L²_tH⁻¹_x + L²_tḢ⁻¹_x` limit
(`paper/sections/04-whole-space.tex:218-228`).

The planned “35th” label is only scheduling metadata. On the required base,
the registry has 32 entries and this lane has 33; the worker discloses that
fact rather than importing unrelated concurrent work
(`research/R47/REPORT_260.md:21-25`).

## 2. What is in Lean

### Statement fidelity

The public record begins with the prescribed parameters
`ν,a,g,T,δ,reference,n,grids` (`verification/Contracts/V1/GridObservations.lean:20-22`).
It contains one positive-radius common ball and one containing cell per grid
(`verification/Contracts/V1/GridObservations.lean:26-40`), one positive scale
cutoff and one total force/solution family
(`verification/Contracts/V1/GridObservations.lean:44-64`), inherited history
and compact force difference (`verification/Contracts/V1/GridObservations.lean:71-78`),
both observation equalities on the correct half-open interval
(`verification/Contracts/V1/GridObservations.lean:84-95`), exact lifespan
(`verification/Contracts/V1/GridObservations.lean:100-101`), the energy and
literal three-term force convergence (including exactly
`mixedLebesgueENorm 1 2`) (`verification/Contracts/V1/GridObservations.lean:106-120`),
and all three support clauses (`verification/Contracts/V1/GridObservations.lean:125-144`).
The outer API preserves the requested universal binder order and selects one
witness only after the whole `Fin n` grid family
(`verification/Contracts/V1/GridObservations.lean:152-165`).

Two independent text comparisons produced no diff: Spec versus contract after
only the two allowed renamings, and Spec versus lane 258's copied records. Thus
the lane satisfies the brief's token-for-token requirement. The registry entry
has the right ID, parent, version, modules, declaration, and an honest scope
(`verification/contracts.json:357-365`).

The registered data are not vacuous. `radius_pos` and `eps_pos` make the ball
and positive-scale interval inhabited (`verification/Contracts/V1/GridObservations.lean:33,48`),
while the outer `0 < T` makes `[0,T)` inhabited
(`verification/Contracts/V1/GridObservations.lean:159-165`). The norms are
`ℝ≥0∞`-valued rather than unsafe `.toReal` bounds
(`verification/Contracts/V1/Data.lean:225-228,251-254,390-393,475-476`), and
the lifespan equality is to finite `ENNReal.ofReal T`, with `T>0`
(`verification/Contracts/V1/GridObservations.lean:98-101`). The grid type is a
complete Cartesian grid with positive widths and half-open cells, and the
observation function is the cell-average function
(`verification/Contracts/V1/Data.lean:757-766,768-784`). Finally, the compiled
one-element unit-grid instance has concrete `ν=T=δ=1`, `a=g=0`
(`research/R47/axioms_contract.lean:41-47`); it is not the empty-family case.

### Implementation and cited suppliers

The adapter copies all nineteen projections from the same assembly witness and
introduces no hypothesis or new choice
(`verification/Bindings/GridObservations.lean:20-44`). The registered theorem
has exactly the API's `choose` statement and calls lane 258 with the
unconditional lane-255 theorem
(`verification/Bindings/GridObservations.lean:47-62`). Lane 258's cited theorem
really has the exact conditional statement
(`verification/Bindings/GridAssembly.lean:305-314`), and lane 255 really proves
`compactHomogeneousRealization` without a premise
(`verification/Bindings/ScalingHomogeneousClosed.lean:26-30`) from the
a.e.-strong-measurability theorem
(`formalization/NSFormalization/Section4/I03/PathMeasurability.lean:178-186`).

The cited tree also contains the actual common-ball supplier
(`verification/Bindings/GridLemmas.lean:28-39`), velocity observation theorem
(`verification/Bindings/ForceCellIntegral.lean:182-198`), and force observation
theorem (`verification/Bindings/FluxCancellation.lean:281-294`). Their
intervals, support containment, grid arguments, and conclusions agree with the
contract. The test exports the registered theorem, runs the axiom checker, and
restates the exact `choose` type (`verification/Tests/GridObservations.lean:15-29`).

No silent extra premise occurs in the public result. The only formerly named
input, `CompactHomogeneousRealization`, is isolated in the upstream assembly
and discharged before registration. The admissibility hypotheses match the
paper and mandated Spec; the explicit reference and positive `T,δ` prevent an
empty-horizon reading.

## 3. Gaps

There is no Lean or mathematical gap in the requested V1 registration.

There is one documentation defect. The worker report says `COMPARISON.md`
records registration (`research/R47/REPORT_260.md:58-59`), but that file still
calls `CompactHomogeneousRealization` the “single remaining input,” says lane
255 is merely assigned, and says the assembly is conditional
(`research/R47/COMPARISON.md:97-101`). Moreover, `COMPARISON.md` is absent from
the branch change list, although the brief required it to be updated. Exact
one-line fix: replace `research/R47/COMPARISON.md:97-101` with:

> The former `CompactHomogeneousRealization` input is discharged unconditionally by lane 255's `I03.compactHomogeneousRealization`, and lane 260 registers the resulting theorem as `R47.grid_observations` V1; no R47 contract gap remains.

The comparison's separate observation that this lane does not prove a general
`mixedLebesgueENorm 1 2 = forceSobolevENorm 1 0` identity is not a blocker and
is accurate (`research/R47/COMPARISON.md:103-109`). As required for a
“not supplied” statement, a multiline whole-tree search of
`formalization/NSFormalization/Section4` for either ordering of those two names
within 500 characters returned no result.

The substantive reviewer mutation widens the velocity-observation interval
from `[0,T)` to `[0,T]` (`research/R47/probes/rev260_widen_interval.lean:19-33`).
It fails specifically because the available theorem requires `Ico`, not because
an argument was dropped. This confirms the endpoint in the main statement is
load-bearing.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, set `LEAN_NUM_THREADS=6`, and
ran Lake from `verification/`. The reviewer made no git state change. The only
reviewer-created files are the permitted probe and this report.

### Exact statement comparisons

```text
$ diff -u <(sed -n '37,182p' research/R47/Spec.lean | sed -e 's/RGridFamily/GridFamilyAPI/g' -e 's/RGridAPI/GridObservationsAPI/g') <(sed -n '20,165p' verification/Contracts/V1/GridObservations.lean)
[no output; exit 0]
$ diff -u <(sed -n '37,182p' research/R47/Spec.lean) <(sed -n '39,184p' verification/Bindings/GridAssembly.lean)
[no output; exit 0]
```

### Focused build and direct elaboration

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build Bindings.GridObservations
...
Build completed successfully (10624 jobs).
```

Exit 0. The omitted replay consists only of pre-existing dependency linter
warnings; there is no warning or error from `Bindings/GridObservations.lean`.
The exact direct-module output was empty:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean Bindings/GridObservations.lean
[no output; exit 0]
```

The registered test target also exited 0. Its relevant exact terminal lines
were:

```text
ℹ [10626/10626] Replayed Tests.GridObservations
info: Tests/GridObservations.lean:18:0: Contract BlowupDensity.Tests.checkedGridObservations: checked; standard logical axioms only
Build completed successfully (10626 jobs).
```

### Axiom audit

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R47/axioms_contract.lean
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

Exit 0. Every printed declaration has exactly the permitted three axioms.

### Repository gates

`LEAN_NUM_THREADS=6 make check` exited 0. Its architecture JSON is very large;
following the repository rule against embedding thousands of closure lines,
the exact terminal tail was:

```text
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GridObservations"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`LEAN_NUM_THREADS=6 scripts/gates.sh Bindings.GridObservations` exited 0. The
exact gate summary (with the large `make check` closure and unrelated contract
audit lines omitted) was:

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== lake build Bindings.GridObservations
Build completed successfully (10624 jobs).
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

The separately required architecture check exited 0. Its requested exact
fields were:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
{
  "registered_contracts": 33,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The base contains 32 registry entries and the lane contains 33. The registry
diff is addition-only:

```text
$ git diff --stat origin/erenup/integration...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

### Hygiene and negative check

```text
$ rg -n "^\\s*(axiom|admit|sorry)\\b|\\bby\\s+(sorry|admit|native_decide)\\b|\\bnative_decide\\b|set_option\\s+maxHeartbeats" verification/Contracts/V1/GridObservations.lean verification/Bindings/GridObservations.lean verification/Tests/GridObservations.lean research/R47/axioms_contract.lean
[no output; exit 1 because there were no matches]
$ git diff --check
[no output; exit 0]
```

There is no `sorry`, `admit`, axiom declaration, `native_decide`, or
`maxHeartbeats` override in the authored Lean. The base change list contains
only generated records plus new lane files; in particular, no pre-existing
contract, test, binding, or formalization module was modified.

The required substantive mutation produced the expected error:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R47/probes/rev260_widen_interval.lean
../research/R47/probes/rev260_widen_interval.lean:33:41: error: Application type mismatch: The argument
  ht
has type
  t ∈ Icc 0 T
but is expected to have type
  t ∈ Ico 0 T
in the application
  F.velocity_observations ε hε i t ht
```

Exit 1, as required.

The whole-tree missing-identity check was also exact and empty:

```text
$ rg -n -U "mixedLebesgueENorm[\\s\\S]{0,500}forceSobolevENorm|forceSobolevENorm[\\s\\S]{0,500}mixedLebesgueENorm" formalization/NSFormalization/Section4
[no output]
```
