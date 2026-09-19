# Lane 455 — T18 U12 assembly and registration

## 1. What was proved

`NSFormalization.Section3.T18.assemble` constructs all **45 fields** of the
canonical `PeriodicInsertionAPI` from U1–U11. `RawPremises data` bundles
exactly `hsupp` (packet slice support), `hM` and `hD` (the two energy signs).
The canonical `periodicInsertionStatement_holds` quantifies all raw packet
fields and the threaded placement/scaling/reference/correction records.

The registered `BlowupDensity.T18.Spec.periodicInsertionStatement` is proved
by `Bindings.PeriodicInsertion.periodicInsertionStatement_holds` and checked
as `BlowupDensity.Tests.checkedPeriodicInsertion`. Its **record and statement
are byte-identical** to `research/T18/Spec.lean`; it adds no raw premises.
The binding discharges them using `PacketImportAPI.velocity_support`,
`energy_isLUB` at time zero, and `dissipation_eq`. Exact momentum, maximal
lifespan `T`, both blow-up forms, periodic shrinking support, all three
closeness rates and negative-order honesty are included. No analytic input
or conclusion field is deferred.

## 2. What exists in Lean

- `formalization/NSFormalization/Section3/T18/Assembly.lean`: canonical record,
  explicit raw-premise bundle, assembly, universally quantified existence
  statement and conditional non-vacuity theorem.
- `verification/Contracts/V1/PeriodicInsertion.lean`: verbatim T18 contract;
  T15 scaling restatement; historical namespace exports of registered packet,
  localization, local-potential and `Correction3.Packet` vocabulary.
- `verification/Bindings/PeriodicInsertion.lean`: fieldwise conversions in
  both directions with `rfl` round trips; named definitional bridges;
  constructed API, statement theorem and statement iff bridge; explicit
  `nonvacuity_of_witnesses`.
- `verification/Tests/PeriodicInsertion.lean`: checked statement, axiom check,
  independent momentum/support/energy field shapes and staged non-vacuity.
- `research/T18/axioms_u12.lean`: all **78** new named implementation/contract
  declarations audited; each has exactly the three standard logical axioms.
- Registry `T03.periodic_insertion`, V1; work items and generated cards;
  `ATTEMPTS_U12.md` and the completed U12 status in `T18_SPLIT.md`.

The initial worktree had 46 contracts but the requested remote base has 48.
Eight missing prerequisite files were copied **byte-for-byte** from base
`33515e1fea080d094f2b97863a843317e259480e`: the T17/T20 canonical assemblies
and the `Correction3`/`CriticalRegularityT` registration trios. Their two
registry entries and work-item references were restored. These are already
landed prerequisites, not additional lane-455 registrations. Final count:
**49 = base 48 + 1**. No existing Lean module was edited. No merge, rebase,
or push was performed; the work is committed on
`erenup/455-T18-U12-assembly-registration`.

`parent_task` is `T02`, exactly as the T18 work-item deliverable specifies;
the requested contract ID remains `T03.periodic_insertion`. The registry
scope records that existing bucket discrepancy explicitly.

## 3. What remains missing

Only concrete **end-to-end non-vacuity** remains staged: a full T15 U15
scaling/placement witness for the registered packet, together with a
compatible reference and cutoff/correction witness. T13/T11 are already
inhabited. The landed T17 U12 now supplies an amended correction existence
theorem and a nonzero-reference example, but that example does not instantiate
the future T15 scaling record automatically. Its viscosity, radius, margin,
global smoothness/periodicity, local divergence, packet-support and chart
hypotheses must hold for the chosen data.

The binding and test spell the gate as
`(∃ scaling, ∃ reference, Nonempty (CorrectionAPI …)) → Nonempty (Σ scaling,
Σ reference, Σ correction, PeriodicInsertionAPI …)`, with positive margin
and initial/force class hypotheses explicit. This is proved without an
admission; no unconditional concrete insertion witness is claimed.
Resolved elaboration failures and the original base mismatch are recorded
in `ATTEMPTS_U12.md`. There are no unresolved proof or gate failures.

## 4. Commands and results

All commands ran in this worktree after `. scripts/lean-env.sh`; every Lake
invocation ran from `verification/` with `LEAN_NUM_THREADS=6`.

`lake build Tests.PeriodicInsertion Tests.Correction3 Tests.CriticalRegularityT`
— exit 0. The targeted T18 build printed:

```text
Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
Build completed successfully (10664 jobs).
```

`BASE_REF=origin/erenup/integration-section3 scripts/gates.sh` — exit 0.
Pasted gate summary (the large module-closure lists and unrelated contract
success lines are omitted):

```text
== make check
  "registered_contracts": 49,
Ran 13 tests in 0.045s
OK
45 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
== gates OK
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
— exit 0. Output with the module-closure listing omitted:

```json
{
  "registered_contracts": 49,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`lake env lean ../research/T18/axioms_u12.lean` — exit 0. Complete output:

```text
'NSFormalization.Section3.T18.assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.periodicInsertionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.periodicInsertionStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.nonvacuity_of_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.placementOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.localizationOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.potentialOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scalingOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correctionOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.ofSpecInputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.packet_energyBound_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.packet_dissipationBound_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.toSpecAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.ofSpecAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.api_to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.api_of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.periodicInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.periodicInsertionStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaledStartTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaledSourcePoint_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.IsPeriodicLebesgueSlicePath_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.mixedLebesgueENormT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.MemMixedLebesgueR_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.MemMixedLebesgueT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.MemForceSobolevT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.EnergySlicesMemLpT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.alphaT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaledVelocity_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaledPressure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaledForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.periodizedScaledVelocity_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.periodizedScaledPressure_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.periodizedScaledForce_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.normalizedScaledPressure_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.torusSpaceTimeLift_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.torusSpatialSupport_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.torusTemporalSupport_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.fixedProfileCylinder_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correctionForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correctionChartPoint_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.rescaledReference_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.rescaledPotential_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.rescaledCorrectionProfile_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.rescaledForceProfile_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.placementToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.placement_to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.placement_of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scalingToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaling_to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.scaling_of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correctionToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correction_to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correction_of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.correctionPlacement_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.nonvacuity_of_witnesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.PeriodicInsertion.periodicInsertionStatement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Tests.checkedPeriodicInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.PeriodicInsertionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.RawPremises' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.scaledStartTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.scaledSourcePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.scaledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.scaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.scaledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.periodizedScaledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.periodizedScaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.periodizedScaledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.normalizedScaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.IsPeriodicLebesgueSlicePath' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.mixedLebesgueENormT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.MemMixedLebesgueR' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.MemMixedLebesgueT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.MemForceSobolevT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.EnergySlicesMemLpT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.alphaT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T15.Draft.ScalingAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T18.Spec.PeriodicInsertionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T18.Spec.periodicInsertionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]

```

`git diff --stat verification/contracts.json` (before commit):

```text
 verification/contracts.json | 33 +++++++++++++++++++++++++++++++++
 1 file changed, 33 insertions(+)

```

The 33 added lines include 22 for the two already-landed prerequisite entries.
Relative to the requested remote base, the same registry diff is exactly
one entry:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)

```

Additional checks: `python3 experiments/tasks.py render` succeeded;
`git diff --check` was clean; exact text comparison confirmed both T18
contract declarations match the Spec; all eight recovered prerequisite files
match base bytes; all 78 printed axiom sets equal
`[propext, Classical.choice, Quot.sound]`.
