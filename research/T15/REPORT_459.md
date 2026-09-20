# Lane 459 — T15 U15 assembly and registration

## 1. Theorem proved

Completed Proposition 3.3's full 21-field `ScalingAPI`, the canonical raw
`scalingStatement_holds`, and the verbatim packet-indexed registered
`scalingStatement`. Its quantifiers remain
`∀ (𝔉 : PacketImportFamily) (ν : ℝ) (hν : 0 < ν) (place : PlacementData
(𝔉.select ν hν).toPacketAPI), Nonempty (ScalingAPI (𝔉.select ν hν) place)`.
The placement is fixed before every scale. Full convergence uses lane 462's
combined `forceConvergence` for both `q=1` and `q=2`; localization is the
canonical proved T13 witness.

`placementData` is data for any prescribed `T` with `0 < T`, and
`(placementData … T hT).T = T` by `rfl` in both layers. Its compact carrier
is `K ∪ Prod.snd '' tsupport f`; its chart is centred at `(1/2,1/2,1/2)`
with radius `3/8`; its threshold is
`min (min (1/2) (T/4)) (1/(8*(R+1)))`, for a positive carrier norm bound R.

The union of the 16 raw clauses is listed in ATTEMPTS_U15.md. The first eight
are exactly I03's `PacketData`; the other eight are pressure support and
extension smoothness, force smoothness/positive compact support/nonpositive
vanishing, extended momentum/divergence, and unbounded speed. No extra
premise is added to either statement. Source and periodized non-vacuity use
`Bindings.packet` at arbitrary positive viscosity and prescribed horizon.

## 2. What Lean now contains

- `Section3/T15/Assembly.lean`: placement construction, definitional horizon
  identity, all 21 assembled fields and canonical statement.
- `Contracts/V1/Scaling3.lean`: the Spec's PlacementData, ScalingAPI and
  scalingStatement copied exactly, over registered vocabulary. An exact
  text comparison of this entire block returned `True`; field count is 21.
- `Bindings/Scaling3.lean`: 16 `rfl` vocabulary bridges, fieldwise placement
  and scaling conversions in both directions with `rfl` round trips,
  statement conversion, canonical placement and registered packet instance.
- `Tests/Scaling3.lean`: checked universal statement, three independent
  field-shape examples (solution, energy identity, full convergence), full
  packet instance, prescribed-horizon example and two nonzero theorems.
- `probes/assembly_closes.lean`: raw clauses restated at the registered
  packet and passed to the canonical assembly.
- Registry/work-item/task cards: `T02.scaling`, V1, parent `T02`; registry
  count 49 → 50. U15 status and attempt/axiom records are updated.

## 3. Gaps and errors

No remaining gap. No existing Lean module was modified. No admissions,
extra axioms, placeholder fields or narrowed conclusion were introduced.
The three resolved development errors (section-variable inclusion, an
existing duplicate binding name, and horizon rewrite matching) are recorded
in ATTEMPTS_U15.md. All 68 named declarations audited across the new canonical,
contract, binding and test modules print exactly the standard three axioms;
the raw probe is audited separately with the same result.

## 4. Commands and results

All Lake commands ran from `verification/`, after `. scripts/lean-env.sh`,
with `LEAN_NUM_THREADS=6`.

```text
lake build Tests.Scaling3
Build completed successfully (10667 jobs).
Contract BlowupDensity.Tests.checkedScaling3: checked; standard logical axioms only
Contract BlowupDensity.Tests.checkedScaling3Packet: checked; standard logical axioms only
Contract BlowupDensity.Tests.scaling3_source_nonzero: checked; standard logical axioms only
Contract BlowupDensity.Tests.scaling3_periodized_nonzero: checked; standard logical axioms only
exit 0

lake env lean ../research/T15/probes/assembly_closes.lean
'NSFormalization.Section3.T15.AssemblyProbe.registeredRawScaling' depends on axioms:
[propext, Classical.choice, Quot.sound]
exit 0

BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh
== make check
[architecture, contract policy and work queue checks passed]
== make test
[registered contract tests checked; standard logical axioms only]
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
exit 0
```

The bracketed gate lines summarize the large closure listings; the remaining
lines above are output excerpts. Full local output is in `tmp/u15-gates.log`.

```text
python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
{
  "registered_contracts": 50,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
exit 0
```

The closure map is omitted here; the base registry has 49 entries.

```text
git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)

python3 experiments/tasks.py render
exit 0

git diff --check
exit 0
```

Axiom command and complete output:

```text
lake env lean ../research/T15/axioms_u15.lean
'NSFormalization.Section3.T15.placementCenter' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementCarrier_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementCarrier_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placement_norm_le_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementThreshold_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placement_chart_in_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementData' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementData_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scalingAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scalingStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.placementOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.localizationOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scalingOfSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.placementToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.placement_to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.placement_of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scalingToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaling_to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaling_of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaledStartTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaledSourcePoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaledVelocity_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaledPressure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scaledForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.periodizedScaledVelocity_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.periodizedScaledPressure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.periodizedScaledForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.normalizedScaledPressure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.IsPeriodicLebesgueSlicePath_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Scaling3.mixedLebesgueENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.MemMixedLebesgueR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.MemMixedLebesgueT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.MemForceSobolevT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.EnergySlicesMemLpT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.alphaT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scalingStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.placementData' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.placementData_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scalingAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scalingStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Scaling3.scalingPacket' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedScaling3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedScaling3Packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.scaling3_source_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.scaling3_periodized_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.scaledStartTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.scaledSourcePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.scaledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.scaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.scaledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.periodizedScaledVelocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.periodizedScaledPressure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.periodizedScaledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.normalizedScaledPressure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.IsPeriodicLebesgueSlicePath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.mixedLebesgueENormT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.MemMixedLebesgueR' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.MemMixedLebesgueT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.MemForceSobolevT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.EnergySlicesMemLpT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.alphaT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.PlacementData' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.ScalingAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Scaling3.scalingStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
