# Lane 394 report — T17 U-CAN canonical correction

## 1. What was restated

`NSFormalization.Section3.T17.Correction` now provides the canonical T17
statement layer needed by T18.  `CorrectionAPI` has all 45 reconciled Spec
fields in their original order and with their paper-line docstrings.  Its
placement is T15 U-CAN's raw-field `PlacementData u p f K`; the sole packet
projection in the Spec, `P.velocity`, is `u`, while the profile formulas use
the proved bare `(place.x₀, place.T)` spelling.  `correctionStatement` has the
same existential shape over the raw parameters.

Lane 375 was not present on this base, so the canonical U4
`ForceProfile.lean` source was also restored as a new file.  The already
canonical U3/U2/U5/U6 modules are imported unchanged.

## 2. Lean files and conformance

- `Correction.lean` imports canonical T13/T15/T16 and T17 proof units; it does
  not import `Contracts.*`.
- `correction_canonical.lean` imports the contract layer, carries the literal
  reconciled Spec block under a probe namespace, and provides fieldwise
  adapters for placement, cutoff, local potential, localization, and all 45
  correction fields in both directions.  Both correction conversions have
  round-trip theorems.
- The probe records `rfl` bridges for the fixed cylinder, chart point, the
  three profiles, correction force, and both torus support projections.  It
  closes the landed U3/U4 profile conclusions and U5/U6 derivative bounds by
  `exact` under their stated `hv` and `ε₀≤1` premises.
- `axioms_ucan.lean` audits the new canonical declarations; every printed
  footprint is exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps

This is deliberately a statement-restatement unit and constructs no
`CorrectionAPI` inhabitant.  Per G1, the record field list is unchanged and
contains no `reference_smooth`; T17 assembly must obtain the proved units'
global `hv : ContDiff ℝ ∞ v` premise by chart truncation or by an explicit
assembly theorem hypothesis.

The canonical periodized `force_profile_identity` is closed at the concrete
`correctionData` by
`NSFormalization.Section3.T17.force_profile_identity_canonical` in
`research/T17/probes/force_profile_canonical.lean`.  Its conclusion is
literally the canonical field type specialized to that data.  It composes
U2's `Transport.force_eq` with the local single-copy germ from
`T16.latticeLift_eq_of_ball`, then applies U4's
`physicalForce_eq_rescaledForceProfile`; its only extra premise is the
documented G1 hypothesis `hv : ContDiff ℝ ∞ v`.  The later support, volume,
energy, mixed, and Sobolev proof units remain outside this lane.

## 4. Commands and results

Run from the worktree after `. scripts/lean-env.sh`, with every Lake command
from `verification/`:

| Command | Result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Correction` | pass, 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T17/Correction.lean` | pass, 0 output |
| `lake env lean ../research/T17/probes/correction_canonical.lean` | pass, 0 output |
| `lake env lean ../research/T17/axioms_ucan.lean` | pass; every declaration reports exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` | pass: plan check, contract/import policy, 13 policy tests, and 45-item work queue |

## Continuation (fix)

### 1. What closed

Outcome A is complete.  The probe theorem
`NSFormalization.Section3.T17.force_profile_identity_canonical` has literally
the canonical `CorrectionAPI.force_profile_identity` conclusion specialized to
the concrete `correctionData`.  Its only added premise is the documented G1
premise `hv : ContDiff ℝ ∞ v`; all other premises are canonical record data
already available before the field (`potential`, `radius_pos`,
`ball_in_chart`, `reference_periodic`, and `place.chartBall_in_cube`).

The proof composes `Transport.force_eq` with a genuine local single-copy germ.
The latter uses `ball_in_chart` and `place.chartBall_in_cube` to obtain
`2*r < 1`, proves the chart point lies in `ball place.x₀ r`, obtains the
single-copy force support from `physical_support` and
`source_correctionForce_support`, and applies `T16.latticeLift_eq_of_ball`.
The remaining chart equality is exactly
`ForceProfile.physicalForce_eq_rescaledForceProfile`.

### 2. Files

- `research/T17/probes/force_profile_canonical.lean`: adds the canonical
  concrete-data theorem and a silent exact three-axiom guard.
- `formalization/NSFormalization/Section3/T17/ForceProfile.lean`: repairs the
  stale lane/source narrative, records that `Transport.force_eq` is present,
  and points to `ATTEMPTS_UCAN.md` and the closing probe.
- `research/T17/ATTEMPTS_UCAN.md`: changes the honest U4 residual from open to
  closed and records the proof route.
- `research/T17/REPORT_394.md`: corrects §3 and records this continuation.

### 3. Exact gap

There is no residual gap in the requested concrete canonical
`force_profile_identity` conformance, so no T17 U4b re-scope is needed.  G1
remains exactly as documented: a future full `CorrectionAPI` assembly must
supply `hv : ContDiff ℝ ∞ v` by chart truncation or as an explicit assembly
hypothesis.  This continuation still does not construct a complete
`CorrectionAPI` inhabitant; the later support, volume, energy, mixed, and
Sobolev fields remain their separately scoped proof units.

### 4. Commands and outputs

Every Lake command was run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T17.Correction NSFormalization.Section3.T17.ForceProfile`
exited 0.  It replayed pre-existing dependency warnings and ended exactly:

```text
✔ [10014/10015] Built NSFormalization.Section3.T17.ForceProfile (2.9s)
✔ [10015/10015] Built NSFormalization.Section3.T17.Correction (2.8s)
Build completed successfully (10015 jobs).
```

The following each exited 0 with output exactly empty:

```text
lake env lean ../formalization/NSFormalization/Section3/T17/Correction.lean
lake env lean ../formalization/NSFormalization/Section3/T17/ForceProfile.lean
lake env lean ../research/T17/probes/force_profile_canonical.lean
```

The last command is the replacement for the rejected
`rev394_field_conformance.lean` probe.  Its silent `#guard_msgs` audit asserts
that `force_profile_identity_canonical` prints exactly
`[propext, Classical.choice, Quot.sound]`.

`lake env lean ../research/T17/axioms_ucan.lean` exited 0 and printed:

```text
'NSFormalization.Section3.T17.rescaledReference' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.rescaledForceProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.spatialDerivative_rescaledReference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.rescaledReference_spatialDerivative_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.rescaledForceProfile_eq_forceProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.force_profile_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_profile_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceProfileConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceProfileConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_profile_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.inverseScale_correctionChartPoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.physicalForce_eq_rescaledForceProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.torusSpaceTimeLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.torusSpatialSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.torusTemporalSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.CorrectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` exited 0.  Its exact final output was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The plan output retained the pre-existing repository-wide
`source_hashes_match=false` and copied-source admission inventory; neither is a
failure of `make check` or of this continuation.
