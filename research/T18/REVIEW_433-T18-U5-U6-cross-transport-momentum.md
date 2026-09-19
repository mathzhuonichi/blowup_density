ACCEPT-WITH-NOTES

## What the lane claims

The worker report claims the two U5 fields and U6 `momentum` are proved with no
named inputs or gaps (`research/T18/REPORT_433.md:7-32,43-53`).  The claimed
statements agree with the reconciled Spec: the two cross-transport fields are
exactly the `Ioc`/`Ico`/pointwise statements at `research/T18/Spec.lean:1838-1852`,
and momentum is exactly the `Ioc`/`Ioo` residual equation at
`research/T18/Spec.lean:1770-1776`.  The cited paper proof has the same inserted
triple and pressure normalization at `paper/sections/03-torus.tex:312-320`,
the background equation and two cross terms at `:321-330`, and the cancellation
lemma gives an open neighborhood of the packet support at `:188-193,214-215`.
There is no silently added positivity or interval hypothesis in the three
public theorem types.

## What is in Lean

`CrossTransport.lean` proves the packet zero-slice fact at the exact activation
threshold (`formalization/NSFormalization/Section3/T18/CrossTransport.lean:30-43`),
uses the threaded `correction_cancels` neighborhood and
`Source.cross_advection_eq_zero` (`:66-79`; source lemma
`formalization/NSFormalization/Source/Insertion.lean:51-69`), and exports both
Spec-shaped fields (`CrossTransport.lean:81-95`).  The cancellation source field
really has the required open set and support inclusion
(`formalization/NSFormalization/Section3/T16/LocalPotential.lean:158-162`).

`Momentum.lean` derives the corrected-background equation from the reference
momentum field and the T17 force definition (`formalization/NSFormalization/Section3/T18/Momentum.lean:80-106`,
with the bridge at `formalization/NSFormalization/Section3/T17/Transport.lean:259-274`),
expands the residual with the two cross terms, removes both pressure gauges, and
exports the exact target at `Momentum.lean:108-190`.  The source expansion used is
the six-term `residual_add` theorem (`formalization/NSFormalization/Source/Insertion.lean:30-49`).
The Spec conversion probe checks all three exact field types and discharges them
from the canonical theorems (`research/T18/probes/u5_u6_closes.lean:239-275`).

The axioms file audits all 14 declarations (`research/T18/axioms_u5_u6.lean:3-16`);
the rerun printed only `[propext, Classical.choice, Quot.sound]` for each.
There are no `maxHeartbeats` overrides.  A source-only forbidden-token search
over the two new modules and the canonical probe/axioms file produced no output.
The diff against the stated base contains only additions plus the expected
status-record edit (`git diff --name-status origin/erenup/integration-section3...HEAD`);
no pre-existing Lean module is modified.

## Gaps

The report is honest that it does not construct a full `InsertionData` witness;
it records the remaining T15 U15/T17 U12 assembly dependency
(`research/T18/REPORT_433.md:43-45`).  I searched the entire Section 4 tree as
required:

```text
grep -rnE 'T15 U15|T17 U12|PeriodicInsertionAPI|InsertionData|ScalingAPI.*place|CorrectionAPI.*place' formalization/NSFormalization/Section4
(no matches)
```

The generic Section 4 insertion algebra does exist (`formalization/NSFormalization/Section4/R42/Assembly.lean:118-159`),
but it is not a missing torus witness.  The reviewer-only positive probe
`research/T18/probes/rev433_nonvacuity.lean:8-12` succeeds and shows that,
conditional on the threaded datum, `Ioc 0 (ε₀ data)` is nonempty via
`eps_pos`; this addresses interval vacuity without pretending that the full
T15/T17 construction exists.

The substantive negative probe widens the zero-past interval from
`t ≤ T - ε²` to `t ≤ T` (`research/T18/probes/rev433_negative.lean:14-21`).
It fails as expected, not by dropping an argument:

```text
../research/T18/probes/rev433_negative.lean:21:35: error: linarith failed to find a contradiction
data : InsertionData
ε t : ℝ
ht : t ≤ data.place.T
a✝ : data.place.T - ε ^ 2 < t
⊢ False
failed
```

The notes are report-only.  `REPORT_433.md:47` says “Four failed approaches”
but lists six bullets (`:48-53`): change “Four” to “Six”.  Also
`REPORT_433.md:41` names `58e94178` as the lane commit although the report itself
is on `324c1cb1`; identify the former as the implementation commit and the
latter as the report commit.  Finally, the current worktree predates newer
commits on `origin/erenup/integration-section3`; the optional contract gate
therefore fails before checking this lane because the worktree lacks the base's
stable `verification/Contracts/V1/AffineVariation.lean`:

```text
AssertionError: Removed stable specification: verification/Contracts/V1/AffineVariation.lean
```

This is base drift, not a verification change in this lane (the lane diff has
no `verification/` path).  Rerun `scripts/gates.sh`/`check_contracts.py` after
bringing the lane up to the current integration base.

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6` and one Lake process at a time.

```text
lake build NSFormalization.Section3.T18.CrossTransport NSFormalization.Section3.T18.Momentum
Build completed successfully (10021 jobs).

lake env lean ../formalization/NSFormalization/Section3/T18/CrossTransport.lean
(no output, exit 0)
lake env lean ../formalization/NSFormalization/Section3/T18/Momentum.lean
(no output, exit 0)
lake env lean ../research/T18/probes/u5_u6_closes.lean
(no output, exit 0)
lake env lean ../research/T18/axioms_u5_u6.lean
'NSFormalization.Section3.T18.periodicScaledPacket_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.packet_slice_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.crossTransport_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.crossTransport_background_advects_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.crossTransport_packet_advects_background' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.contDiff_two_of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.slice_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.slice_contDiff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.slab_temporal_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.pressureGradient_normalizePressureT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.residual_normalizePressureT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.reference_interior_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.corrected_background_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.momentum' depends on axioms: [propext, Classical.choice, Quot.sound]

make check
Ran 13 tests in 0.042s
OK
45 work items: ownership, contract registration and task cards consistent.
```

The required `scripts/gates.sh` run with
`BASE_REF=origin/erenup/integration-section3` completed the build and mutation
checks (`extra_axiom: rejected as required`, `weakened_hypothesis: rejected as
required`, `Mutation suite passed`) and then stopped at the base-drift
`AffineVariation.lean` assertion quoted above.  The explicit
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
reproduced the same assertion.  The positive non-vacuity probe passed with no
output; the widened-interval probe failed with the expected error above.

The lane is accepted because the three target statements are exact, the
canonical Lean proofs and Spec conversion build cleanly, and the only remaining
construction gap is explicitly outside U5/U6.  Fix the three report/gate notes
above when preparing the lane for integration.
