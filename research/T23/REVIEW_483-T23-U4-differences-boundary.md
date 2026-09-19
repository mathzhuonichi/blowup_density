ACCEPT-WITH-NOTES

## 1. What the lane claims

The lane claims conditional suppliers for exactly the eight U4 fields:
`collar_agreement`, `noSlip_preserved`, `velocityDifference_divFree`,
`diffSupportRadius`, `diffSupportRadius_pos`, `velocityDifference_support`,
`diffSupport_in_chart`, and `forceDifference_spatialSupport`
(`research/T23/REPORT_483.md:5-24`).  It additionally claims the downstream
closed-support result for the literal zero extension
(`research/T23/REPORT_483.md:26-34`).

These are the mathematics requested by the brief.  The paper requires a
prescribed interior ball and retained no-slip values
(`paper/sections/03-torus.tex:646`), a fixed boundary collar and interior force
support (`paper/sections/03-torus.tex:654-655`), and one fixed compact support
also after `T` (`paper/sections/03-torus.tex:661-663`).  The canonical field
types say exactly:

- fixed-ball collar agreement and no-slip on `frontier Ω`
  (`formalization/NSFormalization/Section3/T23/Boundary.lean:268-277`);
- divergence of the actual velocity difference, a positive real radius, and
  one `tsupport` ball (`formalization/NSFormalization/Section3/T23/Boundary.lean:342-360`);
- containment of that ball in the fixed chart and pointwise all-real-time force
  support in its closure (`formalization/NSFormalization/Section3/T23/Boundary.lean:364-377`).

Those types agree with the research spec
(`research/T23/Spec.lean:823-832`, `research/T23/Spec.lean:897-932`).  In
particular, the time intervals remain `Ico 0 T`, the scale interval remains
`Ioc 0 ε₀`, the force conclusion quantifies every `t : ℝ`, and the spatial
sets have not been widened or replaced.

The cross-lane hypotheses are honest.  The velocity and force formulas in the
supplier theorems (`formalization/NSFormalization/Section3/T23/Differences.lean:208-210`,
`:337-339`) are the exact U3 field types
(`formalization/NSFormalization/Section3/T23/Boundary.lean:194-196`, `:209-211`).
Likewise the smoothness and incompressibility inputs at
`formalization/NSFormalization/Section3/T23/Differences.lean:272-276` are the
exact upstream fields at `formalization/NSFormalization/Section3/T23/Boundary.lean:229-245`.
None is conclusion-shaped.

The remaining support premises are genuine raw supplier data: sharp correction
support is in `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:289-291`,
correction-force support is at `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:382-385`,
and the scaled packet/force transport lemmas are at
`formalization/NSFormalization/Section3/T15/Placement.lean:128-157` and
`:207-224`.  The auxiliary carrier-ball premise is derivable from the canonical
`Kstar_compact` and `carrier_subset` fields; the checked derivation is
`research/T23/probes/rev483_nonvacuity.lean:10-19`.  It is therefore neither a
gap nor a named analytic input.

## 2. What is in Lean

All reported declarations exist.  The eight field suppliers are:

- `diffSupportRadius` and its positivity theorem at
  `formalization/NSFormalization/Section3/T23/Differences.lean:25-45`;
- `diffSupport_in_chart` at
  `formalization/NSFormalization/Section3/T23/Differences.lean:75-102`;
- `velocityDifference_support` at
  `formalization/NSFormalization/Section3/T23/Differences.lean:167-192`;
- `collar_agreement` at
  `formalization/NSFormalization/Section3/T23/Differences.lean:197-225`;
- `noSlip_preserved` at
  `formalization/NSFormalization/Section3/T23/Differences.lean:230-261`;
- `velocityDifference_divFree` at
  `formalization/NSFormalization/Section3/T23/Differences.lean:266-291`;
- `forceDifference_spatialSupport` at
  `formalization/NSFormalization/Section3/T23/Differences.lean:329-371`.

The worker's conformance probe checks every canonical field by `exact`
(`research/T23/probes/T23-U4-differences-boundary_closes.lean:42-97`), and the
zero-extension corollary is stated and consumed at
`formalization/NSFormalization/Section3/T23/Differences.lean:391-411` and
`research/T23/probes/T23-U4-differences-boundary_closes.lean:99-105`.
The claimed count of 21 public definitions/theorems is correct
(`research/T23/axioms_T23-U4-differences-boundary.lean:5-25`).

The construction is non-vacuous on the intended upstream inputs.
`differenceThreshold_pos` proves positivity from the U3 base threshold and the
actual positive cutoff radius
(`formalization/NSFormalization/Section3/T23/Differences.lean:56-64`), and the
reviewer probe exhibits the upper endpoint as an element of the resulting
`Ioc` interval (`research/T23/probes/rev483_nonvacuity.lean:21-28`).  There is no
`ENNReal.toReal` totalization, empty-interval trick, unused result binder, or
hidden change to the conclusion.  Direct typechecking produces no warning from
the module.

The substantive negative check triples the chart-support radius while leaving
all premises intact (`research/T23/probes/rev483_triple_radius_mutation.lean:12-19`).
The original proof no longer has the required type, exactly as expected; this
is a changed conclusion, not a dropped argument.

## 3. Gaps and notes

There is no U4 proof gap.  As authorized by the lead note, U9 must instantiate
the exact threaded U3 formula/smoothness/incompressibility fields and choose the
shrunk threshold; this conditionality is already stated in
`research/T23/T23_SPLIT.md:109-119`.  The report and attempts file make no
"not in the tree" or missing-lemma claim, so the requested whole-Section4 grep
condition has no instance to audit.  The scan for such claims returned no
matches.

Two exact one-line record fixes are required:

1. Delete the extra blank line `research/T23/REPORT_483.md:118`; it is the sole
   reason the reported `git diff --check` result at `research/T23/REPORT_483.md:117`
   is currently false.
2. At `research/T23/T23_SPLIT.md:113`, replace “the raw I03 `carrier_subset`
   clause” with “a carrier-ball bound derived from `place.Kstar_compact` and
   `place.carrier_subset`”; the supplier theorem accepts that derived bound
   explicitly rather than consuming `carrier_subset` directly.

The multiple-merge-base origin diff includes the inherited U-CAN files, but the
lane-only diff from merge commit `b8ef83ae` shows `Differences.lean` as the sole
Lean implementation file and shows no modified pre-existing Lean module.  No
file under `verification/` was touched, so the conditional `scripts/gates.sh`
and standalone `check_contracts.py --base-ref origin/erenup/integration-section3`
gates do not apply.  (`make check` still ran the ordinary contract checker.)

## 4. Commands and results

Every Lean command sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
every Lake command ran from `verification/`.

### Build and direct typechecks

`lake build NSFormalization.Section3.T23.Boundary` exited 0.  Last output line:

```text
Build completed successfully (10087 jobs).
```

`lake build NSFormalization.Section3.T23.Differences` exited 0.  The first and
last output excerpts (middle consists only of replayed upstream warnings) were:

```text
⚠ [8778/8836] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

[... middle omitted by reviewer ...]
Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10083/10089] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10089 jobs).
```

These each exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T23/Differences.lean
lake env lean ../research/T23/probes/T23-U4-differences-boundary_closes.lean
lake env lean ../research/T23/probes/rev483_nonvacuity.lean
```

### Axiom audit

`lake env lean ../research/T23/axioms_T23-U4-differences-boundary.lean` exited 0
with the following complete output; every declaration has exactly the required
three axioms:

```text
'NSFormalization.Section3.T23.diffSupportRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.cutoffRadius_lt_diffSupportRadius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.packetRadius_lt_diffSupportRadius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.diffSupportRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.differenceThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.differenceThreshold_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.differenceThreshold_le_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.diffSupport_in_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.slice_tsupport_subset_spacetime_tsupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.correction_slice_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.affineCarrier_subset_commonBall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.scaledPacket_slice_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.velocityDifference_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.collar_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.noSlip_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.velocityDifference_divFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.correctionForce_slice_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.scaledForce_slice_support_chart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.forceDifference_spatialSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.zeroExtension_tsupport_subset_of_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.forceDifference_zeroExtension_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Negative check

`lake env lean ../research/T23/probes/rev483_triple_radius_mutation.lean` exited
1 with the expected changed-conclusion error:

```text
../research/T23/probes/rev483_triple_radius_mutation.lean:19:2: error: Type mismatch
  diffSupport_in_chart place base cutoffRadius packetRadius hcutoff
has type
  ∀ ε ∈ Ioc 0 (differenceThreshold place base cutoffRadius packetRadius),
    ball place.x₀ (ε * diffSupportRadius cutoffRadius packetRadius) ⊆ ball place.chartCenter place.chartRadius
but is expected to have type
  ∀ ε ∈ Ioc 0 (differenceThreshold place base cutoffRadius packetRadius),
    ball place.x₀ (3 * ε * diffSupportRadius cutoffRadius packetRadius) ⊆ ball place.chartCenter place.chartRadius
```

### Repository check

`make check` exited 0.  First and last output excerpts:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 732,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 54,
[... middle omitted by reviewer ...]
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.047s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The historical `Paper1/BoundaryCorollary.lean:90` token is outside this lane and
is not imported by `Differences.lean`; the targeted lane scan below is clean.

### Hygiene and diff checks

The following scans produced no output (`rg` exit 1 means no matches):

```text
rg -n -w 'sorry|admit|axiom|native_decide' formalization/NSFormalization/Section3/T23/Differences.lean research/T23/probes/T23-U4-differences-boundary_closes.lean research/T23/axioms_T23-U4-differences-boundary.lean
rg -n 'set_option maxHeartbeats|Paper1\.BoundaryCorollary' formalization/NSFormalization/Section3/T23/Differences.lean research/T23/probes/T23-U4-differences-boundary_closes.lean research/T23/axioms_T23-U4-differences-boundary.lean
```

`git diff --name-status b8ef83ae..HEAD` produced:

```text
A	formalization/NSFormalization/Section3/T23/Differences.lean
A	research/T23/ATTEMPTS_T23-U4-differences-boundary.md
A	research/T23/REPORT_483.md
M	research/T23/T23_SPLIT.md
A	research/T23/axioms_T23-U4-differences-boundary.lean
A	research/T23/probes/T23-U4-differences-boundary_closes.lean
```

`git diff --name-only --diff-filter=M b8ef83ae..HEAD -- '*.lean'` and
`git diff --name-only b8ef83ae..HEAD -- verification/` both exited 0 with zero
output.  The required origin comparison also ran; it warned that there are
multiple merge bases and listed inherited U-CAN additions as well as this lane.

Finally, `git diff --check b8ef83ae..HEAD` currently exits 2:

```text
research/T23/REPORT_483.md:118: new blank line at EOF.
```

That reproduces note 1 above and is the only reason for
`ACCEPT-WITH-NOTES` rather than `ACCEPT`.
