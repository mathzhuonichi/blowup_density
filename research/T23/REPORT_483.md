# Lane 483 — T23 U4 localized differences and boundary retention

## 1. Statements

`NSFormalization.Section3.T23.Differences` closes all eight U4 fields over the
explicit hypotheses assigned to this parallel lane:

- `collar_agreement` and `noSlip_preserved` use the threaded U3 velocity
  formula, actual local-correction support, scaled packet support, and the
  prescribed-ball/frontier separation lemma.
- `velocityDifference_divFree` consumes the threaded U3 closed-slab
  smoothness and incompressibility facts directly; it does not require an
  inserted `ClassicalSolutionOmega` package.
- `diffSupportRadius` is `max R_cutoff R_packet + 1`, hence is strictly larger
  than both supplier radii and positive from the actual positive cutoff radius.
- `differenceThreshold` shrinks an already compatible positive threshold so
  `ball x₀ (ε * diffSupportRadius)` lies in the fixed chart ball even at the
  closed upper endpoint.  `velocityDifference_support` rewrites the U3 formula
  and explicitly uses `tsupport_add` followed by the correction and scaled
  packet summand bounds.
- `forceDifference_spatialSupport` holds for every real time, including after
  `T`: the correction-force branch uses the lane-477 I02 support theorem and
  sharp correction support, while the scaled-force branch uses the packet's
  compact positive-time support and placement's all-time force projection.

The additional theorem `forceDifference_zeroExtension_support` proves

```text
tsupport (zeroExtension Ω (fun x => force ε (t,x) - g (t,x)))
  ⊆ closure (ball place.chartCenter place.chartRadius)
```

for every real `t`.  The proof uses `closure_minimal` and
`isClosed_closure`; the zero extension vanishes definitionally outside `Ω`.

## 2. Files

- `formalization/NSFormalization/Section3/T23/Differences.lean`: 21 public
  definitions/theorems, including the eight U4 field suppliers and the
  downstream zero-extension support corollary.
- `research/T23/probes/T23-U4-differences-boundary_closes.lean`: one `by exact`
  consumer for each canonical `BoundaryInsertionAPI` U4 field, instantiated at
  the explicit U3 formulas/regularity facts, plus the zero-extension consumer.
- `research/T23/axioms_T23-U4-differences-boundary.lean`: audits all 21 public
  declarations.
- `research/T23/ATTEMPTS_T23-U4-differences-boundary.md`: four resolved failures
  with exact diagnostics.
- `research/T23/T23_SPLIT.md`: U4 marked conditionally complete.
- `research/T23/REPORT_483.md`: this four-part report.

No existing Lean module was edited, no parallel-lane module was imported, and
no record already owned by Boundary/Placement/LocalCorrection/DomainSolution
was restated.

## 3. Gaps and exact error text

There is no open U4 proof gap.  The result is conditional exactly as planned:
U9 must instantiate the threaded U3 velocity/force formulas, smoothness and
incompressibility facts, and select `differenceThreshold` from their common
base threshold.  Lane 483 neither imports nor assumes a package from parallel
lane 482.

All development failures were resolved and are recorded verbatim in the
ATTEMPTS file.  The key diagnostics were:

```text
Unknown constant `Filter.nhds`
```

```text
Application type mismatch: The argument
  hxnot
has type
  x ∉ tsupport fun y => velocity ε (t, y) - v (t, y)
but is expected to have type
  v (t, x) ∉ tsupport (HSub.hSub (velocity ε (t, x)))
```

```text
has type
  spatialDivergence (velocity ε) t x - spatialDivergence reference.velocity t x = 0
but is expected to have type
  ∑ x_1, ((spatialDerivative (fun z => velocity ε z - reference.velocity z) t x)
    (coordinateVector x_1)).ofLp x_1 = 0
```

```text
../research/T23/probes/T23-U4-differences-boundary_closes.lean:63:0:
warning: declaration uses `sorry`
```

The last warning was eliminated by explicitly binding the two threaded U3
hypotheses in that probe example; the final probe has zero output.  Targeted
source scans found no proof admission, `native_decide`, heartbeat override, or
import of `Paper1.BoundaryCorollary` in the delivered Lean files/import area.

## 4. Commands and results

Every Lean shell sourced `scripts/lean-env.sh`; every Lake command ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- Built the requested supplier closure first, including `Boundary`,
  `Placement`, `LocalCorrection`, `SpatialExtension`,
  `LocalCorrectionBridge`, `StatementRepair`, `DomainSolution`,
  `NoSlipEnergy`, `DifferenceEnergy`, and `BoxIntegration`: exit 0.
- `lake build NSFormalization.Section3.T23.Differences`: exit 0, 10089 jobs;
  only replayed upstream warnings.
- `lake env lean` on `Differences.lean`: exit 0, zero output.
- `lake env lean` on the exact-field probe: exit 0, zero output.
- `lake env lean` on the axiom file: exit 0; every one of 21 declarations
  prints exactly `[propext, Classical.choice, Quot.sound]`.
- `make check`: exit 0; 54 registered contracts, 13 policy tests, and 45
  consistent work items.  As in preceding T23 reports, the broad inventory
  still prints the historical `Paper1/BoundaryCorollary.lean:90` admission and
  `source_hashes_match: false`; neither is in this module's imports or changes.
- Targeted forbidden-token/unsafe-import scans: no output.
- `git diff --check`: exit 0.
