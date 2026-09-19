# Lane 484 report — T23 U5 domain/zero-extension comparison

## 1. Statements

`NSFormalization.Section3.T23.domain_zeroExt_comparison` proves the exact U5
field.  Given the canonical T22 `BoundedDomainNormAPI`, the domain openness and
prescribed interior ball, U3's exact `forceDifference_mem` field type, and U4's
exact all-time pointwise support field type, it proves

```lean
∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
  domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
      zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ∧
  zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
      ENNReal.ofReal C *
        domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z)
```

The fixed compact set is `closure (Metric.ball c R)`.  The T22 constant is
chosen once after `s` and before both time and `ε`.  Both inequalities are
integrated over `Ioi 0` by monotonicity; the upper side uses constant
multiplication for `ℝ≥0∞`, so infinite norms remain valid.

Supporting the field:

- `tsupport_zeroExtension_subset_of_pointwise_support` converts U4's
  pointwise support statement to T22's literal-zero-extension premise.
- `contDiffOn_slice_of_memForceOmega` extracts every positive-time smooth
  spatial slice from U3's force-class membership.
- `domainForceDifference_orderZero` applies the T22 order-zero field to the
  actual force difference, identifying it with the restricted physical
  `L²(Ω)` norm.
- Five `rfl` theorems expose the exact definitions of
  `domainEnergyEssSup`, `domainEnergyGradient`, `domainEnergyENorm`,
  `domainForceSobolevENorm`, and `zeroExtForceSobolevENorm`.
- The closure probe checks fieldwise conversions in both directions between
  the registered T22 contract copy and the canonical proof-side three-field
  record, with round trips and shared-definition `rfl` bridges.

## 2. Files

- `formalization/NSFormalization/Section3/T23/DomainNorms.lean`: five exact
  norm-definition bridges.
- `formalization/NSFormalization/Section3/T23/DomainComparison.lean`: support,
  slice-smoothness, order-zero, and integrated comparison theorems.
- `research/T23/probes/T23-U5-domain-comparison_closes.lean`: exact norm/API
  transports and the U5 field instantiated only from the threaded U3/U4 facts.
- `research/T23/axioms_T23-U5-domain-comparison.lean`: all nine production
  declarations audited.
- `research/T23/ATTEMPTS_T23-U5-domain-comparison.md`: verbatim failed
  elaborations and the successful proof route.
- `research/T23/T23_SPLIT.md`: U5 status marked complete.
- `research/T23/REPORT_484.md`: this report.

## 3. Gaps and exact errors

There is no mathematical gap inside U5.  Final assembly must supply the already
assigned U3 force-class membership and U4 fixed-support facts; they are exact
upstream field types, not conclusion-shaped assumptions.  This lane does not
claim U3, U4, U6, or the final T23 construction.

Two resolved development errors are recorded in full in the attempts file.
The compactness proof first tried to rewrite at an applied theorem expression:

```text
error: NSFormalization/Section3/T23/DomainComparison.lean:69:48: Unexpected term `prescribed_closedBall_compact`; expected single reference to variable
```

The probe initially selected the registered historical field abbreviation
instead of the canonical raw placement field:

```text
../research/T23/probes/T23-U5-domain-comparison_closes.lean:88:47: error: Application type mismatch: The argument
  u
has type
  VelocityField
but is expected to have type
  NavierStokes.ProblemStatement.VelocityField
in the application
  DomainPlacementData u
```

Both are fixed.  No error remains in any delivered Lean file.

## 4. Commands and results

Every Lean command sourced `scripts/lean-env.sh`; every Lake invocation ran
from `verification/` with `LEAN_NUM_THREADS=6`.

- The requested Boundary/T22/T23 dependency closure built first: exit 0,
  10,142 jobs, dependency warnings only.
- `lake build NSFormalization.Section3.T23.DomainNorms`: exit 0, 0 errors.
- `lake build NSFormalization.Section3.T23.DomainComparison`: exit 0, 0 errors.
- `lake env lean` on each new implementation module: exit 0, zero output.
- `lake env lean ../research/T23/probes/T23-U5-domain-comparison_closes.lean`:
  exit 0, zero output.
- `lake env lean ../research/T23/axioms_T23-U5-domain-comparison.lean`: exit 0;
  all nine lines list exactly `[propext, Classical.choice, Quot.sound]`.
- Targeted forbidden-token, heartbeat-override, unsafe-import scans and
  `git diff --check`: zero output.
- `make check`: exit 0; 54 registered contracts, 13 policy tests pass, and 45
  work items are consistent.  It still prints the repository's historical
  copied-umbrella `Paper1/BoundaryCorollary.lean:90` admission and
  `source_hashes_match: false`; neither is in this lane's imports or changes.
