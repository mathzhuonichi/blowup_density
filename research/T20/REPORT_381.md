# Lane 381 — T20 canonical statement report

## 1. What is restated

`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean` restates
Proposition `prop:critical`'s reconciled statement vocabulary over the
canonical T10/T11/T12 modules. It contains 17 T20 helper definitions, the
23-field `CriticalRegularityTAPI` (12 constant/positivity/shrinking fields and
11 mathematical estimate/regularity fields), and the definition-level
statement `criticalRegularityStatement := Nonempty CriticalRegularityTAPI`.
This is a statement lane: it constructs no API inhabitant and proves none of
the mathematical fields.

## 2. Lean files and conformance

- `research/T20/probes/api_on_canonical.lean` copies the T20 part of the Spec,
  checks all 17 helper definitions by `rfl`, converts the 23-field structure in
  both directions fieldwise, proves both round trips by `rfl`, and compares the
  two statement definitions through those conversions.
- `research/T20/axioms_canonical.lean` audits every declaration of the
  canonical module. Every printed dependency set is exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T20/ATTEMPTS_CANONICAL.md` records the canonicalization and the
  structure-exception decisions. No existing Lean module was edited.

## 3. H¹-ball finding

`research/T20/H1_CHECK.md` records the complete grep. The only occurrences of
`periodicSobolevENorm 1` are `Spec.lean:402` in copied
`PeriodicContinuationAPI.restart` and `Spec.lean:437` in copied
`restartBeyond`. Proving those manuscript fields themselves would require the
named open H¹ restart predicates. They are not fields or dependencies of
`CriticalRegularityTAPI`. T20's present criterion route uses
`higherOrderBound` at `m = 3` and the ball-free `extendsBeyond` /
`lifespanInfiniteOfLocallyFinite` fields, so the proved H³ continuation package
suffices and `PeriodicRestartH1` is not needed.

## 4. Verification

The following commands were run from `verification/` after sourcing
`scripts/lean-env.sh`:

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalRegularity`
- `lake env lean ../formalization/NSFormalization/Section3/T20/CriticalRegularity.lean`
- `lake env lean ../research/T20/probes/api_on_canonical.lean`
- `lake env lean ../research/T20/axioms_canonical.lean`
- `make check`

All completed successfully. The direct module elaboration produced zero
output; the probe and axiom audit printed only the expected standard-three
axiom reports.
