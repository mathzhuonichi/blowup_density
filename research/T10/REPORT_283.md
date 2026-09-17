# Report 283 — canonical T10 periodic-data module

## What the module defines

`NSFormalization.Section3.T10.PeriodicData` now provides the complete amended
T10 definitions-only layer: periodicity; real weighted `lp` coefficient
carriers; inhomogeneous and homogeneous datum predicates and extended norms;
mean/zero-mode objects; derivative, solenoidal, Leray, and reweight predicates;
Sobolev paths and force norms; initial/force classes; pressure normalization;
`ClassicalSolutionT`; lifespan, regularity, breakdown, and relative-density
objects; and both physical and coefficient energy norms.  The five existing
`Paper1.TorusCube` objects are reused definitionally rather than copied.

## Files

- `formalization/NSFormalization/Section3/T10/PeriodicData.lean` — canonical
  module, with no contract or binding import.
- `research/T10/probes/api_on_canonical.lean` — the full amended
  `TorusDataAPI` statement over the canonical module plus five `rfl` reuse
  checks.
- `research/T10/CANONICAL.md` — declaration/source map and reuse ledger.
- `research/T10/ATTEMPTS_CANONICAL.md` — exact failed diagnostics and their
  resolutions.
- `research/T10/REPORT_283.md` — this report.

## Gaps and encountered errors

There is no mathematical or elaboration gap in the requested definitions or
API statement.  The brief's `verification/Bindings/Data.lean` path does not
exist; bridge evidence is distributed across the files listed in
`CANONICAL.md`.  The first unconstrained polymorphic `torusLift` alias failed
with `don't know how to synthesize implicit argument E`; the exact full error is
preserved in `ATTEMPTS_CANONICAL.md`, and the explicitly typed reducible alias
passes its `rfl` identity check.  Lake discovered the new Section 3 module, so
no lakefile edit was needed.

## Commands and results

- `. ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PeriodicData` from `verification/`: passed; only replayed upstream warnings.
- `. ../scripts/lean-env.sh && lake env lean ../formalization/NSFormalization/Section3/T10/PeriodicData.lean` from `verification/`: passed with zero output.
- `. ../scripts/lean-env.sh && lake env lean ../research/T10/probes/api_on_canonical.lean` from `verification/`: passed with zero output.
- `. scripts/lean-env.sh && make check` from the worktree root: passed (13 policy tests; 45 work items consistent).  The pre-existing copied-source audit still reports `Paper1/BoundaryCorollary.lean:90` in its informational manifest, but the gate exits 0.
