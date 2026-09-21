# Report 299 — canonical T13 localization module

## What the module defines

`NSFormalization.Section3.T13.Localization` provides all eleven new T13
definitions before the API: the fixed fundamental cube, coordinate-ball
support, lattice embedding and periodization, the singular radial and
periodic kernels, the concrete fractional constant, the nonzero lattice tail,
the whole-space and torus Gagliardo difference integrals, and the physical
Hilbert--Schmidt gradient extended norm.  T10 vocabulary is imported from its
canonical module.  The whole-space homogeneous norm needed by the API is
reused from its local Section 4 D01 source.

## Files

- `formalization/NSFormalization/Section3/T13/Localization.lean` — the
  definitions-only canonical module, with no contract/binding import and no
  instance declaration.
- `research/T13/probes/api_on_canonical.lean` — the verbatim reconciled
  six-field Prop-valued API statement over the canonical declarations, plus
  `rfl` checks for the reused Section 4 field type and homogeneous norm.
- `research/T13/CANONICAL.md` — spec-line/declaration/source map and reuse
  ledger.
- `research/T13/ATTEMPTS_CANONICAL.md` — failure ledger.
- `research/T13/REPORT_299.md` — this report.

## Gaps and encountered errors

There is no mathematical or elaboration gap in the requested definitions or
API statement.  No command failed, so there is no error text to report.  The
six theorem clauses remain a probe structure by design; later T13 proof lanes
must construct an inhabitant.

## Commands and results

- `. ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.Localization` from `verification/`: passed; only pre-existing upstream warnings were replayed.
- `. ../scripts/lean-env.sh && lake env lean ../formalization/NSFormalization/Section3/T13/Localization.lean` from `verification/`: passed with zero output.
- `. ../scripts/lean-env.sh && lake env lean ../research/T13/probes/api_on_canonical.lean` from `verification/`: passed with zero output.
- `. scripts/lean-env.sh && make check` from the worktree root: passed.
