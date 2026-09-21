# Report 297 — canonical T12 mean-zero calculus module

## What the module defines

`NSFormalization.Section3.T12.MeanZeroCalculus` provides the complete new T12
definitions-only layer before the API: the integrable scalar periodic datum and
its total extended Sobolev norm; scalar/vector integer-order membership;
mean-zero homogeneous membership; smooth periodic fields; the generic physical
torus `L^p` extended norm; the registered lift, gradient-tensor, and Laplacian
spellings; and the coefficientwise periodic Lambda graph.  T10 vocabulary is
imported from its canonical module, and the three derivative spellings reuse
their local Section 4 canonical sources through reducible aliases.

## Files

- `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean` — the
  definitions-only canonical module, with no contract or binding import.
- `research/T12/probes/api_on_canonical.lean` — the verbatim reconciled
  Type-valued API statement over the canonical declarations, plus `rfl` checks
  for all three reused derivative declarations against both local and
  registered sources.
- `research/T12/CANONICAL.md` — spec-line/declaration/source map and reuse
  ledger.
- `research/T12/ATTEMPTS_CANONICAL.md` — failure ledger.
- `research/T12/REPORT_297.md` — this report.

## Gaps and encountered errors

There is no mathematical or elaboration gap in the requested definitions or
API statement.  No Lean command failed, so there is no error text to report.
The API remains a probe statement by design; the later T12 proof lanes must
construct an inhabitant.  The canonical module declares no instances and thus
does not duplicate the imported torus measure instances.

## Commands and results

- `. ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.MeanZeroCalculus` from `verification/`: passed; only pre-existing upstream warnings were replayed.
- `. ../scripts/lean-env.sh && lake env lean ../formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean` from `verification/`: passed with zero output.
- `. ../scripts/lean-env.sh && lake env lean ../research/T12/probes/api_on_canonical.lean` from `verification/`: passed with zero output.
- `. scripts/lean-env.sh && make check` from the worktree root: passed (13 policy tests; 45 work items consistent).  The pre-existing copied-source audit still reports `Paper1/BoundaryCorollary.lean:90` in its informational manifest, but the gate exits 0.
