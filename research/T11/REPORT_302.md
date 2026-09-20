# Lane 302 report — T11 canonical local theory module

## 1. What the module defines

`NSFormalization.Section3.T11.LocalTheory` now contains all reconciled T11
vocabulary outside the four public consumer API records:

- interval-local Sobolev paths, scalar pressure Laplacian, shorter-horizon and
  maximal-solution predicates, the squared-H² criterion, and concrete
  extension;
- `PeriodicLocalRegularity`, included because the reconciliation makes it
  shared vocabulary consumed by all four public APIs;
- the data-defined velocity/force means, `galileanMeanT`, displacement and the
  velocity/force/pressure Galilean transforms;
- the four forward unit-viscosity maps and three restoring maps.

The module imports T10 rather than copying it.  `convectionDivergenceT` and
`timeShiftT` are reducible aliases of their token-identical local Section 4
sources.  `SolvesBelowT`, `IsMaximalPeriodicSolution`, and
`squaredHTwoIntegralT` remain torus definitions because the existing sources
use, respectively, the distinct `ClassicalSolutionR` structure /
`maximalLifespanR` or the whole-space Sobolev norm.

## 2. Files

- `formalization/NSFormalization/Section3/T11/LocalTheory.lean`: canonical
  definitions-only module; no contracts, admissions, or instances.
- `research/T11/probes/api_on_canonical.lean`: all five reconciled structures
  elaborated over canonical T10/T11 declarations, plus local-source and
  contract-side `rfl` checks for both reused definitions.
- `research/T11/CANONICAL.md`: line-by-line declaration/source map and reuse
  decisions.
- `research/T11/IMPLEMENTATION_CANDIDATES.md`: one row per API field with an
  inspected declaration and its exact remaining gap.
- `research/T11/ATTEMPTS_CANONICAL.md`: failure ledger.
- `research/T11/REPORT_302.md`: this report.

## 3. Remaining proof gaps and error text

This lane intentionally supplies statements, not the T11 proofs.  The main
gaps exposed by the survey are:

1. conversion in both directions between `ClassicalSolutionT` and
   `Paper1.PeriodicLifespan.Flow`, including round trips and lifespan equality;
2. smooth-in-time Fourier datum paths and physical Poisson pressure recovery;
3. the bridge from `squaredHTwoIntegralT ≠ ⊤` to
   `PeriodicLocalLifespan.FiniteH2Energy`, plus higher-order Grönwall bounds and
   restart at an unattained endpoint;
4. the manuscript-strength fixed-force H¹ restart (the existing whole-space
   registered result narrows this to H⁷);
5. all Galilean mean-evolution and time-dependent translation proofs;
6. full solution/class/gauge/regularity preservation under viscosity scaling.

No Lean command or gate failed.  The only failed discovery subcommand was the
initial check for the not-yet-created directory; its exact diagnostic was:

```text
rg: formalization/NSFormalization/Section3/T11: No such file or directory (os error 2)
```

The first `lake build` replayed pre-existing dependency linter warnings but
returned success; both direct Lean invocations required by the lane produced
zero bytes of output.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.LocalTheory`
  — success (`Built NSFormalization.Section3.T11.LocalTheory`; 9896 jobs).
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/LocalTheory.lean`
  — exit 0, zero output.
- `cd verification && lake env lean ../research/T11/probes/api_on_canonical.lean`
  — exit 0, zero output.
- `make check`
  — exit 0; formalization-plan, contract-policy, contract architecture and
  work-queue checks all completed successfully.
