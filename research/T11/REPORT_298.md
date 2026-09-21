# T11 reconciled specification report — lane 298

## 1. What theorem was specified

`research/T11/Spec.lean` states the periodic half of Proposition `prop:local`
on `T³` (`02-preliminaries.tex:75-120`) together with Appendix A's common
all-order local regularity, uniqueness and maximal gluing, the exact
squared-`H²` continuation criterion, the fixed-force uniform `H¹` restart,
the data-defined Galilean mean reduction, and positive-viscosity rescaling
(`appendix-a-local-theory.tex:60-158`). It also includes the maximal-lifespan
wrapper consumed at `03-torus.tex:490-502`.

The statement follows the binding reconciliation: `PeriodicLocalRegularity`
has 3 fields, `PeriodicLocalTheoryAPI : Type` has 8,
`PeriodicContinuationAPI : Prop` has 5,
`PeriodicMeanReductionAPI : Prop` has 6, and
`PeriodicViscosityRescalingAPI : Prop` has 4. The continuation criterion is
over `SolvesBelowT`; maximal uniqueness is only at presingular times; the
lifespan wrapper uses the load-bearing non-strict endpoint condition `≤`.

## 2. What Lean now contains

The spec provides all reconciled T11-local definitions, including
`IsPeriodicSobolevPathOn`, `convectionDivergenceT`,
`scalarSpatialLaplacianT`, `SolvesBelowT`,
`IsMaximalPeriodicSolution`, `squaredHTwoIntegralT`, `timeShiftT`,
`ExtendsBeyondT`, the data-defined `galileanMeanT a f`, all Galilean
transforms, and the unit/restore viscosity transforms.

The Galilean force subtracts `forceMeanT f`, not a totalized derivative, and
all transforms depend on the known data `(a,f)` rather than arbitrary values
of a total solution field outside its lifespan. Every API field has its paper
line, exact quantifier-order note, and a non-vacuity explanation. Criterion
norms and integrals remain `ℝ≥0∞`-valued with explicit finiteness hypotheses.

The T10 declarations through `breakdownSetT` are copied verbatim from the
amended `research/T10/Spec.lean`, with 45 per-declaration source-line markers.
The six blind-draft provenance files are copied byte-for-byte from lanes 288
and 289. `COMPARISON.md` merges their clause tables, records every lead ruling,
copies the reconciliation's proof dependencies, and lists owner questions.

Four definitional checks elaborate by `rfl`: the two registered
`CompletedDenseVia` abbreviations, the Section 4
`convectionDivergence` body, and the Section 4 `timeShift` body.

## 3. Remaining gaps

This is a specification lane: none of the analytic, gluing, pressure,
Galilean, or viscosity claims is proved here. The complete proof-dependency
list is in `COMPARISON.md`.

The manuscript-strength `H¹` restart is intentionally retained. Section 4
could prove only the explicitly versioned fixed-force `H⁷` narrowing; if the
periodic proof hits the same obstruction, the owner must choose an explicit
T11 V2 narrowing rather than silently weakening this statement.

The registered `T01.torus_data` file exists on lane 293 (`fc21ef3`) but is not
present in lane 298's base commit. Therefore this research spec uses the
reconciliation's fallback copy policy instead of importing
`Contracts.V1.TorusData`; no existing module was added or edited. Integration
should replace the registered data-tier copies with that import once lane 293
is present, while retaining the deferred T11 solution-class declarations.

The instruction mentioning `q : ℝ≥0∞`, `q=1∨q=2`, and
`criticalOrder q.toReal` has no corresponding T11 clause in either blind draft
or the binding reconciliation. In accordance with the ruling that nothing
absent from both drafts is added, those later density parameters are not
invented in these five APIs.

## 4. Commands run and results

- `cd verification && lake env lean ../research/T11/Spec.lean` — exit 0,
  no output, 0 errors.
- Four in-file `example ... := rfl` checks — all accepted by the same Lean run.
- `diff` of the marked-copy block (after removing only marker comments) against
  `research/T10/Spec.lean:46-383` — no differences.
- `git hash-object` comparison of each provenance file against `git show` from
  `erenup/288-SPEC-t11-draft-a` or `erenup/289-SPEC-t11-draft-b` — all six
  report `MATCH`.
- Placeholder scan for `sorry`, `admit`, `axiom`, `True`, and existential
  `True` patterns — no findings.
- `git diff --check` — clean.
- `make check` — exit 0; contract-policy and work-queue checks passed (the
  pre-existing formalization-plan audit still reports
  `source_hashes_match: false` without failing the gate).
- `make test` — exit 0; all registered tests built, with only pre-existing
  upstream/local linter warnings.
- `make test-mutations` — exit 0; mutation suite passed.
