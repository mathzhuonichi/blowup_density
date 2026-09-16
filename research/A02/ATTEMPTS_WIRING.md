# Lane 213 — A01 → A02 wiring

## Proved without additional analytic inputs

`Section4/A02/MaximalWiring.lean` supplies:

- `exists_maximal'`: the exact maximal-existence conclusion, instantiated with
  `A01.localHorizon'` and `(A01.localCarrier ν a f hν ha hf).w`.
- `horizon_le_lifespan'` and `maximalLifespanR_pos`: the selected local horizon
  bounds the maximal lifespan below, and admissible data have positive lifespan.
- `IsMaximalSolution.exists_solution_after`: a classical representative with
  literal velocity/pressure equality on a horizon strictly beyond a presingular time.
- `ClassicalSolutionR.restart_datum`: every slice in `Ico 0 T` is in `initialClassR`.
- `restart_datum`: the exact draft API accessor on maximal solutions.

`maximal_unique` is unchanged. Restriction, normalization, the lifespan order
lemmas and reference lifespan are already exported by the existing A02 modules;
this lane does not duplicate them. The checked draft has its API in §3 (there is
no §4 heading), with `restart_datum`/`restart_force` at lines 512/525.

## Proof choices and negative results

Slice admissibility does not require lane 209's stronger `sobolev_smooth`:
`D01.contDiff_slice`, `ClassicalSolutionR.sobolev` and `.divergence` suffice.
The suggested `restart_datum` in `A02/Restrict.lean` was not present in this
checkout; the two slice accessors above close that omission.

The witness accessor uses the midpoint of a realized horizon and the requested
time. This keeps its chosen horizon strictly below the maximal lifespan, as
required by `IsMaximalSolution`; using the realized horizon itself would give
only a non-strict inequality.

Quantitative restart is not an accessor consequence of maximal existence.
See `../A04/ATTEMPTS_RESTART_WIRING.md`: the supplied fixed-force H⁷ theorem
has different quantifiers from the H¹-uniform `Restart` proposition.

## Validation

The new module compiles with no Lean output. `axioms_wiring.lean` prints exactly
`[propext, Classical.choice, Quot.sound]` for every new declaration and the
unchanged `maximal_unique`. It includes actual zero-data maximal existence and
a slice of `A04.zeroSol`; positivity is not dropped. Full gate results are in
`REPORT_213.md`. Only new files are added.
