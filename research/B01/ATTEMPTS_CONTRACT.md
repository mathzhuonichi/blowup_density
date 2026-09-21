# B01 contract registration — attempts and decisions (lane 071)

Registering `B01.bochner_partial`, the **proved part** of `research/B01/Spec.lean`'s
`BochnerApproxAPI`, as a version-1 lemma-bundle contract:
`verification/Contracts/V1/BochnerPartial.lean` + `Bindings/BochnerPartial.lean`
+ `Tests/BochnerPartial.lean` + `verification/contracts.json` + the B01 work item.

## What went in, what stayed out

Fields registered (types copied verbatim from `Spec.lean:191-338`): `χ`,
`chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range`; `spatialApprox`;
`temporalApprox`; `separatedAssembly`; `approxCompact`;
`completionRepresentative`/`completionSurjective`/`completionNorm`/`completionCongr`;
`compactSubsetForceR`.

Excluded, and recorded in the module docstring + registry `scope` as gaps:

* `schwartzApprox` (`Spec.lean:219`) and `cutoffApprox` (`Spec.lean:234`) — the
  two fidelity-only intermediate spatial displays of stages 1 and 2. They are not
  proved in the tree; `spatialApprox` is the only spatial input `approxCompact`
  consumes, so omitting them weakens nothing a consumer needs. Because they are
  the only fields that mention the spec-local defs `scaledCutoff` (`Spec.lean:123`)
  and `schwartzVector` (`Spec.lean:132`), **neither def is restated** in the
  contract — the task-brief list of "defs it needs" is narrowed accordingly.
* `SeparatedCompactDense` (`Spec.lean:405`, unit 10) — derivable from
  `temporalApprox + spatialApprox + separatedAssembly`; kept as a `def` in the
  spec, not a field here.

## Which vocabulary is Data's and which is spec-local

Confirmed against `verification/Contracts/V1/Data.lean`: `SpatialField` (:99),
`SpaceTimeField` (:104), `forceTimeMeasure` (:118), `IsSobolevDatum` (:160),
`IsSobolevPath` (:174), `bochnerDatumENorm` (:205), `MemBochnerDatum` (:212),
`MemForceR`/`forceClassR` (:544/:553), `MemForceCompact`/`forceClassCompact`
(:559/:563), `CompletedDense` (:743) are all in Data and used directly (opened,
not restated). Only `separatedField`, `separatedPath` (`Spec.lean:140,147`) and
`bochnerSpace` (`Spec.lean:158`) have no Data declaration; those three are
restated token-for-token in the contract and bridged by `rfl` in the binding to
`NSFormalization.Section4.B01.{separatedField,separatedPath,bochnerSpace}`.

## Binding shape (zero `by` blocks)

Each field is `:= Local.theorem`, relying on the same definitional equalities the
conformance files `research/B01/axioms_u{123,68,7}.lean` already exercise:

* direct assignment: `spatialApprox`, `temporalApprox`, `approxCompact`, the four
  `completion*` (local theorems already carry the field shapes);
* eta with `J` made explicit: `separatedAssembly := fun s _J φ h A … => Local … s φ h A …`
  (local `separatedAssembly` has `{J}` implicit; the field has it explicit);
* `compactSubsetForceR := fun _ hf => D01.memForceR_of_memForceCompact hf` — the
  set inclusion `forceClassCompact ⊆ forceClassR` (both `{f | …}` in Data) is
  pointwise membership, discharged by the D01 pointwise implication;
* the cutoff `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff` with its four
  properties from `baseCutoff_smooth/_eq_one/_eq_zero/_nonneg/_le_one`
  (`chi_range := fun x => ⟨baseCutoff_nonneg x, baseCutoff_le_one x⟩`).

Vendor `Space` check: `NavierStokesR3.ProblemStatement.Space` (the `Space` the
cutoff lemmas quantify over) is `abbrev Space := NavierStokes.ProblemStatement.Space`
(`vendor/.../R3/ProblemStatement.lean:38`), reducibly defeq to the contract's
`Space`, so `χ := baseCutoff` typechecks with no bridge.

## Failures / corrections

1. **Parse error `expected token` at `ℝ≥0∞`** in the binding's `variable` line —
   the binding referenced `ℝ≥0∞` and `RealVectorSobolev s` without
   `open scoped ENNReal`. The contract had it (copied from `Spec.lean`); the
   binding did not. Fixed by adding `open scoped ENNReal`. This surfaced as a
   cascading `declaration uses 'sorry'` on `def bochnerPartial` (the parse failure
   left the body unelaborated), which cleared once the token error was fixed.

No mathematical dead ends: this lane registers already-merged proofs, so every
field had a known discharging theorem in `Section4/B01/*` or `Section4/D01/ForceClass.lean`.

## Commands and results

```
lake build Contracts.V1.BochnerPartial            → Built (3.2s)
lake build Bindings.BochnerPartial                → Built (2.5s) after ENNReal fix
lake build Tests.BochnerPartial                   → Built; "checked; standard logical axioms only"
make check                                        → plan ok; check_contracts ok; policy 13/13; work queue 30 items
make test                                         → all 14 contracts checked, incl. checkedBochnerPartial
make test-mutations                               → refactor accepted; admitted/extra_axiom/weakened rejected
check_contracts.py --base-ref origin/erenup/integration
                                                  → registered_contracts 14; base_compatibility_checked True
```

No `maxHeartbeats`, `sorry`, `admit`, `axiom` or `native_decide` in the three new
files. Transitive axioms of `checkedBochnerPartial`: `propext`, `Classical.choice`,
`Quot.sound` only.
