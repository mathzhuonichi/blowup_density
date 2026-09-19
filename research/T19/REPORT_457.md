# Lane 457 report — T19 U-CAN canonical records

## 1. What was restated

`NSFormalization.Section3.T19.Density` now contains the canonical
`PeriodicDensityAPI`, `MixedRegionAPI`, `StrongClosureAPI`, and `ProjectionAPI`
records, with 3/3/4/3 fields respectively, plus the four headline
`…Statement : Prop` definitions.  They retain the approved B/B/A/A bases, are
all `Prop`-valued, use the canonical T10/T11 vocabulary and `T15.alphaT`, and
restate T18's output-level conclusions without threading a T18 record.

The `Already proved` section checks the exact U1–U5 record-field types against
the named lane-388 theorems and checks the two U6 zero-representative helper
types.  All seven examples close by the existing theorem names without an
adapter: `thresholdValue`, `mixedRegionArithmetic`, `regionExamples`,
`energyTimeEmbedding`, `referenceFiniteEnergy`,
`torusForceSobolevENorm_zero`, and `torusMixedLebesgueENormT_zero`.

## 2. Files and conformance evidence

- `formalization/NSFormalization/Section3/T19/Density.lean`: canonical local
  trajectory/breakdown/density vocabulary, four records, four statement defs,
  and the lane-388 seam examples.
- `research/T19/probes/api_on_canonical.lean`: synchronized Contracts-vocabulary
  Spec block; `rfl` drift checks; explicit note and use of the non-`rfl`
  `maximalLifespanT_eq` bridge; fieldwise Spec ↔ canonical conversions for all
  four records; round trips; and equivalences for all four statement defs.
- `research/T19/ATTEMPTS_UCAN.md`: vocabulary and 13-field mapping, including
  the no-T18-threading decision.
- `research/T19/axioms_ucan.lean`: audit of every named declaration introduced
  by `Density.lean`.
- `research/T19/T19_SPLIT.md`: U-CAN completion status.
- `research/T19/REPORT_457.md`: this report.

The structure exception is handled only through
`Bindings.TorusLocalTheory.toContract` / `ofContract`.  Consequently regular
and singular trajectories are rebuilt witness by witness, and maximal
lifespans use `Bindings.TorusLocalTheory.maximalLifespanT_eq`; no false `rfl`
bridge is claimed.

## 3. Unrestated fields or residual gap

None.  All thirteen Spec fields and all four statement definitions have a
canonical restatement.  No field was weakened, dropped, guarded by an extra
assumption, replaced by `True`, or made conditional on a threaded T18 record.
The only non-definitional vocabulary seam is the expected
`ClassicalSolutionT` structure/lifespan seam, and the probe closes it
fieldwise in both directions.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Density`:
  exit 0, `Build completed successfully (10043 jobs)`; only pre-existing
  replayed dependency warnings.
- `lake env lean ../formalization/NSFormalization/Section3/T19/Density.lean`:
  exit 0, no output.
- `lake env lean ../research/T19/probes/api_on_canonical.lean`:
  exit 0; all 44 drift, transport, conversion, round-trip, and statement
  declarations printed exactly `[propext, Classical.choice, Quot.sound]`.
- `lake env lean ../research/T19/axioms_ucan.lean`:
  exit 0; all twelve audited declarations printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token scan over the three Lean deliverables: no `sorry`, `admit`,
  `native_decide`, or `axiom`/`opaque` declaration.
- `git diff --check`: exit 0.
- `make check`: exit 0; formalization-plan, contract-policy, contract
  architecture, policy tests, and work-queue checks passed.
